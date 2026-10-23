"""Build and audit every project Lean source; retain a JSON report on success or failure."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile


REPO = Path(__file__).resolve().parents[1]
BACKEND = Path(__file__).with_name("CheckProofIntegrity.lean")
EXCLUDED_DIRS = {".git", ".lake", "node_modules", ".venv"}
FORBIDDEN_TOKENS = {"sorry", "admit", "native_decide"}
RAW_STRING = re.compile(r'r(#+)?"')
CHARACTER = re.compile(r"'(?:\\u[0-9a-fA-F]{4}|\\.|[^'\\])'")


def proof_holes(source):
    """Find explicit holes, including anonymous examples discarded from .olean files.

    Skip nested comments, quoted identifiers, character literals and string text.
    Expressions inside interpolated strings are still code. Compiled axiom checking
    remains the authority for named declarations, including macro-generated holes.
    """
    found = []
    length = len(source)

    def string(i, interpolated):
        while i < length:
            if source[i] == "\\":
                i += 2
            elif source[i] == '"':
                return i + 1
            elif interpolated and source[i] == "{":
                if source.startswith("{{", i):
                    i += 2
                else:
                    i = code(i + 1, braces=1)
            else:
                i += 1
        return i

    def code(i, braces=0):
        while i < length:
            if source.startswith("--", i):
                end = source.find("\n", i)
                i = length if end < 0 else end + 1
            elif source.startswith("/-", i):
                depth = 1
                i += 2
                while i < length and depth:
                    if source.startswith("/-", i):
                        depth += 1
                        i += 2
                    elif source.startswith("-/", i):
                        depth -= 1
                        i += 2
                    else:
                        i += 1
            elif source[i] == "«":
                end = source.find("»", i + 1)
                i = length if end < 0 else end + 1
            elif raw := RAW_STRING.match(source, i):
                closing = '"' + (raw[1] or "")
                end = source.find(closing, i + len(raw[0]))
                i = length if end < 0 else end + len(closing)
            elif source[i] == '"':
                i = string(i + 1, i > 0 and source[i - 1] == "!")
            elif source[i] == "'" and (char := CHARACTER.match(source, i)):
                i += len(char[0])
            elif source[i].isalpha() or source[i] == "_":
                end = i + 1
                while end < length and (source[end].isalnum() or source[end] in "_'?!"):
                    end += 1
                token = source[i:end]
                if token in FORBIDDEN_TOKENS:
                    found.append({"token": token, "line": source.count("\n", 0, i) + 1})
                i = end
            elif braces and source[i] == "{":
                braces += 1
                i += 1
            elif braces and source[i] == "}":
                braces -= 1
                i += 1
                if not braces:
                    return i
            else:
                i += 1
        return i

    code(0)
    return found


def discover_sources(root):
    """Include orphan sources as well as umbrella imports; exclude dependencies and this tool."""
    sources = []
    for directory, dirs, files in os.walk(root):
        dirs[:] = sorted(d for d in dirs if d not in EXCLUDED_DIRS)
        for name in sorted(files):
            path = Path(directory) / name
            if path.suffix != ".lean" or path.resolve() == BACKEND.resolve():
                continue
            if path.is_symlink():
                raise ValueError("Cannot audit a symlinked Lean source: " + str(path))
            sources.append(path.relative_to(root))
    if not sources:
        raise ValueError("No project Lean sources found")
    return sorted(sources)


def module_name(path):
    return ".".join(path.with_suffix("").parts)


def write_report(path, report):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")


def run(root, report_path):
    report = {"status": "error", "stage": "discovery"}
    write_report(report_path, report)
    try:
        sources = discover_sources(root)
        modules = [module_name(path) for path in sources]
        report.update({
            "sources": [path.as_posix() for path in sources],
            "source_sha256": {
                path.as_posix(): hashlib.sha256((root / path).read_bytes()).hexdigest()
                for path in sources
            },
            "lean_toolchain": (root / "lean-toolchain").read_text().strip(),
            "stage": "source",
        })
        revision = subprocess.run(
            ["git", "rev-parse", "HEAD"], cwd=root, capture_output=True, text=True
        )
        if revision.returncode == 0:
            report["git_revision"] = revision.stdout.strip()
        report["source_violations"] = [
            {"source": path.as_posix(), **hole}
            for path in sources for hole in proof_holes((root / path).read_text())
        ]
        if report["source_violations"]:
            report["status"] = "failed"
            for violation in report["source_violations"]:
                print("{source}:{line}: forbidden proof token {token}".format(**violation),
                      file=sys.stderr)
            return 1
        report["stage"] = "build"
        write_report(report_path, report)
        # Explicit module targets also build files not reachable from an umbrella.
        built = subprocess.run(["lake", "--rehash", "--no-ansi", "build", *modules], cwd=root)
        if built.returncode:
            report["error"] = "Building all project modules failed"
            return 1
        report["stage"] = "audit"
        write_report(report_path, report)
        with tempfile.TemporaryDirectory(prefix="proof-integrity-") as work:
            backend_report = Path(work) / "report.json"
            checked = subprocess.run(
                ["lake", "env", "lean", "--run", str(BACKEND), str(backend_report), *modules],
                cwd=root,
            )
            if not backend_report.exists():
                raise ValueError("Lean checker did not write an audit report")
            result = json.loads(backend_report.read_text())
            if result.get("modules") != modules:
                raise ValueError("Lean checker did not audit the requested modules")
            expected = 0 if result.get("status") == "passed" else 1
            if checked.returncode != expected or result.get("status") not in {"passed", "failed"}:
                raise ValueError("Lean checker returned an inconsistent result")
            report.update(result)
            report["stage"] = "complete"
            return expected
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        report["status"] = "error"
        report["error"] = str(error)
        print("Proof integrity check failed: " + str(error), file=sys.stderr)
        return 1
    finally:
        write_report(report_path, report)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO)
    parser.add_argument("--report", type=Path, default=REPO / ".lake/proof-integrity/report.json")
    args = parser.parse_args()
    return run(args.root.resolve(), args.report.resolve())


if __name__ == "__main__":
    sys.exit(main())
