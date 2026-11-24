"""Build and audit every project Lean source; retain a JSON report on success or failure."""

import argparse
from concurrent.futures import ThreadPoolExecutor
from contextlib import closing
from functools import cache, partial
import hashlib
import json
import os
from pathlib import Path
import platform
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
    This is only an early diagnostic. Lean's elaboration audit checks anonymous
    examples too, without depending on which string interpolation forms this scan knows.
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


def build_project(root, targets):
    return subprocess.run(["lake", "--rehash", "--no-ansi", "build", *targets],
                          cwd=root).returncode


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


def source_cache_keys(root, source_hashes, workers):
    # Lean parses the real import header, including private and meta imports.
    # Outside the project, the pinned toolchain and manifest identify the inputs.
    output = subprocess.check_output(["lake", "env"], cwd=root, text=True)
    lake_env = dict(line.split("=", 1) for line in output.splitlines())
    env = os.environ | lake_env
    context = digest([
        platform.system(), platform.machine(), platform.libc_ver(), platform.mac_ver()[0],
        env.get("ImageOS"), lake_env["LEAN_GITHASH"],
        [hashlib.sha256(path.read_bytes()).hexdigest() for path in (
            Path(__file__), BACKEND, root / "lean-toolchain", root / "lakefile.toml",
            root / "lake-manifest.json",
        )],
    ])
    project_paths = {str(root / source): source for source in source_hashes}

    def project_imports(source):
        output = subprocess.check_output(
            [lake_env["LEAN"], "--src-deps", source], cwd=root, env=env, text=True,
        )
        return sorted({
            project_paths[absolute] for path in output.splitlines()
            if (absolute := os.path.abspath(root / path)) in project_paths
        })

    imports = dict(zip(source_hashes, workers.map(project_imports, source_hashes)))

    @cache
    def key(source):
        return digest([context, source, source_hashes[source], [key(dep) for dep in imports[source]]])

    return {source: key(source) for source in source_hashes}


def load_source_cache(path):
    try:
        data = json.loads(path.read_text())
    except (OSError, ValueError):
        return {}
    return data if isinstance(data, dict) else {}


def save_source_cache(path, results):
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=path.parent) as work:
        staged = Path(work) / "cache.json"
        write_report(staged, results)
        staged.replace(path)


def audit_source(root, work, index, path, module):
    source_report = work / f"source-{index}.json"
    checked = subprocess.run(
        ["lake", "env", "lean", "--run", str(BACKEND), "--source",
         str(source_report), path.as_posix(), module], cwd=root,
    )
    if not source_report.exists():
        raise ValueError("Lean did not write a source audit report: " + str(path))
    result = json.loads(source_report.read_text())
    if (not isinstance(result, dict) or result.get("source") != path.as_posix()
            or result.get("module") != module):
        raise ValueError("Lean audited a different source: " + str(path))
    status = result.get("status")
    expected = 0 if status == "passed" else 1
    if checked.returncode != expected or status not in {"passed", "failed"}:
        raise ValueError("Lean source audit returned an inconsistent result: " + str(path))
    count = result.get("declarations_checked")
    violations = result.get("violations")
    if (type(count) is not int or count < 0 or not isinstance(violations, list)
            or bool(violations) != (status == "failed")):
        raise ValueError("Lean source audit returned an invalid report: " + str(path))
    return result


def run(root, report_path, jobs=1, source_cache=None, *, audit_only=False):
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
        if not audit_only:
            report["stage"] = "build"
            write_report(report_path, report)
            # Explicit module targets also build files not reachable from an umbrella.
            if build_project(root, modules):
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
            if expected:
                report["stage"] = "complete"
                return expected
            report["stage"] = "elaboration"
            report["status"] = "error"
            report["elaboration_sources"] = []
            report["elaboration_declarations_checked"] = 0
            report["elaboration_violations"] = []
            write_report(report_path, report)
            failed = False
            audit = partial(audit_source, root, Path(work))
            with ThreadPoolExecutor(max_workers=jobs) as workers:
                cached = load_source_cache(source_cache) if source_cache else {}
                keys = source_cache_keys(root, report["source_sha256"], workers) if source_cache else {}
                next_cache = {}
                hits = 0

                def check(index, path, module):
                    count = cached.get(keys.get(path.as_posix()))
                    if type(count) is int and count >= 0:
                        return {
                            "declarations_checked": count, "violations": [], "status": "passed",
                        }, True
                    return audit(index, path, module), False

                # Consume results in source order and cancel queued work if aggregation fails.
                with closing(workers.map(check, range(len(sources)), sources, modules)) as results:
                    for path, (result, hit) in zip(sources, results):
                        report["elaboration_sources"].append(path.as_posix())
                        report["elaboration_declarations_checked"] += result["declarations_checked"]
                        report["elaboration_violations"].extend(result["violations"])
                        failed = failed or result["status"] == "failed"
                        hits += hit
                        if source_cache and result["status"] == "passed":
                            next_cache[keys[path.as_posix()]] = result["declarations_checked"]
                        write_report(report_path, report)
            if source_cache:
                print(f"Source audit cache: {hits} hits, {len(sources) - hits} misses.", flush=True)
                if not failed:
                    save_source_cache(source_cache, next_cache)
            report["status"] = "failed" if failed else "passed"
            report["stage"] = "complete"
            print("Source elaboration audit: {} declarations in {} sources; {} violations.".format(
                report["elaboration_declarations_checked"], len(report["elaboration_sources"]),
                len(report["elaboration_violations"])))
            return 0 if report["status"] == "passed" else 1
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
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--build-only", action="store_true",
                      help="build Lake's default targets and every project source in one invocation")
    mode.add_argument("--audit-only", action="store_true",
                      help="audit artifacts from a successful --build-only for the same sources")
    parser.add_argument("--report", type=Path, default=REPO / ".lake/proof-integrity/report.json")
    parser.add_argument("--jobs", type=int, default=1, help="number of concurrent source audits")
    parser.add_argument("--source-cache", type=Path,
                        help="experimental cache of successful source audits from trusted runs")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be at least 1")
    root = args.root.resolve()
    if args.build_only:
        try:
            # @ expands to the root package's default targets. + selects a module
            # even when a library or executable shares its name.
            targets = ["@", *(f"+{module_name(path)}" for path in discover_sources(root))]
            return build_project(root, targets)
        except (OSError, ValueError, subprocess.SubprocessError) as error:
            print("Project build failed: " + str(error), file=sys.stderr)
            return 1
    return run(root, args.report.resolve(), args.jobs, args.source_cache,
               audit_only=args.audit_only)


if __name__ == "__main__":
    sys.exit(main())
