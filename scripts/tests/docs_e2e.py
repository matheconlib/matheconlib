#!/usr/bin/env python3
"""Compare signatures from a real Lean documentation build with reviewed Markdown."""

from __future__ import annotations

import argparse
from contextlib import ExitStack
import difflib
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time


REPO_ROOT = Path(__file__).resolve().parents[2]
FIXTURE = Path(__file__).resolve().parent / "fixtures/docs-e2e"
EXPECTED = FIXTURE / "expected"


def compare(actual: Path) -> bool:
    expected_files = {p.relative_to(EXPECTED) for p in EXPECTED.rglob("*") if p.is_file()}
    actual_files = {p.relative_to(actual) for p in actual.rglob("*") if p.is_file()}
    matches = True
    for name in sorted(expected_files | actual_files):
        expected_bytes = (EXPECTED / name).read_bytes() if name in expected_files else b""
        actual_bytes = (actual / name).read_bytes() if name in actual_files else b""
        if name in expected_files and name in actual_files and expected_bytes == actual_bytes:
            continue
        matches = False
        if name not in expected_files:
            print(f"Unexpected file: {name}", file=sys.stderr)
        elif name not in actual_files:
            print(f"Missing file: {name}", file=sys.stderr)
        diff = difflib.unified_diff(
            expected_bytes.decode("utf-8").splitlines(keepends=True),
            actual_bytes.decode("utf-8").splitlines(keepends=True),
            fromfile=f"expected/{name}", tofile=f"actual/{name}",
        )
        sys.stderr.writelines(diff)
    return matches


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--update", action="store_true", help="Replace the reviewed golden files with current output")
    parser.add_argument("--cache-dir", type=Path, help="Reuse a dependency documentation cache directory")
    args = parser.parse_args()
    start = time.perf_counter()
    try:
        with ExitStack() as stack:
            output = Path(stack.enter_context(tempfile.TemporaryDirectory(prefix="docs-e2e-")))
            cache = args.cache_dir
            if cache is None:
                cache = Path(stack.enter_context(tempfile.TemporaryDirectory(prefix="docs-e2e-cache-")))
            subprocess.run([
                sys.executable, str(REPO_ROOT / "scripts/build_docs.py"),
                "--project", str(FIXTURE), "--library", "DocsFixture",
                "--output-dir", str(output), "--cache-dir", str(cache),
            ], check=True)
            built = time.perf_counter()
            signatures = output / "signatures"
            subprocess.run([
                sys.executable, str(REPO_ROOT / "scripts/extract_signatures.py"),
                "--no-build", "--db", str(output / "api-docs.db"),
                "--root", "DocsFixture", "--output", str(signatures),
            ], check=True)
            extracted = time.perf_counter()
            if args.update:
                shutil.rmtree(EXPECTED, ignore_errors=True)
                shutil.copytree(signatures, EXPECTED)
                print("Updated fixture golden files.", flush=True)
            elif not compare(signatures):
                return 1
            else:
                print("Fixture signatures match the golden files.", flush=True)
        print(f"Wall time: {time.perf_counter() - start:.2f}s "
              f"(documentation build: {built - start:.2f}s; extraction: {extracted - built:.2f}s)", flush=True)
    except (OSError, subprocess.CalledProcessError) as error:
        print(f"Error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
