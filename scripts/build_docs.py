#!/usr/bin/env python3
"""Build API documentation in a disposable Lake project (Python 3.9+)."""

from __future__ import annotations

import argparse
from contextlib import closing
import gzip
import hashlib
import json
import os
from pathlib import Path
import shutil
import sqlite3
import subprocess
import sys
import tempfile


REPO_ROOT = Path(__file__).resolve().parent.parent
LIBRARY = "MathEconLib"
DOCGEN_URL = "https://github.com/danlyng/doc-gen4"
DOCGEN_REV = "5dfeb1052b845c95c92516e05b7dea38cba9ee21"
CACHE_VERSION = 1
DOC_TOOLS = ("doc-gen4", "leansqlite", "MD4Lean", "BibtexQuery", "UnicodeBasic")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def package_name(package: dict) -> str:
    return package["name"].strip("«»")


def open_readonly(path: Path) -> sqlite3.Connection:
    # These databases are read after their producers finish. A live WAL must
    # still be read normally; checkpointed snapshots need no journal sidecars.
    # Apple's SQLite cannot open a WAL-mode database read-only without sidecars.
    uri = path.resolve().as_uri() + "?mode=ro"
    wal = path.with_name(path.name + "-wal")
    if not wal.exists() or wal.stat().st_size == 0:
        uri += "&immutable=1"
    return sqlite3.connect(uri, uri=True)


def verify_dependencies(root: dict, docs: dict) -> None:
    packages = {package_name(p): p for p in docs["packages"]}
    for expected in root["packages"]:
        name = package_name(expected)
        actual = packages.get(name)
        if actual is None or actual.get("rev") != expected.get("rev"):
            raise ValueError(f"Documentation dependency {name} differs from the root manifest")
    docgen = packages.get("doc-gen4", {})
    if docgen.get("rev") != DOCGEN_REV or docgen.get("url", "").removesuffix(".git") != DOCGEN_URL:
        raise ValueError("Documentation manifest does not contain the pinned doc-gen4 backport")


def fingerprint(repo: Path, manifest: dict) -> dict:
    return {
        "version": CACHE_VERSION,
        "toolchain": (repo / "lean-toolchain").read_text().strip(),
        "root_manifest_sha256": sha256(repo / "lake-manifest.json"),
        "docgen_rev": DOCGEN_REV,
        "source_links": os.environ.get("DOCGEN_SRC") or "github",
        "dependencies": sorted(
            (package_name(p), p.get("url"), p["rev"])
            for p in manifest["packages"] if p["type"] == "git"
        ),
    }


def snapshot(source: Path, target: Path) -> None:
    """Copy committed SQLite state without depending on a WAL sidecar."""
    target.parent.mkdir(parents=True, exist_ok=True)
    with closing(open_readonly(source)) as src:
        with closing(sqlite3.connect(target)) as dst:
            src.backup(dst)
            dst.execute("PRAGMA journal_mode = DELETE")


def validate_database(path: Path) -> dict:
    if not path.is_file():
        raise ValueError(f"Documentation database not found: {path}")
    with closing(open_readonly(path)) as conn:
        if conn.execute("PRAGMA quick_check").fetchall() != [("ok",)]:
            raise ValueError("Documentation database failed SQLite integrity checks")
        if conn.execute("PRAGMA foreign_key_check").fetchone() is not None:
            raise ValueError("Documentation database has invalid foreign keys")
        modules = [row[0] for row in conn.execute(
            "SELECT name FROM modules WHERE name = ? OR name LIKE ? ORDER BY name",
            (LIBRARY, LIBRARY + ".%"),
        )]
        if not modules:
            raise ValueError(f"Documentation database has no {LIBRARY} modules")
        return {
            "schema": dict(conn.execute("SELECT key, value FROM schema_meta")),
            "modules": modules,
        }


def remove_project_data(build_dir: Path) -> None:
    """Retain only dependency analysis; always reanalyze checkout modules."""
    db = build_dir / "api-docs.db"
    if db.exists():
        with closing(sqlite3.connect(db)) as conn, conn:
            conn.execute("PRAGMA foreign_keys = ON")
            conn.execute("DELETE FROM modules WHERE name = ? OR name LIKE ?",
                         (LIBRARY, LIBRARY + ".%"))
    data_dir = build_dir / "doc-data"
    if data_dir.exists():
        for path in data_dir.iterdir():
            # The bibliography prepass also creates doc/references.bib. Its
            # cached JSON would skip the prepass after HTML has been removed.
            if path.name.startswith((LIBRARY + ".", LIBRARY + "--", "references.json")):
                if path.is_file():
                    path.unlink()
    shutil.rmtree(build_dir / "doc", ignore_errors=True)
    for path in build_dir.glob("*manifest.json"):
        path.unlink()


def restore_cache(cache: Path, build_dir: Path, expected: dict) -> bool:
    try:
        if json.loads((cache / "fingerprint.json").read_text()) != json.loads(json.dumps(expected)):
            print("Documentation cache fingerprint changed; rebuilding dependencies.", flush=True)
            return False
        shutil.copytree(cache / "build", build_dir, dirs_exist_ok=True)
        if not (build_dir / "api-docs.db").is_file():
            raise ValueError("cached database is missing")
        remove_project_data(build_dir)
        with closing(open_readonly(build_dir / "api-docs.db")) as conn:
            if conn.execute("PRAGMA quick_check").fetchall() != [("ok",)]:
                raise ValueError("invalid database")
            if conn.execute("PRAGMA foreign_key_check").fetchone() is not None:
                raise ValueError("invalid cached foreign keys")
            modules = {row[0] for row in conn.execute("SELECT name FROM modules")}
            if not modules:
                raise ValueError("cached database has no dependency modules")
            for marker in (build_dir / "doc-data").glob("*.doc"):
                name = marker.stem
                if name.startswith("core-"):
                    prefix = name.removeprefix("core-")
                    present = any(m == prefix or m.startswith(prefix + ".") for m in modules)
                else:
                    present = name in modules
                if not present:
                    raise ValueError(f"cached analysis marker has no database data: {name}")
        print("Restored dependency documentation cache.", flush=True)
        return True
    except (OSError, ValueError, sqlite3.Error) as error:
        shutil.rmtree(build_dir, ignore_errors=True)
        print(f"Dependency documentation cache unavailable ({error}); rebuilding.", flush=True)
        return False


def save_cache(build_dir: Path, cache: Path, state: dict, repo: Path) -> None:
    cache.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="doc-cache-", dir=cache.parent) as tmp:
        staged = Path(tmp)
        saved_build = staged / "build"
        saved_build.mkdir()
        snapshot(build_dir / "api-docs.db", saved_build / "api-docs.db")
        shutil.copytree(build_dir / "doc-data", saved_build / "doc-data")
        remove_project_data(saved_build)
        # All HTML completion markers are excluded, even if other facets ran.
        for path in (saved_build / "doc-data").glob("*.docs*"):
            path.unlink()
        for name in DOC_TOOLS:
            tool_build = repo / ".lake/packages" / name / ".lake/build"
            if tool_build.is_dir():
                shutil.copytree(tool_build, staged / "tool-builds" / name)
        (staged / "fingerprint.json").write_text(json.dumps(state, sort_keys=True) + "\n")
        if cache.exists():
            shutil.rmtree(cache)
        shutil.copytree(staged, cache)


def build_docs(output: Path, cache: Path | None = None, repo: Path = REPO_ROOT) -> None:
    output = output.resolve()
    cache = cache.resolve() if cache else None
    repo = repo.resolve()
    for target in (output, cache):
        if target is not None and (target == repo or target in repo.parents):
            raise ValueError("Output and cache directories must not replace the checkout or its ancestors")
    if cache and (output == cache or output in cache.parents or cache in output.parents):
        raise ValueError("Output and cache directories must not overlap")
    lake = shutil.which("lake")
    if not lake:
        raise ValueError("lake was not found on PATH; install Lean before building documentation")
    root_manifest = json.loads((repo / "lake-manifest.json").read_text())
    env = dict(os.environ, MATHLIB_NO_CACHE_ON_UPDATE="1")
    if (env.get("DOCGEN_SRC") or "github") not in ("github", "file", "vscode"):
        raise ValueError("DOCGEN_SRC must be github, file, or vscode")
    print("Building API documentation in a temporary Lake workspace...", flush=True)
    with tempfile.TemporaryDirectory(prefix="matheconlib-docbuild-") as tmp:
        workspace = Path(tmp)
        config = (
            'name = "docbuild"\nreservoir = false\nversion = "0.1.0"\n'
            f'packagesDir = {json.dumps(str(repo / ".lake" / "packages"))}\n\n'
            f'[[require]]\nname = {json.dumps(root_manifest["name"])}\n'
            f'path = {json.dumps(str(repo))}\n\n'
            f'[[require]]\nname = "doc-gen4"\ngit = {json.dumps(DOCGEN_URL)}\n'
            f'rev = {json.dumps(DOCGEN_REV)}\n'
        )
        # Lake can otherwise select a dependency's older transitive pin (notably
        # leansqlite's plausible). Direct requirements preserve the root graph.
        for package in root_manifest["packages"]:
            if package["type"] != "git":
                raise ValueError("Documentation setup requires Git-pinned root dependencies")
            config += (
                f'\n[[require]]\nname = {json.dumps(package_name(package))}\n'
                f'git = {json.dumps(package["url"])}\nrev = {json.dumps(package["rev"])}\n'
            )
        (workspace / "lakefile.toml").write_text(config)
        shutil.copyfile(repo / "lean-toolchain", workspace / "lean-toolchain")
        subprocess.run([lake, "update", root_manifest["name"], "doc-gen4"],
                       cwd=workspace, env=env, check=True)
        docs_manifest = json.loads((workspace / "lake-manifest.json").read_text())
        verify_dependencies(root_manifest, docs_manifest)
        docgen_toolchain = repo / ".lake/packages/doc-gen4/lean-toolchain"
        if docgen_toolchain.read_text().strip() != (repo / "lean-toolchain").read_text().strip():
            raise ValueError("The doc-gen4 backport does not match the project toolchain")
        state = fingerprint(repo, docs_manifest)
        build_dir = workspace / ".lake/build"
        if cache and restore_cache(cache, build_dir, state):
            # Clone sources first: restoring build-only package directories before
            # `lake update` would leave non-Git directories at Lake's clone paths.
            for name in DOC_TOOLS:
                saved_tool = cache / "tool-builds" / name
                if saved_tool.is_dir():
                    shutil.copytree(saved_tool, repo / ".lake/packages" / name / ".lake/build", dirs_exist_ok=True)
        subprocess.run([lake, "build", LIBRARY + ":docs"], cwd=workspace, env=env, check=True)
        database_info = validate_database(build_dir / "api-docs.db")
        expected_modules = {LIBRARY} | {
            ".".join(path.relative_to(repo).with_suffix("").parts)
            for path in (repo / LIBRARY).rglob("*.lean")
        }
        if set(database_info["modules"]) != expected_modules:
            raise ValueError("Documented modules differ from the source tree; regenerate import lists")
        if not (build_dir / "doc/index.html").is_file():
            raise ValueError("Documentation build did not produce doc/index.html")
        output.mkdir(parents=True, exist_ok=True)
        snapshot(build_dir / "api-docs.db", output / "api-docs.db")
        with (output / "api-docs.db").open("rb") as src:
            with (output / "api-docs.db.gz").open("wb") as dest:
                with gzip.GzipFile(filename="", fileobj=dest, mode="wb", mtime=0) as archive:
                    shutil.copyfileobj(src, archive)
        shutil.rmtree(output / "doc", ignore_errors=True)
        shutil.copytree(build_dir / "doc", output / "doc")
        shutil.copyfile(workspace / "lake-manifest.json", output / "lake-manifest.json")
        revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()
        dirty = bool(subprocess.check_output(
            ["git", "status", "--porcelain", "--untracked-files=no"], cwd=repo, text=True
        ).strip())
        metadata = dict(database_info, revision=revision, toolchain=state["toolchain"],
                        checkout_dirty=dirty,
                        source_links=state["source_links"],
                        docgen_revision=DOCGEN_REV,
                        root_manifest_sha256=state["root_manifest_sha256"],
                        documentation_manifest_sha256=sha256(output / "lake-manifest.json"),
                        database_sha256=sha256(output / "api-docs.db"),
                        archive_sha256=sha256(output / "api-docs.db.gz"))
        (output / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
        if cache:
            save_cache(build_dir, cache, state, repo)
    print(f"Exported API documentation and standalone database to {output}", flush=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", required=True, type=Path, help="Directory for HTML, database, and provenance")
    parser.add_argument("--cache-dir", type=Path, help="Optional dependency documentation cache directory")
    args = parser.parse_args()
    try:
        build_docs(args.output_dir, args.cache_dir)
    except (OSError, ValueError, sqlite3.Error, subprocess.CalledProcessError) as error:
        print(f"Error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
