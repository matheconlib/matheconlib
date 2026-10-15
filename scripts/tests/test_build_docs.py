"""Documentation workspace, snapshot, and cache contracts without Lean."""

import importlib.util
import json
from pathlib import Path
import sqlite3
import shutil
import tempfile
import unittest
from unittest.mock import patch


SPEC = importlib.util.spec_from_file_location("build_docs", Path(__file__).resolve().parents[1] / "build_docs.py")
docs = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(docs)


def database(path, names=("Mathlib.Base", "MathEconLib", "MathEconLib.A")):
    path.parent.mkdir(parents=True, exist_ok=True)
    with sqlite3.connect(path) as conn:
        conn.executescript("""
            CREATE TABLE IF NOT EXISTS modules (name TEXT PRIMARY KEY);
            CREATE TABLE IF NOT EXISTS name_info (
                module_name TEXT REFERENCES modules(name) ON DELETE CASCADE, name TEXT);
            CREATE TABLE IF NOT EXISTS schema_meta (key TEXT PRIMARY KEY, value TEXT);
        """)
        for name in names:
            conn.execute("INSERT OR IGNORE INTO modules VALUES (?)", (name,))
            conn.execute("INSERT INTO name_info VALUES (?, ?)", (name, name + ".value"))
        conn.execute("INSERT OR REPLACE INTO schema_meta VALUES ('ddl_hash', 'fixture')")


class DocumentationTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.repo = self.base / "repo"
        self.repo.mkdir()
        (self.repo / "lean-toolchain").write_text("leanprover/lean4:v4.28.0\n")
        self.root_manifest = {"name": "matheconlib", "packages": [
            {"name": "mathlib", "type": "git", "url": "https://example.org/mathlib", "rev": "a" * 40},
        ]}
        (self.repo / "lake-manifest.json").write_text(json.dumps(self.root_manifest))
        (self.repo / "MathEconLib").mkdir()
        (self.repo / "MathEconLib/A.lean").write_text("def value := 1\n")
        self.output = self.base / "output"
        self.cache = self.base / "cache"
        self.workspaces = []
        self.fail_build = False
        self.expect_restored_tool = False

    def fake_lake(self, command, *, cwd, **kwargs):
        cwd = Path(cwd)
        if command[1] == "update":
            self.workspaces.append(cwd)
            config = (cwd / "lakefile.toml").read_text()
            self.assertIn(str(self.repo), config)
            self.assertIn(docs.DOCGEN_REV, config)
            for dependency in self.root_manifest["packages"]:
                self.assertIn(f'rev = "{dependency["rev"]}"', config)
            manifest = dict(self.root_manifest, packages=self.root_manifest["packages"] + [
                {"name": "«doc-gen4»", "type": "git", "url": docs.DOCGEN_URL, "rev": docs.DOCGEN_REV},
            ])
            (cwd / "lake-manifest.json").write_text(json.dumps(manifest))
            package = self.repo / ".lake/packages/doc-gen4"
            package.mkdir(parents=True, exist_ok=True)
            (package / "lean-toolchain").write_text((self.repo / "lean-toolchain").read_text())
        elif command[1] == "build":
            if self.fail_build:
                raise docs.subprocess.CalledProcessError(1, command)
            tool_build = self.repo / ".lake/packages/doc-gen4/.lake/build"
            if self.expect_restored_tool:
                self.assertEqual((tool_build / "compiled-tool").read_text(), "cached tool")
            tool_build.mkdir(parents=True, exist_ok=True)
            (tool_build / "compiled-tool").write_text("cached tool")
            build = cwd / ".lake/build"
            database(build / "api-docs.db")
            data = build / "doc-data"
            data.mkdir(exist_ok=True)
            for name in ["Mathlib.Base.doc", "MathEconLib.A.doc", "MathEconLib.A.doc.trace", "MathEconLib--library.docs_built"]:
                (data / name).write_text("marker")
            html = build / "doc"
            html.mkdir(exist_ok=True)
            # Simulate Lake skipping bibPrepass when its cached JSON survives.
            if not (data / "references.json").exists():
                (data / "references.json").write_text("{}")
                (html / "references.bib").write_text("")
            if not (html / "references.bib").exists():
                raise ValueError("cached bibliography prepass omitted references.bib")
            (html / "index.html").write_text("<html>fixture</html>")
            (build / "doc-manifest.json").write_text("[]")
        else:
            self.fail(f"Unexpected command: {command}")

    def build(self):
        with patch.object(docs.shutil, "which", return_value="lake"), \
             patch.object(docs.subprocess, "run", side_effect=self.fake_lake), \
             patch.object(docs.subprocess, "check_output", return_value="b" * 40 + "\n"):
            docs.build_docs(self.output, self.cache, self.repo)

    def test_export_cleanup_and_dependency_only_cache(self):
        self.build()
        self.assertTrue(all(not p.exists() for p in self.workspaces))
        self.assertFalse((self.repo / "docbuild").exists())
        info = docs.validate_database(self.output / "api-docs.db")
        self.assertEqual(info["modules"], ["MathEconLib", "MathEconLib.A"])
        metadata = json.loads((self.output / "metadata.json").read_text())
        self.assertEqual(metadata["database_sha256"], docs.sha256(self.output / "api-docs.db"))
        self.assertEqual(metadata["archive_sha256"], docs.sha256(self.output / "api-docs.db.gz"))
        with docs.gzip.open(self.output / "api-docs.db.gz", "rb") as src:
            self.assertEqual(src.read(), (self.output / "api-docs.db").read_bytes())
        with sqlite3.connect(self.cache / "build/api-docs.db") as conn:
            self.assertEqual(conn.execute("SELECT name FROM modules").fetchall(), [("Mathlib.Base",)])
            self.assertEqual(conn.execute("SELECT module_name FROM name_info").fetchall(), [("Mathlib.Base",)])
        self.assertEqual([p.name for p in (self.cache / "build/doc-data").iterdir()], ["Mathlib.Base.doc"])
        self.assertFalse((self.cache / "build/doc").exists())
        self.assertFalse((self.cache / "build/doc-data/references.json").exists())
        self.assertEqual((self.cache / "tool-builds/doc-gen4/compiled-tool").read_text(), "cached tool")
        shutil.rmtree(self.repo / ".lake/packages/doc-gen4")
        self.expect_restored_tool = True
        self.build()
        self.assertTrue(all(not p.exists() for p in self.workspaces))

    def test_failure_removes_workspace_and_does_not_publish(self):
        self.fail_build = True
        with self.assertRaises(docs.subprocess.CalledProcessError):
            self.build()
        self.assertTrue(all(not p.exists() for p in self.workspaces))
        self.assertFalse(self.output.exists())
        self.assertFalse(self.cache.exists())

    def test_dependency_mismatch_is_rejected(self):
        actual = dict(self.root_manifest, packages=[dict(self.root_manifest["packages"][0], rev="wrong")])
        with self.assertRaisesRegex(ValueError, "differs from the root manifest"):
            docs.verify_dependencies(self.root_manifest, actual)

    def test_source_link_mode_changes_cache_fingerprint(self):
        with patch.dict(docs.os.environ, DOCGEN_SRC="file"):
            file_state = docs.fingerprint(self.repo, self.root_manifest)
        with patch.dict(docs.os.environ, DOCGEN_SRC="github"):
            github_state = docs.fingerprint(self.repo, self.root_manifest)
        self.assertNotEqual(file_state, github_state)

    def test_snapshot_includes_live_wal(self):
        source = self.base / "wal.db"
        conn = sqlite3.connect(source)
        self.addCleanup(conn.close)
        conn.execute("PRAGMA journal_mode = WAL")
        conn.execute("CREATE TABLE values_table (n INTEGER)")
        conn.execute("INSERT INTO values_table VALUES (42)")
        conn.commit()
        target = self.base / "snapshot.db"
        docs.snapshot(source, target)
        with sqlite3.connect(target.as_uri() + "?immutable=1", uri=True) as copied:
            self.assertEqual(copied.execute("SELECT n FROM values_table").fetchone(), (42,))
        self.assertFalse(target.with_name(target.name + "-wal").exists())

    def test_checkpointed_wal_database_needs_no_sidecars(self):
        source = self.base / "checkpointed.db"
        conn = sqlite3.connect(source)
        conn.execute("PRAGMA journal_mode = WAL")
        conn.execute("CREATE TABLE values_table (n INTEGER)")
        conn.execute("INSERT INTO values_table VALUES (42)")
        conn.commit()
        conn.execute("PRAGMA wal_checkpoint(TRUNCATE)").fetchall()
        conn.close()
        downloaded = self.base / "downloaded.db"
        shutil.copyfile(source, downloaded)
        self.assertFalse(downloaded.with_name(downloaded.name + "-wal").exists())
        copied = docs.open_readonly(downloaded)
        self.addCleanup(copied.close)
        self.assertEqual(copied.execute("SELECT n FROM values_table").fetchone(), (42,))

    def test_cache_fingerprint_and_corruption_rebuild(self):
        self.build()
        destination = self.base / "restored"
        state = json.loads((self.cache / "fingerprint.json").read_text())
        docs.restore_cache(self.cache, destination, dict(state, docgen_rev="changed"))
        self.assertFalse(destination.exists())
        (self.cache / "build/api-docs.db").write_bytes(b"not sqlite")
        docs.restore_cache(self.cache, destination, state)
        self.assertFalse(destination.exists())

    def test_missing_database_or_missing_module_invalidates_markers(self):
        self.build()
        destination = self.base / "restored"
        state = json.loads((self.cache / "fingerprint.json").read_text())
        cached_db = self.cache / "build/api-docs.db"
        cached_db.unlink()
        self.assertFalse(docs.restore_cache(self.cache, destination, state))
        self.assertFalse(destination.exists())
        database(cached_db, names=("Mathlib.Unrelated",))
        self.assertFalse(docs.restore_cache(self.cache, destination, state))
        self.assertFalse(destination.exists())

    def test_overlapping_output_and_cache_are_rejected(self):
        with self.assertRaisesRegex(ValueError, "overlap"):
            docs.build_docs(self.output, self.output / "cache", self.repo)

    def test_output_or_cache_cannot_replace_checkout(self):
        for output, cache in [(self.repo, None), (self.output, self.repo)]:
            with self.subTest(output=output, cache=cache), self.assertRaisesRegex(ValueError, "checkout"):
                docs.build_docs(output, cache, self.repo)


if __name__ == "__main__":
    unittest.main()
