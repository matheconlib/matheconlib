"""Signature rendering against small doc-gen4 databases."""

import importlib.util
import json
from pathlib import Path
import sqlite3
import subprocess
import sys
import tempfile
import unittest


SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))
SPEC = importlib.util.spec_from_file_location("extract_signatures", SCRIPTS / "extract_signatures.py")
signatures = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(signatures)


def nat(value):
    out = bytearray()
    while value >= 128:
        out.append((value & 127) | 128)
        value >>= 7
    return bytes(out) + bytes([value])


def string(value):
    encoded = value.encode("utf-8")
    return nat(len(encoded)) + encoded


def text(value):
    return b"\x00" + string(value)


class ExtractionTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.db = self.root / "api docs #1.db"
        self.output = self.root / "signatures"
        with sqlite3.connect(self.db) as conn:
            conn.executescript("""
                CREATE TABLE modules (name TEXT PRIMARY KEY);
                CREATE TABLE name_info (module_name, position, kind, name, type, sorried, render);
                CREATE TABLE declaration_markdown_docstrings (module_name, position, text);
                CREATE TABLE declaration_args (module_name, position, sequence, binder);
                CREATE TABLE structures (module_name, position);
                CREATE TABLE structure_parents (module_name, position, sequence, projection_fn, type);
                CREATE TABLE structure_fields (module_name, position, sequence, proj_name, type, is_direct);
                CREATE TABLE structure_field_args (module_name, position, field_sequence, arg_sequence, binder);
                CREATE TABLE definition_equations (module_name, position, sequence, code);
            """)
            for module in ["MathEconLib", "MathEconLib.Parent", "MathEconLib.Parent.A",
                           "MathEconLib.Parent.B", "MathEconLib.With_under", "MathEconLib.WithXunder",
                           "Mathlib.Other", "MathEconLibTest.Other", "MathEconLibExtra"]:
                conn.execute("INSERT INTO modules VALUES (?)", (module,))
            decls = [
                ("MathEconLib", 0, "theorem", "MathEconLib.root", "True", 0, 1),
                ("MathEconLib.Parent", 0, "theorem", "Nat.local_result", "True", 0, 1),
                ("MathEconLib.Parent.A", 0, "definition", "MathEconLib.identity", "ℕ", 0, 1),
                ("MathEconLib.Parent.A", 1, "theorem", "MathEconLib.private_helper", "True", 0, 0),
                ("MathEconLib.Parent.B", 0, "structure", "MathEconLib.Bundle", "Type", 0, 1),
                ("MathEconLib.Parent.B", 1, "theorem", "MathEconLib.unfinished", "True", 1, 1),
                ("MathEconLib.With_under", 0, "definition", "MathEconLib.underscore", "ℕ", 0, 1),
                ("MathEconLib.WithXunder", 0, "definition", "MathEconLib.other", "ℕ", 0, 1),
                ("Mathlib.Other", 0, "theorem", "Mathlib.external", "True", 0, 1),
                ("MathEconLibTest.Other", 0, "theorem", "MathEconLibTest.external", "True", 0, 1),
            ]
            for module, position, kind, name, type_value, sorried, render in decls:
                conn.execute("INSERT INTO name_info VALUES (?, ?, ?, ?, ?, ?, ?)",
                             (module, position, kind, name, text(type_value), sorried, render))
            conn.execute("INSERT INTO declaration_args VALUES (?, 0, 0, ?)",
                         ("MathEconLib.Parent.A", text("(x : ℕ)")))
            conn.execute("INSERT INTO definition_equations VALUES (?, 0, 1, ?)",
                         ("MathEconLib.Parent.A", text("MathEconLib.identity x = x")))
            conn.execute("INSERT INTO structures VALUES ('MathEconLib.Parent.B', 0)")
            for sequence, parent in [(1, "SecondParent ℕ"), (0, "FirstParent ℕ")]:
                conn.execute("INSERT INTO structure_parents VALUES (?, 0, ?, ?, ?)",
                             ("MathEconLib.Parent.B", sequence, "MathEconLib.Bundle.to" + parent.split()[0], text(parent)))
            for sequence, name, direct in [(1, "second", 1), (0, "first", 1), (2, "inherited", 0)]:
                conn.execute("INSERT INTO structure_fields VALUES (?, 0, ?, ?, ?, ?)",
                             ("MathEconLib.Parent.B", sequence, "MathEconLib.Bundle." + name, text("ℕ"), direct))
            conn.execute("INSERT INTO declaration_markdown_docstrings VALUES (?, 0, ?)",
                         ("MathEconLib.Parent.A", "Identity docstring."))
            for sequence, binder in [(1, "(x : ℕ)"), (0, "{k : ℕ}")]:
                conn.execute("INSERT INTO structure_field_args VALUES (?, 0, 1, ?, ?)",
                             ("MathEconLib.Parent.B", sequence, text(binder)))

    def run_cli(self, *args):
        return subprocess.run([sys.executable, str(SCRIPTS / "extract_signatures.py"),
                               "--no-build", "--db", str(self.db), "--output", str(self.output), *args],
                              capture_output=True, text=True)

    def contents(self):
        return {p.relative_to(self.output): p.read_bytes() for p in self.output.rglob("*") if p.is_file()}

    def test_split_preserves_parent_declarations_and_filters_modules(self):
        result = self.run_cli("--max-lines", "1", "--docstrings")
        self.assertEqual(result.returncode, 0, result.stderr)
        output = "\n".join(value.decode() for value in self.contents().values())
        self.assertEqual(output.count("theorem MathEconLib.root : True"), 1)
        self.assertEqual(output.count("theorem Nat.local_result : True"), 1)
        self.assertIn("definition MathEconLib.identity (x : ℕ) : ℕ", output)
        self.assertIn("MathEconLib.identity x = x", output)
        self.assertIn("Identity docstring.", output)
        self.assertIn("structure MathEconLib.Bundle extends FirstParent ℕ, SecondParent ℕ : Type\n  where", output)
        self.assertIn("MathEconLib.Bundle.first : ℕ", output)
        self.assertIn("MathEconLib.Bundle.second {k : ℕ} (x : ℕ) : ℕ", output)
        self.assertIn("MathEconLib.unfinished : True [sorry]", output)
        self.assertNotIn("private_helper", output)
        self.assertNotIn("Bundle.inherited", output)
        self.assertNotIn("Mathlib.external", output)
        self.assertNotIn("MathEconLibTest.external", output)
        self.assertIn("7 declarations across 6 modules", (self.output / "README.md").read_text())
        self.assertIn("2 declarations across 1 modules", (self.output / "Parent/B.md").read_text())

    def test_metadata_revision_is_placed_only_in_top_level_index(self):
        metadata = self.root / "metadata.json"
        revision = "a1" * 20
        metadata.write_text(json.dumps({"revision": revision}))
        result = self.run_cli("--metadata", str(metadata), "--max-lines", "1")
        self.assertEqual(result.returncode, 0, result.stderr)
        index = (self.output / "README.md").read_text()
        self.assertIn("(default mode splits into this directory).\n\n"
                      f"Source revision: `{revision}`\n\n**Totals:", index)
        self.assertEqual(index.count("Source revision:"), 1)
        for path, content in self.contents().items():
            if path != Path("README.md"):
                self.assertNotIn(b"Source revision:", content)
        result = self.run_cli("--max-lines", "1")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual((self.output / "README.md").read_text(),
                         index.replace(f"\nSource revision: `{revision}`\n", ""))

    def test_invalid_metadata_revision_does_not_write_output(self):
        metadata = self.root / "metadata.json"
        for revision in ["A" * 40, "a" * 39, "g" * 40, "a" * 40 + "\n", None, 123]:
            with self.subTest(revision=revision):
                metadata.write_text(json.dumps({"revision": revision}))
                result = self.run_cli("--metadata", str(metadata))
                self.assertEqual(result.returncode, 1)
                self.assertIn("revision must be 40 lowercase hex characters", result.stderr)
                self.assertFalse(self.output.exists())

    def test_single_mode_ignores_metadata(self):
        result = self.run_cli("--single", "MathEconLib.Parent", "--metadata", str(self.root / "missing.json"))
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertNotIn("Source revision:", self.output.read_text())

    def test_regeneration_is_deterministic(self):
        self.assertEqual(self.run_cli().returncode, 0)
        before = self.contents()
        self.assertEqual(self.run_cli().returncode, 0)
        self.assertEqual(self.contents(), before)

    def test_class_with_only_parents_preserves_binders_and_parent_order(self):
        parents = ["HasIndependentTypes A", "HasIdenticalTypes A", "HasBoundedTypes A",
                   "HasDensity A", "HasAtomlessTypes A"]
        with sqlite3.connect(self.db) as conn:
            conn.execute("INSERT INTO name_info VALUES (?, 2, 'class', ?, ?, 0, 1)",
                         ("MathEconLib.Parent.B", "MathEconLib.IsSymmetricIPV", text("Prop")))
            conn.execute("INSERT INTO declaration_args VALUES (?, 2, 0, ?)",
                         ("MathEconLib.Parent.B", text("(A : Auction Ω n)")))
            conn.execute("INSERT INTO structures VALUES ('MathEconLib.Parent.B', 2)")
            for sequence, parent in reversed(list(enumerate(parents))):
                conn.execute("INSERT INTO structure_parents VALUES (?, 2, ?, ?, ?)",
                             ("MathEconLib.Parent.B", sequence, "to" + parent.split()[0], text(parent)))
        result = self.run_cli("--single", "MathEconLib.Parent.B")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("class MathEconLib.IsSymmetricIPV (A : Auction Ω n) extends "
                      + ", ".join(parents) + " : Prop\n```", self.output.read_text())

    def test_structure_without_parents_preserves_header_and_direct_fields(self):
        with sqlite3.connect(self.db) as conn:
            conn.execute("DELETE FROM structure_parents")
        result = self.run_cli("--single", "MathEconLib.Parent.B")
        self.assertEqual(result.returncode, 0, result.stderr)
        output = self.output.read_text()
        self.assertIn("structure MathEconLib.Bundle : Type\n  where", output)
        self.assertIn("MathEconLib.Bundle.first : ℕ", output)
        self.assertIn("MathEconLib.Bundle.second {k : ℕ} (x : ℕ) : ℕ", output)
        self.assertNotIn("extends", output)

    def test_parent_removal_type_change_and_reordering_change_output(self):
        for single in (False, True):
            args = ("--single", "MathEconLib.Parent.B") if single else ()
            for mutation, change, params in [
                ("remove", "DELETE FROM structure_parents WHERE sequence = 1", ()),
                ("type", "UPDATE structure_parents SET type = ? WHERE sequence = 1", (text("ChangedParent ℝ"),)),
                ("reorder", "UPDATE structure_parents SET sequence = 1 - sequence", ()),
            ]:
                with self.subTest(single=single, mutation=mutation):
                    self.output = self.root / f"output-{single}-{mutation}"
                    with sqlite3.connect(self.db) as conn:
                        conn.execute("DELETE FROM structure_parents")
                        for sequence, parent in enumerate(["FirstParent ℕ", "SecondParent ℕ"]):
                            conn.execute("INSERT INTO structure_parents VALUES (?, 0, ?, ?, ?)",
                                         ("MathEconLib.Parent.B", sequence, "toParent", text(parent)))
                    self.assertEqual(self.run_cli(*args).returncode, 0)
                    before = self.output.read_bytes() if single else self.contents()
                    with sqlite3.connect(self.db) as conn:
                        conn.execute(change, params)
                    result = self.run_cli(*args)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertNotEqual(self.output.read_bytes() if single else self.contents(), before)

    def test_malformed_parent_and_missing_parent_schema_leave_output_untouched(self):
        self.assertEqual(self.run_cli().returncode, 0)
        before = self.contents()
        with sqlite3.connect(self.db) as conn:
            conn.execute("UPDATE structure_parents SET type = ?", (b"\x00\x05x",))
        result = self.run_cli()
        self.assertEqual(result.returncode, 1)
        self.assertIn("Malformed RenderedCode", result.stderr)
        self.assertEqual(self.contents(), before)
        with sqlite3.connect(self.db) as conn:
            conn.execute("DROP TABLE structure_parents")
        result = self.run_cli()
        self.assertEqual(result.returncode, 1)
        self.assertIn("Incompatible documentation schema: structure_parents", result.stderr)
        self.assertEqual(self.contents(), before)

    def test_regeneration_restores_changed_and_missing_files_and_removes_obsolete_ones(self):
        self.assertEqual(self.run_cli().returncode, 0)
        before = self.contents()
        (self.output / "Parent.md").write_text("changed")
        (self.output / "With_under.md").unlink()
        (self.output / "obsolete.md").write_text("old")
        self.assertEqual(self.run_cli().returncode, 0)
        self.assertEqual(self.contents(), before)

    def test_single_mode_and_literal_underscore_prefix(self):
        result = self.run_cli("--single", "MathEconLib.With_under")
        self.assertEqual(result.returncode, 0, result.stderr)
        content = self.output.read_text()
        self.assertIn("MathEconLib.underscore", content)
        self.assertNotIn("MathEconLib.other", content)
        self.output.write_text("changed")
        self.assertEqual(self.run_cli("--single", "MathEconLib.With_under").returncode, 0)
        self.assertEqual(self.output.read_text(), content)

    def test_malformed_blob_and_missing_schema_leave_output_untouched(self):
        self.assertEqual(self.run_cli().returncode, 0)
        before = self.contents()
        with sqlite3.connect(self.db) as conn:
            conn.execute("UPDATE name_info SET type = ? WHERE name = 'MathEconLib.root'", (b"\x00\x05x",))
        result = self.run_cli()
        self.assertEqual(result.returncode, 1)
        self.assertIn("Malformed RenderedCode", result.stderr)
        self.assertEqual(self.contents(), before)
        with sqlite3.connect(self.db) as conn:
            conn.execute("DROP TABLE declaration_args")
        result = self.run_cli()
        self.assertEqual(result.returncode, 1)
        self.assertIn("Incompatible documentation schema", result.stderr)
        self.assertEqual(self.contents(), before)

    def test_missing_database_and_unknown_prefix_do_not_generate_output(self):
        result = self.run_cli("--root", "Unknown")
        self.assertEqual(result.returncode, 1)
        self.assertIn("No documented modules", result.stderr)
        self.db.unlink()
        result = self.run_cli()
        self.assertEqual(result.returncode, 1)
        self.assertIn("Database not found", result.stderr)
        self.assertFalse(self.output.exists())

    def test_existing_database_requires_no_build_output_and_nonnegative_threshold(self):
        result = subprocess.run([sys.executable, str(SCRIPTS / "extract_signatures.py"),
                                 "--no-build", "--output", str(self.output)],
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 2)
        result = subprocess.run([sys.executable, str(SCRIPTS / "extract_signatures.py"),
                                 "--no-build", "--db", str(self.db)],
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 2)
        self.assertIn("--output", result.stderr)
        self.assertEqual(self.run_cli("--max-lines", "-1").returncode, 2)

    def test_output_cannot_replace_repository_via_parent_components(self):
        result = self.run_cli("--output", str(signatures.REPO_ROOT / "MathEconLib/.."))
        self.assertEqual(result.returncode, 1)
        self.assertIn("Refusing to replace the repository", result.stderr)


class DecoderTest(unittest.TestCase):
    def test_utf8_leb128_and_all_code_tags(self):
        long_text = "∀ x : ℝ, " * 30
        self.assertEqual(signatures.decode_rendered_code(text(long_text)), long_text)
        for tag in [0, 1, 3, 4, 5, 6, 7]:
            self.assertEqual(signatures.decode_rendered_code(bytes([1, tag]) + text("Type")), "Type")
        # Constant tag with the numeric name `Test.150`, then appended text.
        name = b"\x02\x01\x00" + string("Test") + nat(150)
        blob = b"\x02\x02\x01\x02" + name + text("Test") + text(" value")
        self.assertEqual(signatures.decode_rendered_code(blob), "Test value")

    def test_corrupt_truncated_and_trailing_data_are_rejected(self):
        for blob in [b"", b"\x00\x80", b"\x00\x02x", b"\x01\x08" + text("x"),
                     b"\x03", text("ok") + b"extra", b"\x00\x01\xff"]:
            with self.subTest(blob=blob), self.assertRaisesRegex(ValueError, "Malformed RenderedCode"):
                signatures.decode_rendered_code(blob)


if __name__ == "__main__":
    unittest.main()
