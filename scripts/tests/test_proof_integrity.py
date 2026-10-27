"""Compile real Lean fixtures and check that proof-integrity failures produce a nonzero exit."""

import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
BACKEND = ROOT / "scripts/CheckProofIntegrity.lean"
DRIVER = ROOT / "scripts/check-proof-integrity.py"
FIXTURES = Path(__file__).with_name("fixtures") / "proof_integrity"
spec = importlib.util.spec_from_file_location("proof_integrity", DRIVER)
driver = importlib.util.module_from_spec(spec)
spec.loader.exec_module(driver)


class CompiledProofIntegrityTest(unittest.TestCase):
    def setUp(self):
        parent = ROOT / ".lake" / "build"
        parent.mkdir(parents=True, exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(prefix="proof-integrity-tests-", dir=parent)
        self.addCleanup(self.temp.cleanup)
        self.work = Path(self.temp.name)
        self.env = dict(os.environ)
        self.env["LEAN_PATH"] = str(self.work) + os.pathsep + self.env.get("LEAN_PATH", "")

    def compile_fixture(self, name):
        path = self.work / (name + ".lean")
        path.write_text((FIXTURES / (name + ".lean.txt")).read_text())
        result = subprocess.run(
            ["lake", "env", "lean", "-R", str(self.work), "-o",
             str(path.with_suffix(".olean")), str(path)],
            cwd=ROOT, env=self.env, capture_output=True, text=True, timeout=90,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def audit(self, *modules):
        path = self.work / "report.json"
        result = subprocess.run(
            ["lake", "env", "lean", "--run", str(BACKEND), str(path), *modules],
            cwd=ROOT, env=self.env, capture_output=True, text=True, timeout=90,
        )
        self.assertTrue(path.exists(), result.stdout + result.stderr)
        return result, json.loads(path.read_text())

    def assert_rejected(self, name, axiom):
        self.compile_fixture(name)
        result, report = self.audit(name)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertEqual(report["status"], "failed")
        self.assertGreater(report["declarations_checked"], 0)
        self.assertTrue(any(axiom in v["axiom"] for v in report["violations"]), report)

    def test_standard_axioms_are_allowed_and_comments_are_harmless(self):
        self.compile_fixture("Good")
        result, report = self.audit("Good")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(report["status"], "passed")
        self.assertEqual(set(report["axioms"]), {"propext", "Classical.choice", "Quot.sound"})
        self.assertEqual(report["violations"], [])

    def test_sorry_is_caught_even_when_warnings_are_not_errors(self):
        self.assert_rejected("Sorry", "sorryAx")

    def test_admit_is_caught(self):
        self.assert_rejected("Admit", "sorryAx")

    def test_unused_axiom_is_caught_in_an_unexpected_namespace(self):
        self.assert_rejected("UnusedAxiom", "UnexpectedNamespace.unused")

    def test_private_unused_axiom_is_caught(self):
        self.assert_rejected("PrivateAxiom", "hiddenAssumption")

    def test_sorry_in_an_imported_dependency_is_caught(self):
        self.compile_fixture("BadDependency")
        self.compile_fixture("Dependent")
        result, report = self.audit("Dependent")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertTrue(any(
            v["axiom"] == "sorryAx" and v["module"] == "Dependent"
            for v in report["violations"]
        ), report)

    def test_imported_custom_axiom_is_caught(self):
        self.compile_fixture("CustomDependency")
        self.compile_fixture("DependentAxiom")
        result, report = self.audit("DependentAxiom")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertTrue(any(
            "importedAssumption" in v["axiom"] and v["module"] == "DependentAxiom"
            for v in report["violations"]
        ), report)

    def test_missing_compiled_module_fails(self):
        result = subprocess.run(
            ["lake", "env", "lean", "--run", str(BACKEND), str(self.work / "missing.json"),
             "ThisModuleDoesNotExist"],
            cwd=ROOT, env=self.env, capture_output=True, text=True, timeout=90,
        )
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)


class SourceInventoryTest(unittest.TestCase):
    def test_anonymous_proofs_and_interpolated_expressions_are_checked(self):
        for token in ("sorry", "admit", "native_decide"):
            with self.subTest(token=token):
                source = "set_option warningAsError false\nexample : True := by " + token
                self.assertEqual(driver.proof_holes(source), [{"token": token, "line": 2}])
        self.assertEqual(driver.proof_holes('def s := s!"value {(by sorry : Nat)}"'),
                         [{"token": "sorry", "line": 1}])

    def test_comments_strings_and_longer_identifiers_are_not_proof_holes(self):
        source = '''-- sorry
/- admit /- native_decide -/ sorry -/
def text := "sorry, admit, native_decide and \\"quotes\\""
def raw := r###"sorry " admit native_decide"###
def «sorry» := '"'
def sorryName := text
def admit' := text
def native_decide? := text
def interpolated := s!"sorry {1} admit"
'''
        self.assertEqual(driver.proof_holes(source), [])

    def test_orphan_test_and_example_sources_are_included(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for relative in ["MathEconLib.lean", "MathEconLib/Unimported.lean",
                             "MathEconLibTest/Unimported.lean", "MathEconLibExamples/Unused.lean",
                             "ApiStability.lean", ".lake/packages/Dependency.lean",
                             "scripts/tests/fixtures/Incomplete.lean.txt",
                             "scripts/tests/fixtures/docs-e2e/Fixture/Holes.lean"]:
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("")
            found = {p.as_posix() for p in driver.discover_sources(root)}
            self.assertEqual(found, {"MathEconLib.lean", "MathEconLib/Unimported.lean",
                                    "MathEconLibTest/Unimported.lean",
                                    "MathEconLibExamples/Unused.lean", "ApiStability.lean"})

    def test_no_sources_fails(self):
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaisesRegex(ValueError, "No project Lean sources"):
                driver.discover_sources(Path(directory))


class DriverIntegrationTest(unittest.TestCase):
    def setUp(self):
        parent = ROOT / ".lake/build"
        parent.mkdir(parents=True, exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(prefix="proof-integrity-project-", dir=parent)
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / "lean-toolchain").write_text((ROOT / "lean-toolchain").read_text())
        (self.root / "lakefile.toml").write_text(
            'name = "fixture"\n[[lean_lib]]\nname = "Fixture"\n')
        (self.root / "Fixture.lean").write_text("module\npublic import Init\n")
        (self.root / "Fixture").mkdir()

    def check(self, source, expected_exit=1):
        # Deliberately absent from Fixture.lean's imports and Lake's default targets.
        (self.root / "Fixture/Orphan.lean").write_text(source)
        report = self.root / "report.json"
        result = subprocess.run(
            [sys.executable, str(DRIVER), "--root", str(self.root), "--report", str(report)],
            cwd=ROOT, capture_output=True, text=True, timeout=120,
        )
        self.assertEqual(result.returncode, expected_exit, result.stdout + result.stderr)
        self.assertTrue(report.exists(), result.stdout + result.stderr)
        return json.loads(report.read_text())

    def check_compiled_fixture(self, name, expected_exit=1):
        source = (FIXTURES / (name + ".lean.txt")).read_text()
        (self.root / "Fixture/Orphan.lean").write_text(source)
        built = subprocess.run(
            ["lake", "--rehash", "--no-ansi", "build", "Fixture.Orphan"],
            cwd=self.root, capture_output=True, text=True, timeout=90,
        )
        self.assertEqual(built.returncode, 0, built.stdout + built.stderr)
        return self.check(source, expected_exit)

    def test_separated_interpolations_with_suppressed_sorry_warnings_are_rejected(self):
        for name in ("SpacedInterpolation", "CommentInterpolation", "NewlineInterpolation"):
            with self.subTest(fixture=name):
                report = self.check_compiled_fixture(name)
                self.assertEqual(report["source_violations"], [])
                self.assertEqual(report["status"], "failed")
                self.assertTrue(any(v["axiom"] == "sorryAx"
                                    for v in report["elaboration_violations"]), report)

    def test_trace_interpolation_without_a_bang_is_rejected(self):
        report = self.check_compiled_fixture("TraceInterpolation")
        self.assertEqual(report["source_violations"], [])
        self.assertEqual(report["status"], "failed")
        self.assertTrue(any(v["axiom"] == "sorryAx"
                            for v in report["elaboration_violations"]), report)

    def test_macro_generated_anonymous_hole_is_rejected(self):
        report = self.check_compiled_fixture("MacroHole")
        self.assertEqual(report["source_violations"], [])
        self.assertEqual(report["status"], "failed")
        self.assertTrue(any(v["axiom"] == "sorryAx"
                            for v in report["elaboration_violations"]), report)

    def test_later_example_in_one_macro_command_is_also_audited(self):
        report = self.check_compiled_fixture("RepeatedExamples")
        self.assertEqual(report["source_violations"], [])
        self.assertEqual(report["status"], "failed")
        self.assertTrue(any(v["axiom"] == "sorryAx"
                            for v in report["elaboration_violations"]), report)

    def test_completed_examples_and_literal_proof_words_are_allowed(self):
        report = self.check_compiled_fixture("CompleteInterpolations", expected_exit=0)
        self.assertEqual(report["status"], "passed")
        self.assertEqual(report["elaboration_violations"], [])
        self.assertGreater(report["elaboration_declarations_checked"], 0)

    def test_evaluation_commands_are_not_treated_as_proof_axioms(self):
        report = self.check_compiled_fixture("Evaluation", expected_exit=0)
        self.assertEqual(report["status"], "passed")
        self.assertEqual(report["elaboration_violations"], [])
        self.assertGreater(report["elaboration_declarations_checked"], 0)

    def test_unused_axiom_in_an_unimported_file_is_built_and_rejected(self):
        report = self.check("module\npublic import Init\npublic axiom unused : False\n")
        self.assertEqual(report["stage"], "complete", report)
        self.assertEqual(report["status"], "failed")
        self.assertIn("Fixture/Orphan.lean", report["sources"])
        self.assertTrue(any(v["axiom"] == "unused" for v in report["violations"]), report)

    def test_anonymous_sorry_is_rejected(self):
        report = self.check("module\npublic import Init\nset_option warningAsError false\n"
                            "example : False := by sorry\n")
        self.assertEqual(report["status"], "failed")
        self.assertEqual(report["source_violations"],
                         [{"source": "Fixture/Orphan.lean", "line": 4, "token": "sorry"}])

    def test_build_errors_fail_and_leave_a_report(self):
        report = self.check("module\npublic import Init\ntheorem broken : True := 0\n")
        self.assertEqual(report["status"], "error")
        self.assertEqual(report["stage"], "build")


if __name__ == "__main__":
    unittest.main(verbosity=2)
