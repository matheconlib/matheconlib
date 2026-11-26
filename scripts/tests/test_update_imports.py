"""Exercise import generation and the helper's exit handling without a Lean installation."""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest


HELPER = Path(__file__).resolve().parents[1] / "update-imports.sh"
ROOT = Path("MathEconLib.lean")
CATEGORY = Path("MathEconLib/Index/Topic.lean")
TEST_ROOT = Path("MathEconLibTest.lean")
OUTPUTS = (ROOT, CATEGORY, TEST_ROOT)
LAKE = r'''#!/usr/bin/env python3
import os
from pathlib import Path
import sys

args = sys.argv[1:]
lib = args[args.index("--lib") + 1]
check = "--check" in args
assert lib == "MathEconLibTest"
assert args == ["exe", "mk_all", "--lib", lib, "--git"] + (["--check"] if check else [])
with Path("calls").open("a") as log:
    log.write(lib + (" check\n" if check else " generate\n"))
mode = os.environ.get("TEST_MODE", "normal")
target = Path(lib + ".lean")
expected = "import " + lib + ".Example\n"
if mode == "error1" and not check:
    sys.exit(1)
if mode == "error2" and not check:
    sys.exit(2)
if mode == "error_after_write" and not check:
    target.write_text(expected)
    sys.exit(2)
if mode == "bad_write" and not check:
    target.write_text("invalid\n")
    sys.exit(1)
if mode == "check_error" and check:
    sys.exit(2)
stale = not target.exists() or target.read_bytes() != expected.encode()
if stale and not check:
    target.write_bytes(expected.encode())
sys.exit(int(stale))
'''


class UpdateImportsTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        self.bin = self.root / "bin"
        self.bin.mkdir()
        lake = self.bin / "lake"
        lake.write_text(LAKE)
        lake.chmod(0o755)
        self.env = dict(os.environ, PATH=str(self.bin) + os.pathsep + os.environ["PATH"])
        for source in ("MathEconLib/Topic/Basic.lean", "MathEconLib/Topic.lean",
                       "MathEconLib/Standalone.lean"):
            self.add_source(source)
        result = self.run_helper()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.expected = self.snapshot()
        (self.root / "calls").unlink()

    def add_source(self, source):
        path = self.root / source
        path.parent.mkdir(parents=True, exist_ok=True)
        path.touch()
        subprocess.run(["git", "add", "--", source], cwd=self.root, check=True)

    def snapshot(self):
        return {path: (self.root / path).read_bytes() for path in OUTPUTS}

    def run_helper(self, *args, mode="normal"):
        return subprocess.run(
            ["bash", str(HELPER), *args], cwd=self.root,
            env=dict(self.env, TEST_MODE=mode), text=True, capture_output=True,
        )

    def calls(self):
        log = self.root / "calls"
        return log.read_text().splitlines() if log.exists() else []

    def assert_verified(self):
        self.assertEqual(self.calls(), ["MathEconLibTest generate", "MathEconLibTest check"])
        self.assertEqual(self.snapshot(), self.expected)

    def test_unchanged(self):
        result = self.run_helper()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, "")
        self.assert_verified()

    def test_category_inventory(self):
        self.assertEqual(
            [line for line in self.expected[ROOT].decode().splitlines()
             if line.startswith("public import ")],
            ["public import MathEconLib.Standalone", "public import MathEconLib.Index.Topic"],
        )
        self.assertEqual(
            [line for line in self.expected[CATEGORY].decode().splitlines()
             if line.startswith("public import ")],
            ["public import MathEconLib.Topic", "public import MathEconLib.Topic.Basic"],
        )

    def test_stale_library_and_test_lists(self):
        for output in OUTPUTS:
            path = self.root / output
            path.write_bytes(path.read_bytes() + b"-- stale\n")
        stale = self.snapshot()
        self.assertEqual(self.run_helper("--check").returncode, 1)
        self.assertEqual(self.snapshot(), stale)
        self.assertEqual(self.run_helper().returncode, 0)
        self.assert_verified()

    def test_missing_lists(self):
        for output in OUTPUTS:
            (self.root / output).unlink()
        result = self.run_helper("--check")
        self.assertEqual(result.returncode, 1)
        self.assertFalse(any((self.root / path).exists() for path in OUTPUTS))
        self.assertEqual(self.run_helper().returncode, 0)
        self.assert_verified()

    def test_only_tracked_leaves_affect_indices(self):
        leaf = "MathEconLib/Topic/New.lean"
        (self.root / leaf).touch()
        self.assertEqual(self.run_helper("--check").returncode, 0)
        self.add_source(leaf)
        stale = self.run_helper("--check")
        self.assertEqual(stale.returncode, 1)
        self.assertIn("Topic.lean: stale or missing", stale.stdout)
        self.assertEqual(self.snapshot(), self.expected)
        self.assertEqual(self.run_helper().returncode, 0)
        self.assertEqual((self.root / ROOT).read_bytes(), self.expected[ROOT])
        self.assertIn(b"public import MathEconLib.Topic.New\n", (self.root / CATEGORY).read_bytes())
        self.assertEqual(self.run_helper("--check").returncode, 0)

    def test_category_rename_removes_obsolete_index(self):
        subprocess.run(["git", "add", "--", str(CATEGORY)], cwd=self.root, check=True)
        for old, new in (("Topic.lean", "Renamed.lean"), ("Topic", "Renamed")):
            subprocess.run(["git", "mv", "--", f"MathEconLib/{old}", f"MathEconLib/{new}"],
                           cwd=self.root, check=True)
        old_index = self.root / CATEGORY
        new_index = old_index.with_name("Renamed.lean")
        result = self.run_helper("--check")
        self.assertEqual(result.returncode, 1)
        self.assertIn("Topic.lean: obsolete", result.stdout)
        self.assertTrue(old_index.exists())
        self.assertFalse(new_index.exists())
        self.assertEqual(self.run_helper().returncode, 0)
        self.assertFalse(old_index.exists())
        self.assertIn(b"public import MathEconLib.Renamed.Basic\n", new_index.read_bytes())
        self.assertNotIn(b"MathEconLib.Index.Topic", (self.root / ROOT).read_bytes())
        self.assertEqual(self.run_helper("--check").returncode, 0)

    def test_unmarked_index_is_not_overwritten(self):
        (self.root / CATEGORY).write_bytes(b"-- hand-written content\n")
        before = self.snapshot()
        result = self.run_helper()
        self.assertEqual(result.returncode, 1)
        self.assertIn("reserved for generated import indices", result.stderr)
        self.assertEqual(self.snapshot(), before)

    def test_nested_source_is_rejected_inside_index_directory(self):
        path = "MathEconLib/Index/Nested/Leaf.lean"
        self.add_source(path)
        result = self.run_helper("--check")
        self.assertEqual(result.returncode, 1)
        self.assertIn(f"{path}: reserved for generated import indices", result.stderr)

    def test_eol_only_updates_with_autocrlf(self):
        subprocess.run(["git", "config", "core.autocrlf", "true"], cwd=self.root, check=True)
        (self.root / ".gitattributes").write_text("*.lean text\n")
        before = {}
        for output, expected in self.expected.items():
            path = self.root / output
            path.write_bytes(expected.replace(b"\n", b"\r\n"))
            before[output] = subprocess.check_output(
                ["git", "hash-object", str(path)], cwd=self.root,
            )

        result = self.run_helper()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assert_verified()
        for output, hash_before in before.items():
            # Git's normalized hash cannot detect this real byte-level update.
            self.assertEqual(hash_before, subprocess.check_output(
                ["git", "hash-object", str(self.root / output)], cwd=self.root,
            ))

    def test_exit_one_without_change_is_an_error(self):
        result = self.run_helper(mode="error1")
        self.assertEqual(result.returncode, 1)
        self.assertIn("without updating", result.stderr)
        self.assertEqual(self.calls(), ["MathEconLibTest generate"])

    def test_other_generation_errors_are_preserved(self):
        for mode in ["error2", "error_after_write"]:
            with self.subTest(mode=mode):
                (self.root / "calls").unlink(missing_ok=True)
                result = self.run_helper(mode=mode)
                self.assertEqual(result.returncode, 2)
                self.assertEqual(self.calls(), ["MathEconLibTest generate"])

    def test_verification_rejects_invalid_generated_content(self):
        result = self.run_helper(mode="bad_write")
        self.assertEqual(result.returncode, 1)
        self.assertEqual(self.calls(), ["MathEconLibTest generate", "MathEconLibTest check"])

    def test_verification_errors_are_preserved(self):
        result = self.run_helper(mode="check_error")
        self.assertEqual(result.returncode, 2)

    def test_check_only_does_not_write(self):
        result = self.run_helper("--check")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.calls(), ["MathEconLibTest check"])
        (self.root / "MathEconLibTest.lean").write_text("stale\n")
        result = self.run_helper("--check")
        self.assertEqual(result.returncode, 1)
        self.assertEqual((self.root / "MathEconLibTest.lean").read_text(), "stale\n")

    def test_invalid_arguments(self):
        for args in [("--unknown",), ("--check", "extra")]:
            with self.subTest(args=args):
                self.assertEqual(self.run_helper(*args).returncode, 2)
        self.assertEqual(self.calls(), [])


if __name__ == "__main__":
    unittest.main()
