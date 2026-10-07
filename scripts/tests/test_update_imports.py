"""Exercise the import helper's exit handling without a Lean installation."""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest


HELPER = Path(__file__).resolve().parents[1] / "update-imports.sh"
LIBS = ("Auctionlib", "AuctionlibTest")
LAKE = r'''#!/usr/bin/env python3
import os
from pathlib import Path
import sys

args = sys.argv[1:]
lib = args[args.index("--lib") + 1]
check = "--check" in args
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
if mode == "second_error" and lib == "AuctionlibTest" and not check:
    sys.exit(1)
stale = not target.exists() or target.read_text() != expected
if stale and not check:
    target.write_text(expected)
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
        for lib in LIBS:
            (self.root / (lib + ".lean")).write_text(self.expected(lib))

    @staticmethod
    def expected(lib):
        return "import " + lib + ".Example\n"

    def run_helper(self, *args, mode="normal"):
        return subprocess.run(
            ["bash", str(HELPER), *args], cwd=self.root,
            env=dict(self.env, TEST_MODE=mode), text=True, capture_output=True,
        )

    def calls(self):
        log = self.root / "calls"
        return log.read_text().splitlines() if log.exists() else []

    def assert_verified(self):
        self.assertEqual(self.calls(), [
            "Auctionlib generate", "AuctionlibTest generate",
            "Auctionlib check", "AuctionlibTest check",
        ])
        for lib in LIBS:
            self.assertEqual((self.root / (lib + ".lean")).read_text(), self.expected(lib))

    def test_unchanged(self):
        result = self.run_helper()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assert_verified()

    def test_stale_library_and_test_lists(self):
        for stale in [("Auctionlib",), ("AuctionlibTest",), LIBS]:
            with self.subTest(stale=stale):
                (self.root / "calls").unlink(missing_ok=True)
                for lib in stale:
                    (self.root / (lib + ".lean")).write_text("stale\n")
                result = self.run_helper()
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assert_verified()

    def test_missing_lists(self):
        for lib in LIBS:
            (self.root / (lib + ".lean")).unlink()
        result = self.run_helper()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assert_verified()

    def test_exit_one_without_change_is_an_error(self):
        result = self.run_helper(mode="error1")
        self.assertEqual(result.returncode, 1)
        self.assertIn("without updating", result.stderr)
        self.assertEqual(self.calls(), ["Auctionlib generate"])

    def test_other_generation_errors_are_preserved(self):
        for mode in ["error2", "error_after_write"]:
            with self.subTest(mode=mode):
                (self.root / "calls").unlink(missing_ok=True)
                result = self.run_helper(mode=mode)
                self.assertEqual(result.returncode, 2)
                self.assertEqual(self.calls(), ["Auctionlib generate"])

    def test_second_generation_error_stops_before_verification(self):
        result = self.run_helper(mode="second_error")
        self.assertEqual(result.returncode, 1)
        self.assertEqual(self.calls(), ["Auctionlib generate", "AuctionlibTest generate"])

    def test_verification_rejects_invalid_generated_content(self):
        result = self.run_helper(mode="bad_write")
        self.assertEqual(result.returncode, 1)
        self.assertEqual(self.calls(), [
            "Auctionlib generate", "AuctionlibTest generate", "Auctionlib check",
        ])

    def test_verification_errors_are_preserved(self):
        result = self.run_helper(mode="check_error")
        self.assertEqual(result.returncode, 2)

    def test_check_only_does_not_write(self):
        result = self.run_helper("--check")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.calls(), ["Auctionlib check", "AuctionlibTest check"])
        (self.root / "AuctionlibTest.lean").write_text("stale\n")
        result = self.run_helper("--check")
        self.assertEqual(result.returncode, 1)
        self.assertEqual((self.root / "AuctionlibTest.lean").read_text(), "stale\n")

    def test_invalid_arguments(self):
        for args in [("--unknown",), ("--check", "extra")]:
            with self.subTest(args=args):
                self.assertEqual(self.run_helper(*args).returncode, 2)
        self.assertEqual(self.calls(), [])


if __name__ == "__main__":
    unittest.main()
