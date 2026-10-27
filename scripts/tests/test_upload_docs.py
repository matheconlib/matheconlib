"""Exercise R2 publication using stub AWS and Git CLIs; never contact storage."""

import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


HELPER = Path(__file__).resolve().parents[1] / "upload-docs.sh"


class UploadDocumentationTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.output = self.root / "output"
        self.output.mkdir()
        (self.output / "metadata.json").write_text(json.dumps({"revision": "a" * 40}))
        for filename in ["api-docs.db.gz", "lake-manifest.json"]:
            (self.output / filename).write_text("fixture")
        binary = self.root / "bin"
        binary.mkdir()
        aws = binary / "aws"
        aws.write_text('''#!/usr/bin/env python3
import json, os, sys
with open(os.environ["AWS_TEST_LOG"], "a") as log:
    log.write(json.dumps({"args": sys.argv[1:], "config": os.environ["AWS_CONFIG_FILE"], "region": os.environ["AWS_DEFAULT_REGION"]}) + "\\n")
    if sys.argv[1:4] == ["s3", "cp", "-"]:
        log.write(json.dumps({"stdin": sys.stdin.read()}) + "\\n")
if os.environ.get("AWS_TEST_FAIL") == "1" and sys.argv[1:3] == ["s3", "cp"]:
    sys.exit(1)
if sys.argv[1:3] == ["s3", "cp"] and sys.argv[4] == "-":
    pointer = os.environ.get("AWS_TEST_POINTER")
    if not pointer:
        sys.exit(1)
    print(pointer)
if sys.argv[1:3] == ["s3api", "list-objects-v2"]:
    print(os.environ.get("AWS_TEST_TREES", "None"))
''')
        aws.chmod(0o755)
        git = binary / "git"
        # Every commit exists locally; `diff --quiet` reports GIT_TEST_DOCS_CHANGED.
        git.write_text('''#!/usr/bin/env python3
import os, sys
if sys.argv[1] == "ls-remote":
    assert sys.argv[2:] == ["origin", "refs/heads/main"], sys.argv
    print(os.environ["GIT_TEST_MAIN"] + "\\trefs/heads/main")
elif sys.argv[1] == "diff":
    sys.exit(1 if os.environ.get("GIT_TEST_DOCS_CHANGED") == "1" else 0)
else:
    assert sys.argv[1:3] == ["cat-file", "-e"], sys.argv
''')
        git.chmod(0o755)
        self.log = self.root / "calls.jsonl"
        self.env = dict(os.environ, PATH=str(binary) + os.pathsep + os.environ["PATH"],
                        AWS_TEST_LOG=str(self.log), R2_BUCKET="test-bucket",
                        R2_ENDPOINT_URL="https://example.invalid", AWS_ACCESS_KEY_ID="fixture",
                        AWS_SECRET_ACCESS_KEY="fixture", GITHUB_RUN_ID="123", GITHUB_RUN_ATTEMPT="2",
                        GITHUB_REF="refs/heads/main", GITHUB_EVENT_NAME="push",
                        GITHUB_STEP_SUMMARY=str(self.root / "summary"), GIT_TEST_MAIN="a" * 40)

    def run_helper(self, **env):
        return subprocess.run(["bash", str(HELPER), str(self.output)],
                              env=dict(self.env, **env), capture_output=True, text=True)

    def calls(self):
        return [json.loads(line) for line in self.log.read_text().splitlines()]

    def test_revision_specific_snapshot_and_config_cleanup(self):
        result = self.run_helper()
        self.assertEqual(result.returncode, 0, result.stderr)
        calls = self.calls()
        self.assertEqual(calls[0]["args"], ["configure", "set", "default.s3.preferred_transfer_client", "classic"])
        for call, name in zip(calls[1:4], ["api-docs.db.gz", "lake-manifest.json", "metadata.json"]):
            self.assertEqual(call["args"][3], f's3://test-bucket/matheconlib/{"a" * 40}/123-2/{name}')
            self.assertEqual(call["region"], "auto")
        self.assertFalse(Path(calls[0]["config"]).parent.exists())
        self.assertIn("api-docs.db.gz", (self.root / "summary").read_text())

    def test_html_tree_moves_pointer_last_and_prunes_all_but_previous(self):
        tree = f'matheconlib/html/{"a" * 40}-123-2/'
        previous = "matheconlib/html/old-1-1/"
        result = self.run_helper(
            AWS_TEST_POINTER=json.dumps({"revision": "o" * 40, "prefix": previous}),
            AWS_TEST_TREES="\t".join([previous, tree, "matheconlib/html/stale-2-1/"]))
        self.assertEqual(result.returncode, 0, result.stderr)
        calls = self.calls()
        args = [call.get("args") for call in calls]
        sync = args.index(["s3", "sync", str(self.output / "doc"), f"s3://test-bucket/{tree}",
                           "--endpoint-url", "https://example.invalid", "--only-show-errors"])
        written = next(i for i, call in enumerate(calls) if "stdin" in call)
        self.assertGreater(written, sync)
        self.assertEqual(args[written - 1][3], "s3://test-bucket/matheconlib/html/current.json")
        self.assertEqual(json.loads(calls[written]["stdin"]), {"revision": "a" * 40, "prefix": tree})
        removed = [(i, a[3]) for i, a in enumerate(args) if a and a[:2] == ["s3", "rm"]]
        self.assertEqual([key for _, key in removed], ["s3://test-bucket/matheconlib/html/stale-2-1/"])
        self.assertGreater(removed[0][0], written)
        self.assertIn(tree, (self.root / "summary").read_text())

    def test_first_publication_writes_pointer_and_keeps_its_tree(self):
        tree = f'matheconlib/html/{"a" * 40}-123-2/'
        result = self.run_helper(AWS_TEST_TREES=tree)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(any("stdin" in call for call in self.calls()))
        self.assertFalse([c for c in self.calls() if c.get("args", [])[:2] == ["s3", "rm"]])

    def test_superseded_revision_keeps_database_but_skips_html(self):
        result = self.run_helper(GIT_TEST_MAIN="b" * 40, GIT_TEST_DOCS_CHANGED="1",
                                 AWS_TEST_TREES="matheconlib/html/stale-2-1/")
        self.assertEqual(result.returncode, 0, result.stderr)
        args = [call.get("args") for call in self.calls()]
        self.assertEqual(sum(1 for a in args if a and a[:2] == ["s3", "cp"]), 3)
        self.assertFalse(any(a and a[:2] in (["s3", "sync"], ["s3", "rm"]) for a in args))
        self.assertFalse(any("stdin" in call for call in self.calls()))

    def test_newer_main_without_documentation_changes_still_publishes(self):
        tree = f'matheconlib/html/{"a" * 40}-123-2/'
        result = self.run_helper(GIT_TEST_MAIN="b" * 40, AWS_TEST_TREES=tree)
        self.assertEqual(result.returncode, 0, result.stderr)
        written = next(call for call in self.calls() if "stdin" in call)
        self.assertEqual(json.loads(written["stdin"])["prefix"], tree)

    def test_missing_configuration_fails_before_aws(self):
        result = self.run_helper(R2_BUCKET="")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("R2_BUCKET", result.stderr)
        self.assertFalse(self.log.exists())

    def test_upload_failure_does_not_publish_metadata_or_success_summary(self):
        result = self.run_helper(AWS_TEST_FAIL="1")
        self.assertNotEqual(result.returncode, 0)
        calls = [json.loads(line) for line in self.log.read_text().splitlines()]
        self.assertEqual(len(calls), 2)
        self.assertFalse((self.root / "summary").exists())
        self.assertFalse(Path(calls[0]["config"]).parent.exists())

    def test_invalid_run_identity_fails_before_aws(self):
        result = self.run_helper(GITHUB_RUN_ID="../other")
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(self.log.exists())

    def test_pr_and_non_main_events_never_publish(self):
        for event, ref in [("pull_request", "refs/heads/main"), ("push", "refs/heads/feature"),
                           ("workflow_dispatch", "refs/heads/feature")]:
            with self.subTest(event=event, ref=ref):
                result = self.run_helper(GITHUB_EVENT_NAME=event, GITHUB_REF=ref)
                self.assertNotEqual(result.returncode, 0)
                self.assertFalse(self.log.exists())

    def test_manual_main_run_can_publish(self):
        result = self.run_helper(GITHUB_EVENT_NAME="workflow_dispatch")
        self.assertEqual(result.returncode, 0, result.stderr)


class DocumentationInputsTest(unittest.TestCase):
    """Compare commits in a scratch repository with the real Git CLI."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name)
        self.git("init", "-q")
        for path in ["MathEconLib.lean", "MathEconLib/A.lean", "MathEconLibTest/T.lean", "README.md"]:
            self.write(path, "initial")
        self.base = self.commit()

    def git(self, *args):
        return subprocess.run(["git", "-c", "user.name=Test", "-c", "user.email=test@example.invalid", *args],
                              cwd=self.repo, check=True, capture_output=True, text=True).stdout.strip()

    def write(self, path, text):
        (self.repo / path).parent.mkdir(parents=True, exist_ok=True)
        (self.repo / path).write_text(text)

    def commit(self):
        self.git("add", "-A")
        self.git("commit", "-q", "--allow-empty", "-m", "change")
        return self.git("rev-parse", "HEAD")

    def changed(self, before, after):
        return subprocess.run(["bash", str(HELPER.with_name("docs-inputs-changed.sh")), before, after],
                              cwd=self.repo, capture_output=True, text=True).returncode

    def test_library_sources_pins_and_tooling_are_inputs(self):
        for path in ["MathEconLib/Sub/B.lean", "MathEconLib.lean", "lean-toolchain", "lake-manifest.json",
                     "scripts/build_docs.py", ".github/workflows/lean_action_ci.yaml"]:
            with self.subTest(path=path):
                self.write(path, path)
                self.assertEqual(self.changed(self.base, self.commit()), 0)
                self.git("reset", "-q", "--hard", self.base)

    def test_tests_prose_and_non_lean_library_files_are_not_inputs(self):
        for path in ["MathEconLibTest/T.lean", "README.md", "MathEconLib/notes.md", "website/index.html"]:
            with self.subTest(path=path):
                self.write(path, "changed")
                self.assertEqual(self.changed(self.base, self.commit()), 1)
                self.git("reset", "-q", "--hard", self.base)

    def test_invalid_or_unavailable_commits_are_errors(self):
        for before in ["0" * 40, "HEAD", "f" * 40]:
            with self.subTest(before=before):
                self.assertEqual(self.changed(before, self.base), 2)


if __name__ == "__main__":
    unittest.main()
