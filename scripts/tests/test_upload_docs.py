"""Exercise R2 publication using a stub AWS CLI; never contact storage."""

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
if os.environ.get("AWS_TEST_FAIL") == "1" and sys.argv[1:3] == ["s3", "cp"]:
    sys.exit(1)
''')
        aws.chmod(0o755)
        self.log = self.root / "calls.jsonl"
        self.env = dict(os.environ, PATH=str(binary) + os.pathsep + os.environ["PATH"],
                        AWS_TEST_LOG=str(self.log), R2_BUCKET="test-bucket",
                        R2_ENDPOINT_URL="https://example.invalid", AWS_ACCESS_KEY_ID="fixture",
                        AWS_SECRET_ACCESS_KEY="fixture", GITHUB_RUN_ID="123", GITHUB_RUN_ATTEMPT="2",
                        GITHUB_REF="refs/heads/main", GITHUB_EVENT_NAME="push",
                        GITHUB_STEP_SUMMARY=str(self.root / "summary"))

    def run_helper(self, **env):
        return subprocess.run(["bash", str(HELPER), str(self.output)],
                              env=dict(self.env, **env), capture_output=True, text=True)

    def test_revision_specific_snapshot_and_config_cleanup(self):
        result = self.run_helper()
        self.assertEqual(result.returncode, 0, result.stderr)
        calls = [json.loads(line) for line in self.log.read_text().splitlines()]
        self.assertEqual(calls[0]["args"], ["configure", "set", "default.s3.preferred_transfer_client", "classic"])
        self.assertEqual(len(calls), 4)
        for call, name in zip(calls[1:], ["api-docs.db.gz", "lake-manifest.json", "metadata.json"]):
            self.assertEqual(call["args"][3], f's3://test-bucket/matheconlib/{"a" * 40}/123-2/{name}')
            self.assertEqual(call["region"], "auto")
        self.assertFalse(Path(calls[0]["config"]).parent.exists())
        self.assertIn("api-docs.db.gz", (self.root / "summary").read_text())

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


if __name__ == "__main__":
    unittest.main()
