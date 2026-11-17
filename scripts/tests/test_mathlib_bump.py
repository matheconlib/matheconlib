"""Exercise the Mathlib bump scripts without network access, Lean or GitHub.

Each test builds a throwaway project repository with a local bare `origin`, a
local stand-in for the Mathlib repository, and fake `lake`, `elan`, `curl` and
`gh` commands. Project checks that the bump script calls are replaced by stubs
that fail on request, so every path runs in seconds and writes nothing outside
the temporary directory.
"""

import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


SCRIPTS = Path(__file__).resolve().parents[1]
BUMP = SCRIPTS / "mathlib_bump.sh"
PUBLISH = SCRIPTS / "mathlib_bump_publish.sh"
BOT = ("github-actions[bot]", "github-actions[bot]@users.noreply.github.com")
RELEASE_DATE = "2026-11-16T19:03:49Z"

LAKEFILE = '''name = "matheconlib"
defaultTargets = ["MathEconLib"]

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.35.0"

[[lean_lib]]
name = "MathEconLib"
'''

FAKE_LAKE = r'''#!/usr/bin/env python3
import json, os, subprocess, sys, tomllib
from pathlib import Path
args = sys.argv[1:]
with open(os.environ["FAKE_STATE"] + "/calls", "a") as log:
    log.write("lake " + " ".join(args) + "\n")
fail = os.environ.get("FAKE_FAIL", "")
if args == ["update", "mathlib"]:
    if fail == "lake-update":
        sys.exit("lake update failed")
    rev = next(r["rev"] for r in tomllib.loads(Path("lakefile.toml").read_text())["require"]
               if r["name"] == "mathlib")
    upstream = os.environ["MATHLIB_URL"]
    sha = subprocess.run(["git", "-C", upstream, "rev-parse", rev + "^{commit}"],
                         check=True, capture_output=True, text=True).stdout.strip()
    toolchain = subprocess.run(["git", "-C", upstream, "show", rev + ":lean-toolchain"],
                               check=True, capture_output=True, text=True).stdout
    manifest = json.loads(Path("lake-manifest.json").read_text())
    for package in manifest["packages"]:
        if package["name"] == "mathlib":
            package["inputRev"] = rev
            package["rev"] = os.environ.get("FAKE_MANIFEST_REV", sha)
    Path("lake-manifest.json").write_text(json.dumps(manifest, indent=1) + "\n")
    Path(".lake/packages/mathlib").mkdir(parents=True, exist_ok=True)
    Path(".lake/packages/mathlib/lean-toolchain").write_text(toolchain)
elif args == ["exe", "cache", "get"]:
    sys.exit(1 if fail == "cache-get" else 0)
elif args == ["--rehash", "--no-ansi", "build"]:
    print("warning: MathEconLib/Basic.lean:3:4: unused variable `x`")
    print("warning: MathEconLib/Basic.lean:9:2: this tactic is never executed")
    print("Build completed successfully." if fail != "lake-build" else "error: build failed")
    sys.exit(1 if fail == "lake-build" else 0)
else:
    sys.exit("unexpected lake call: " + " ".join(args))
'''

FAKE_ELAN = r'''#!/usr/bin/env bash
echo "elan $*" >> "$FAKE_STATE/calls"
[ "$1 $2" = "toolchain list" ] && exit 0
[ "$1 $2" = "toolchain install" ] && [ "${FAKE_FAIL:-}" != elan-toolchain ] && exit 0
exit 1
'''

FAKE_CURL = r'''#!/usr/bin/env bash
url="${@: -1}"
echo "curl $url" >> "$FAKE_STATE/calls"
case "$url" in
  https://raw.githubusercontent.com/leanprover-community/mathlib4/*/lean-toolchain)
    [ "${FAKE_FAIL:-}" = discover ] && exit 22
    ref=${url#https://raw.githubusercontent.com/leanprover-community/mathlib4/}
    git -C "$MATHLIB_URL" show "${ref%/lean-toolchain}:lean-toolchain" ;;
  https://api.github.com/repos/leanprover-community/mathlib4/releases/tags/*)
    echo '{"published_at": "2026-11-16T19:03:49Z"}' ;;
  *) exit 22 ;;
esac
'''

# A stateful stand-in for the gh commands the publish script uses.
FAKE_GH = r'''#!/usr/bin/env python3
import json, os, sys
from pathlib import Path
state = Path(os.environ["FAKE_STATE"])
args = sys.argv[1:]
with open(state / "calls", "a") as log:
    log.write("gh " + json.dumps(args) + "\n")
db_path = state / "github.json"
db = json.loads(db_path.read_text()) if db_path.exists() else {"prs": [], "issues": []}
def opt(name):
    return args[args.index(name) + 1] if name in args else None
def save():
    db_path.write_text(json.dumps(db, indent=1))
cmd = args[:2]
if cmd == ["pr", "list"]:
    print(json.dumps([p for p in db["prs"] if p["headRefName"] == opt("--head")]))
elif cmd == ["pr", "create"]:
    if os.environ.get("FAKE_GH_FAIL_CREATE"):
        sys.exit("HTTP 502: gh pr create failed")
    number = len(db["prs"]) + len(db["issues"]) + 1
    url = f"https://github.com/o/r/pull/{number}"
    db["prs"].append({"number": number, "state": "OPEN", "url": url, "headRefName": opt("--head"),
                      "isDraft": "--draft" in args, "title": opt("--title"), "body": opt("--body")})
    save()
    print(url)
elif cmd == ["issue", "list"]:
    print(json.dumps([{"number": i["number"], "title": i["title"]}
                      for i in db["issues"] if i["state"] == "OPEN"]))
elif cmd == ["issue", "create"]:
    number = len(db["prs"]) + len(db["issues"]) + 1
    db["issues"].append({"number": number, "state": "OPEN", "title": opt("--title"), "comments": []})
    save()
    print(f"https://github.com/o/r/issues/{number}")
elif cmd == ["issue", "view"]:
    issue = next(i for i in db["issues"] if i["number"] == int(args[2]))
    print(json.dumps({"comments": [{"body": b} for b in issue["comments"]]}))
elif cmd == ["issue", "comment"]:
    issue = next(i for i in db["issues"] if i["number"] == int(args[2]))
    issue["comments"].append(opt("--body"))
    save()
else:
    sys.exit("unexpected gh call: " + " ".join(args))
'''

# Project checks called by the bump script, each failing when FAKE_FAIL names it.
STUBS = {
    "scripts/check-headers.sh": "check-headers",
    "scripts/update-imports.sh": "check-imports",
    "scripts/tests/test_update_imports.py": "test-update-imports",
    "scripts/tests/test_warning_counts.cjs": "test-warning-counts",
    "scripts/tests/test_mathlib_bump.py": "test-mathlib-bump",
    "scripts/tests/test_proof_integrity.py": "test-proof-integrity",
    "scripts/check-proof-integrity.py": "proof-integrity",
    "scripts/check-bic-regressions.py": "bic-regressions",
    "scripts/tests/check_bic_contract.py": "bic-contract",
}
PY_STUB = '''import os, sys
if "--report" in sys.argv:
    status = "failed" if os.environ.get("FAKE_FAIL") == "{name}" else "passed"
    open(sys.argv[sys.argv.index("--report") + 1], "w").write('{{"status": "%s"}}\\n' % status)
sys.exit(1 if os.environ.get("FAKE_FAIL") == "{name}" else 0)
'''
SH_STUB = '[ "${{FAKE_FAIL:-}}" != {name} ]\n'
JS_STUB = 'process.exit(process.env.FAKE_FAIL === "{name}" ? 1 : 0);\n'


GIT_ENV = {
    "PATH": os.environ["PATH"], "LANG": "C.UTF-8",
    "GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": os.devnull,
    "GIT_AUTHOR_NAME": BOT[0], "GIT_AUTHOR_EMAIL": BOT[1],
    "GIT_COMMITTER_NAME": BOT[0], "GIT_COMMITTER_EMAIL": BOT[1],
}


def git(cwd, *args, check=True):
    return subprocess.run(["git", *args], cwd=cwd, env={**GIT_ENV, "HOME": str(cwd)}, check=check,
                          capture_output=True, text=True).stdout.strip()


def write(path, text, mode=None):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)
    if mode:
        path.chmod(mode)


class BumpTest(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="mathlib-bump-test-"))
        self.addCleanup(shutil.rmtree, self.tmp)
        self.state = self.tmp / "state"
        self.state.mkdir()
        bin_dir = self.tmp / "bin"
        for name, text in {"lake": FAKE_LAKE, "elan": FAKE_ELAN, "curl": FAKE_CURL,
                           "gh": FAKE_GH}.items():
            write(bin_dir / name, text, 0o755)
        self.env = {
            **GIT_ENV,
            "PATH": f"{bin_dir}:{os.environ['PATH']}",
            "HOME": str(self.tmp),
            "FAKE_STATE": str(self.state),
            "MATHLIB_URL": str(self.make_mathlib()),
        }
        self.origin = self.tmp / "origin.git"
        self.repo = self.tmp / "repo"
        self.make_project()

    def make_mathlib(self):
        """A local Mathlib with stable, RC and annotated tags."""
        mathlib = self.tmp / "mathlib"
        mathlib.mkdir()
        git(mathlib, "init", "-q", "-b", "master")
        for tag in ["v4.35.0", "v4.36.0-rc1", "v4.36.0", "v4.36.1", "v4.37.0-rc1"]:
            write(mathlib / "lean-toolchain", f"leanprover/lean4:{tag}\n")
            git(mathlib, "add", ".")
            git(mathlib, "-c", "user.name=m", "-c", "user.email=m@example.com",
                "commit", "-q", "-m", tag)
            if tag == "v4.36.1":
                git(mathlib, "-c", "user.name=m", "-c", "user.email=m@example.com",
                    "tag", "-a", "-m", tag, tag)
            else:
                git(mathlib, "tag", tag)
        self.sha = {t: git(mathlib, "rev-parse", t + "^{commit}")
                    for t in ["v4.35.0", "v4.36.0", "v4.36.1"]}
        return mathlib

    def make_project(self):
        repo = self.repo
        write(repo / "lakefile.toml", LAKEFILE)
        write(repo / "lean-toolchain", "leanprover/lean4:v4.35.0\n")
        manifest = {"version": "1.1.0", "packagesDir": ".lake/packages", "name": "matheconlib",
                    "lakeDir": ".lake", "packages": [
                        {"name": "mathlib", "scope": "leanprover-community", "type": "git",
                         "url": "https://github.com/leanprover-community/mathlib4",
                         "rev": self.sha["v4.35.0"], "inputRev": "v4.35.0"}]}
        write(repo / "lake-manifest.json", json.dumps(manifest, indent=1) + "\n")
        write(repo / ".gitignore", ".lake/\n")
        for script in [BUMP, PUBLISH, SCRIPTS / "warning-counts.cjs"]:
            write(repo / "scripts" / script.name, script.read_text())
        for path, name in STUBS.items():
            stub = {".py": PY_STUB, ".sh": SH_STUB, ".cjs": JS_STUB}[Path(path).suffix]
            write(repo / path, stub.format(name=name))
        git(self.tmp, "init", "-q", "--bare", "-b", "main", str(self.origin))
        git(repo, "init", "-q", "-b", "main")
        git(repo, "add", ".")
        git(repo, "commit", "-q", "-m", "init")
        git(repo, "remote", "add", "origin", str(self.origin))
        git(repo, "push", "-q", "origin", "main")

    def bump(self, *args, fail=None, log_dir=None, **env):
        log_dir = log_dir or self.tmp / "logs"
        extra = {"FAKE_FAIL": fail} if fail else {}
        proc = subprocess.run(["bash", "scripts/mathlib_bump.sh", "--log-dir", str(log_dir), *args],
                              cwd=self.repo, env={**self.env, **extra, **env},
                              capture_output=True, text=True)
        summary = {}
        if (log_dir / "summary.txt").exists():
            for line in (log_dir / "summary.txt").read_text().splitlines():
                key, sep, value = line.partition("=")
                if sep and " " not in key:
                    summary[key] = value
        return proc, summary

    def publish(self, log_dir=None, **env):
        """Run the publish script from a fresh checkout of origin/main, as the publish job does."""
        checkout = self.tmp / "publisher"
        if checkout.exists():
            shutil.rmtree(checkout)
        git(self.tmp, "clone", "-q", str(self.origin), str(checkout))
        env = {**self.env, "GITHUB_ACTIONS": "true", "GITHUB_SERVER_URL": "https://github.com",
               "GITHUB_REPOSITORY": "o/r", "GITHUB_RUN_ID": "42", **env}
        return subprocess.run(["bash", "scripts/mathlib_bump_publish.sh",
                               str(log_dir or self.tmp / "logs")],
                              cwd=checkout, env=env, capture_output=True, text=True)

    def calls(self, prefix):
        path = self.state / "calls"
        lines = path.read_text().splitlines() if path.exists() else []
        return [line for line in lines if line.startswith(prefix)]

    def github(self):
        path = self.state / "github.json"
        return json.loads(path.read_text()) if path.exists() else {"prs": [], "issues": []}

    def remote_branch(self, name="chore/bump-mathlib-v4.36.1"):
        return git(self.tmp, "--git-dir", str(self.origin), "rev-parse", "--verify", "--quiet",
                   "refs/heads/" + name, check=False)

    # Discovery and target selection

    def test_noop_with_consistent_pins(self):
        proc, s = self.bump("--target", "v4.35.0")
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertEqual(s["result"], "up-to-date")
        self.assertEqual(s["target_sha"], self.sha["v4.35.0"])
        self.assertEqual(git(self.repo, "branch", "--show-current"), "main")
        self.assertEqual(self.calls("lake"), [])

    def test_noop_with_inconsistent_pins_fails(self):
        manifest = json.loads((self.repo / "lake-manifest.json").read_text())
        manifest["packages"][0]["rev"] = self.sha["v4.36.0"]
        write(self.repo / "lake-manifest.json", json.dumps(manifest))
        git(self.repo, "commit", "-qam", "drift")
        proc, s = self.bump("--target", "v4.35.0")
        self.assertEqual(proc.returncode, 1)
        self.assertEqual((s["result"], s["failed_step"]), ("failed", "check-pins"))
        self.assertIn("resolves mathlib to", (self.tmp / "logs/01-check-pins.log").read_text())

    def test_default_target_is_latest_stable_and_records_skipped(self):
        proc, s = self.bump("--no-commit")
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertEqual(s["target"], "v4.36.1")
        self.assertEqual(s["target_sha"], self.sha["v4.36.1"])  # annotated tag, peeled
        self.assertEqual(s["skipped_releases"], "v4.36.0")
        self.assertEqual(s["release_date"], RELEASE_DATE)

    def test_rc_target_rejected(self):
        proc, s = self.bump("--target", "v4.37.0-rc1")
        self.assertEqual(proc.returncode, 1)
        self.assertEqual(s["failed_step"], "select-target")
        self.assertEqual(git(self.repo, "branch", "--show-current"), "main")

    def test_older_target_rejected(self):
        self.bump("--target", "v4.36.0")
        git(self.repo, "switch", "-q", "main")
        git(self.repo, "merge", "-q", "chore/bump-mathlib-v4.36.0")
        proc, s = self.bump("--target", "v4.35.0", log_dir=self.tmp / "logs2")
        self.assertEqual(proc.returncode, 1)
        self.assertEqual(s["failed_step"], "select-target")
        self.assertIn("older than the current pin", proc.stderr)

    def test_unstable_override_is_probe_only(self):
        proc, _ = self.bump("--target", "v4.37.0-rc1", "--allow-unstable")
        self.assertEqual(proc.returncode, 2)
        proc, s = self.bump("--target", "v4.37.0-rc1", "--probe", "--allow-unstable")
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertEqual(s["result"], "compatible")
        self.assertNotIn("commit", s)

    def test_probe_on_current_pin_runs_every_check(self):
        proc, s = self.bump("--probe", "--target", "v4.35.0")
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertEqual(s["result"], "compatible")
        self.assertIn("lake --rehash --no-ansi build", self.calls("lake"))
        self.assertEqual(git(self.repo, "branch", "--show-current"), "main")
        self.assertNotIn("branch", s)

    # Bump runs

    def test_successful_bump_commits_locally_without_publishing(self):
        proc, s = self.bump()
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertEqual(s["result"], "bumped")
        self.assertEqual(s["branch"], "chore/bump-mathlib-v4.36.1")
        self.assertEqual(git(self.repo, "rev-parse", "HEAD"), s["commit"])
        message = git(self.repo, "log", "-1", "--format=%B")
        self.assertTrue(message.startswith("chore: bump Mathlib to v4.36.1\n"))
        self.assertIn(self.sha["v4.36.1"], message)
        self.assertIn("not ported separately: v4.36.0", message)
        self.assertEqual(s["passed_steps"].split(), [
            "set-pins", "elan-toolchain", "lake-update", "check-pins", "cache-get",
            "check-headers", "test-update-imports", "test-warning-counts", "test-mathlib-bump",
            "check-imports", "lake-build", "test-proof-integrity", "proof-integrity",
            "bic-regressions", "bic-contract"])
        logs = self.tmp / "logs"
        self.assertEqual(json.loads((logs / "warning-counts.json").read_text())["total"], 2)
        self.assertTrue((logs / "proof-integrity-report.json").exists())
        self.assertEqual(json.loads((logs / "lake-manifest.json").read_text())
                         ["packages"][0]["rev"], self.sha["v4.36.1"])
        self.assertTrue((logs / "bump.bundle").exists())
        # The local script never pushes and never calls gh.
        self.assertEqual(self.remote_branch(), "")
        self.assertEqual(self.calls("gh"), [])

    def test_publish_is_a_noop_outside_actions(self):
        self.bump()
        proc = self.publish(GITHUB_ACTIONS="")
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertEqual(self.remote_branch(), "")
        self.assertEqual(self.calls("gh"), [])

    def test_manifest_resolving_to_another_sha_fails(self):
        proc, s = self.bump(FAKE_MANIFEST_REV=self.sha["v4.36.0"])
        self.assertEqual(proc.returncode, 1)
        self.assertEqual(s["failed_step"], "check-pins")

    def test_early_failure_records_evidence_without_commit(self):
        proc, s = self.bump(fail="discover")
        self.assertEqual(proc.returncode, 1)
        self.assertEqual((s["result"], s["failed_step"]), ("failed", "discover"))
        self.assertEqual(s["target"], "v4.36.1")
        self.assertNotIn("commit", s)
        self.assertEqual(git(self.repo, "branch", "--show-current"), "main")

    def test_build_failure_commits_unverified_partial_bump(self):
        proc, s = self.bump(fail="lake-build")
        self.assertEqual(proc.returncode, 1)
        self.assertEqual(s["failed_step"], "lake-build")
        self.assertTrue(s["remaining_steps"].startswith("test-proof-integrity"))
        message = git(self.repo, "log", "-1", "--format=%B")
        self.assertTrue(message.startswith("chore: bump Mathlib to v4.36.1 (unverified)\n"))
        self.assertIn("NOT verified", message)
        self.assertEqual(s["commit"], git(self.repo, "rev-parse", "HEAD"))
        self.assertEqual(s["warnings_total"], "2")
        self.assertTrue((self.tmp / "logs/warning-counts.json").exists())

    def test_audit_failure_keeps_report(self):
        proc, s = self.bump(fail="proof-integrity")
        self.assertEqual(proc.returncode, 1)
        self.assertEqual(s["failed_step"], "proof-integrity")
        report = json.loads((self.tmp / "logs/proof-integrity-report.json").read_text())
        self.assertEqual(report["status"], "failed")

    # Publication and recovery

    def test_successful_publication_opens_ready_pr(self):
        self.bump()
        proc = self.publish()
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertEqual(self.remote_branch(), git(self.repo, "rev-parse", "HEAD"))
        [pr] = self.github()["prs"]
        self.assertFalse(pr["isDraft"])
        self.assertEqual(pr["title"], "chore: bump Mathlib to v4.36.1")
        self.assertIn(self.sha["v4.36.1"], pr["body"])
        self.assertIn("Approve workflows to run", pr["body"])

    def test_check_failure_opens_draft_pr_with_failed_step(self):
        self.bump(fail="bic-contract")
        proc = self.publish(MATHLIB_BUMP_OWNER="lead")
        self.assertEqual(proc.returncode, 0, proc.stderr)
        [pr] = self.github()["prs"]
        self.assertTrue(pr["isDraft"])
        self.assertIn("(unverified)", pr["title"])
        self.assertIn("Failed step: bic-contract", pr["body"])
        self.assertIn("Owner: @lead", pr["body"])
        self.assertIn("Last lines of 15-bic-contract.log", pr["body"])

    def test_early_failure_reported_once_on_tracking_issue(self):
        self.bump(fail="discover")
        for _ in range(2):
            proc = self.publish()
            self.assertEqual(proc.returncode, 0, proc.stderr)
        [issue] = self.github()["issues"]
        self.assertEqual(len(issue["comments"]), 1)
        self.assertIn("Failed step: discover", issue["comments"][0])
        self.assertIn("Owner: unassigned (see #233)", issue["comments"][0])
        self.assertEqual(self.github()["prs"], [])
        self.assertEqual(self.remote_branch(), "")

    def test_setup_failure_without_summary_is_reported(self):
        empty = self.tmp / "empty"
        empty.mkdir()
        proc = self.publish(log_dir=empty, BUMP_JOB_RESULT="failure")
        self.assertEqual(proc.returncode, 0, proc.stderr)
        [issue] = self.github()["issues"]
        self.assertIn("setup: the bump job (failure)", issue["comments"][0])

    def test_retry_after_failed_pr_creation(self):
        self.bump()
        pushed = git(self.repo, "rev-parse", "HEAD")
        proc = self.publish(FAKE_GH_FAIL_CREATE="1")
        self.assertNotEqual(proc.returncode, 0)
        self.assertEqual(self.remote_branch(), pushed)
        self.assertEqual(self.github()["prs"], [])
        # The next run finds the stranded branch, skips the build and opens the PR.
        git(self.repo, "switch", "-q", "main")
        git(self.repo, "branch", "-q", "-D", "chore/bump-mathlib-v4.36.1")
        lake_calls = len(self.calls("lake"))
        proc, s = self.bump()
        self.assertEqual(s["result"], "branch-exists")
        self.assertEqual(len(self.calls("lake")), lake_calls)
        proc = self.publish()
        self.assertEqual(proc.returncode, 0, proc.stderr)
        [pr] = self.github()["prs"]
        self.assertFalse(pr["isDraft"])
        self.assertEqual(self.remote_branch(), pushed)

    def test_existing_branch_with_pr_is_reused(self):
        self.bump()
        self.publish()
        git(self.repo, "switch", "-q", "main")
        git(self.repo, "branch", "-q", "-D", "chore/bump-mathlib-v4.36.1")
        proc, s = self.bump()
        self.assertEqual(s["result"], "branch-exists")
        proc = self.publish()
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertEqual(len(self.github()["prs"]), 1)
        self.assertIn("Reusing the open PR", proc.stdout)

    def test_human_adaptations_kept_and_conflict_reported(self):
        branch = "chore/bump-mathlib-v4.36.1"
        self.bump(fail="lake-build")
        self.publish()
        # Someone pushes an adaptation to the draft branch...
        work = self.tmp / "human"
        git(self.tmp, "clone", "-q", "-b", branch, str(self.origin), str(work))
        write(work / "lakefile.toml", LAKEFILE.replace('"MathEconLib"]', '"MathEconLib", "X"]'))
        git(work, "-c", "user.name=Ada", "-c", "user.email=ada@example.com",
            "commit", "-qam", "fix: adapt to Mathlib v4.36.1")
        git(work, "push", "-q", "origin", branch)
        adapted = git(work, "rev-parse", "HEAD")
        # ...main changes the same line, and the draft PR is lost.
        git(self.repo, "switch", "-q", "main")
        git(self.repo, "branch", "-q", "-D", branch)
        write(self.repo / "lakefile.toml", LAKEFILE.replace('"MathEconLib"]', '"Other"]'))
        git(self.repo, "commit", "-qam", "main moves on")
        git(self.repo, "push", "-q", "origin", "main")
        db = self.github()
        db["prs"] = []
        (self.state / "github.json").write_text(json.dumps(db))
        # A rerun keeps the branch, reopens a draft PR and reports the conflict.
        proc, s = self.bump()
        self.assertEqual(s["result"], "branch-exists")
        proc = self.publish()
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertEqual(self.remote_branch(), adapted)
        [pr] = self.github()["prs"]
        self.assertTrue(pr["isDraft"])
        [issue] = self.github()["issues"]
        self.assertIn("conflicts with `main` in: lakefile.toml", issue["comments"][-1])

    def test_publication_never_overwrites_an_existing_branch(self):
        self.bump()
        git(self.repo, "push", "-q", "origin", "main:refs/heads/chore/bump-mathlib-v4.36.1")
        before = self.remote_branch()
        proc = self.publish()
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertEqual(self.remote_branch(), before)
        self.assertNotIn("Pushed", proc.stdout)


if __name__ == "__main__":
    unittest.main()
