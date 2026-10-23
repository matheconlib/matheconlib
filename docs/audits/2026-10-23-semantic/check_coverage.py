#!/usr/bin/env python3
"""Verify frozen source coverage; this is bookkeeping, not a semantic proof."""

from copy import deepcopy
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[2]
REV = "1d9f8cc233cdaeee0364b51befb84feea657a4da"
RX = re.compile(r"^\s*(?:@\[.*?\]\s*)*(?:(?:noncomputable|public|private|protected|unsafe|partial)\s+)*(def|abbrev|structure|class|inductive)\s+")


def strip_comments(text):
    result = []
    index = depth = 0
    string = False
    while index < len(text):
        char, pair = text[index], text[index:index+2]
        if depth:
            if pair in {"/-", "-/"}:
                depth += 1 if pair == "/-" else -1
                result.extend("  ")
                index += 2
                continue
            result.append("\n" if char == "\n" else " ")
        elif string:
            if char == "\\" and index+1 < len(text):
                result.extend("  ")
                index += 2
                continue
            if char == '"':
                string = False
            result.append("\n" if char == "\n" else " ")
        elif pair == "/-":
            depth = 1
            result.extend("  ")
            index += 2
            continue
        elif pair == "--":
            end = text.find("\n", index)
            end = len(text) if end < 0 else end
            result.extend(" " * (end-index))
            index = end
            continue
        elif char == '"':
            string = True
            result.append(" ")
        else:
            result.append(char)
        index += 1
    assert not depth and not string
    return "".join(result)


def verify(inventory, fingerprints):
    scopes = json.loads((BASE / "scopes.json").read_text())
    notes = {key: "\n".join(p.read_text() for p in (BASE / "areas" / key).rglob("*.md"))
             for key in scopes}
    paths = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", REV,
                                     "MathEconLib"], cwd=ROOT, text=True).splitlines()
    rows, snapshots = [], []
    for path in paths:
        if not path.endswith(".lean"):
            continue
        data = subprocess.check_output(["git", "show", REV+":"+path], cwd=ROOT)
        areas = [key for key, prefixes in scopes.items()
                 if any(path.startswith(prefix) for prefix in prefixes)]
        assert len(areas) <= 1, path
        lines = data.decode().splitlines()
        count = 0
        for number, line in enumerate(strip_comments(data.decode()).splitlines(), 1):
            if not RX.match(line):
                continue
            assert len(areas) == 1, (path, number)
            row = {"file": path, "line": number,
                   "declaration": lines[number-1].strip(), "area": areas[0]}
            name = re.search(r"\b(?:def|abbrev|structure|class|inductive)\s+(\S+)",
                             row["declaration"])[1]
            assert name in notes[areas[0]], (path, number, name)
            rows.append(row)
            count += 1
        snapshots.append({"file": path, "area": areas[0] if areas else "import-only",
                          "definitions": count, "sha256": hashlib.sha256(data).hexdigest()})
    keyed = lambda values: {(x["file"], x["line"]): x for x in values}
    assert len(rows) == len(inventory) and keyed(rows) == keyed(inventory), "Inventory differs"
    assert sorted(snapshots, key=lambda x: x["file"]) == sorted(
        fingerprints, key=lambda x: x["file"]), "Source fingerprints differ"
    return {"result": "SEMANTIC_AUDIT_COVERAGE_PASSED", "revision": REV,
            "source_modules": len(snapshots), "definition_like_declarations": len(rows),
            "areas": {key: sum(x["area"] == key for x in rows) for key in scopes},
            "limitation": "Source identities and coverage bookkeeping, not semantic truth"}


def main():
    inventory = json.loads((BASE / "inventory.json").read_text())
    fingerprints = json.loads((BASE / "source-snapshot.json").read_text())
    result = verify(inventory, fingerprints)
    if "--self-test" in sys.argv:
        bad_hash = deepcopy(fingerprints)
        bad_hash[0]["sha256"] = "0" * 64
        for name, rows, hashes in [("missing declaration", inventory[:-1], fingerprints),
                                   ("changed fingerprint", inventory, bad_hash)]:
            try:
                verify(rows, hashes)
            except AssertionError:
                continue
            raise AssertionError("Verifier accepted " + name)
        result["negative_controls_rejected"] = 2
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
