#!/usr/bin/env python3
"""Check local links, frozen source line references and the preserved proof index."""

import ast
import json
from pathlib import Path
import re
import subprocess

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[2]
REV = "1d9f8cc233cdaeee0364b51befb84feea657a4da"
PREFIX = "https://github.com/matheconlib/matheconlib/blob/" + REV + "/"


def main():
    local_links = source_links = 0
    for path in sorted(BASE.rglob("*")):
        if not path.is_file():
            continue
        text = path.read_text()
        for marker in ["/"+"Users/", "/"+"private/tmp/", "."+"unlazy/"]:
            assert marker not in text, (path, "nonportable path", marker)
        if path.suffix == ".py":
            ast.parse(text, filename=str(path))
        if path.suffix != ".md":
            continue
        prose = re.sub(r"`[^`]*`", "", text)
        for raw in re.findall(r"\]\(([^)]+)\)", prose):
            if raw.startswith(PREFIX):
                target = raw[len(PREFIX):]
                filename, _, anchor = target.partition("#")
                source = subprocess.check_output(["git", "show", REV+":"+filename],
                                                  cwd=ROOT, text=True)
                if anchor:
                    match = re.fullmatch(r"L(\d+)(?:-L(\d+))?", anchor)
                    assert match and 1 <= int(match[1]) <= len(source.splitlines()), raw
                    if match[2]:
                        assert int(match[1]) <= int(match[2]) <= len(source.splitlines()), raw
                source_links += 1
            elif not raw.startswith(("https://", "http://", "mailto:", "#")):
                target = raw.split("#")[0]
                assert not Path(target).is_absolute(), (path, raw)
                assert (path.parent / target).exists(), (path.relative_to(ROOT), raw)
                local_links += 1
    lean = (ROOT / "MathEconLibTest/Audit/SemanticCounterexamples.lean").read_text()
    names = re.findall(r"^theorem (\w+)", lean, re.M)
    printed = re.findall(r"^#print axioms MathEconLibTest.SemanticAudit\.(\w+)",
                         (BASE / "AxiomChecks.lean").read_text(), re.M)
    assert len(names) == 12 and names == printed, (names, printed)
    assert not re.search(r"\b(sorry|admit|native_decide)\b", lean)
    print(json.dumps({"result": "SEMANTIC_AUDIT_RECORD_PASSED", "local_links": local_links,
                      "audited_source_links": source_links, "supporting_theorems": len(names)},
                     indent=2))


if __name__ == "__main__":
    main()
