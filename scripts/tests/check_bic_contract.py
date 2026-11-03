#!/usr/bin/env python3
"""Prove the BIC contract pin rejects three independently compilable weakenings.

Run after `lake build` from a Git checkout. Each experiment uses a disposable
source/build copy and shares only the already-built, pinned dependency cache.
The source checkout and its build products are never modified.
"""

import json
from pathlib import Path
import shutil
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]
CORE = Path("MathEconLib/Mechanism/Core/BayesianIC.lean")
TARGET = "MathEconLibTest.Mechanism.BayesianICContract"


def run(cwd, target):
    return subprocess.run(["lake", "--no-ansi", "build", target], cwd=cwd,
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)


def main():
    source = (ROOT / CORE).read_text()
    start = source.index("/-- Quasilinear BIC is exactly")
    end = source.index("/-- Pointwise quasilinear BIC on the full", start)
    original = source[start:end]
    signature = "theorem isBICOn_iff [IsProbabilityMeasure μ] (D : ∀ i, Set (T i))"
    assert original.count(signature) == 1
    variants = {
        "tautological_alias": signature + " :\n"
        "    IsBICOn E M μ B D ↔ IsBICOn E M μ B D := Iff.rfl\n\n",
        "inequality_without_integrability": signature + " :\n"
        "    IsBICOn E M μ B D →\n"
        "      ∀ i, ∀ s ∈ D i, ∀ r ∈ D i,\n"
        "        interimUtility E M μ B i s r ≤ interimUtility E M μ B i s s :=\n"
        "  fun h ↦ h.bic\n\n",
        "unneeded_constant_belief_guard": original.replace(signature, signature + "\n"
        "    (_h : ∀ i (s r : T i), B.opponents i s = B.opponents i r)"),
    }
    tracked = subprocess.check_output(["git", "ls-files", "-z"], cwd=ROOT).split(b"\0")
    assert (ROOT / ".lake/build").is_dir(), "Run lake build first"
    assert (ROOT / ".lake/packages").is_dir(), "Pinned dependencies are required"
    results = []
    with tempfile.TemporaryDirectory(prefix="bic-contract-") as tmp:
        checkout = Path(tmp)
        for raw in tracked:
            if not raw:
                continue
            relative = Path(raw.decode())
            if relative.suffix != ".lean" and relative.name not in {
                    "lakefile.toml", "lake-manifest.json", "lean-toolchain"}:
                continue
            target = checkout / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / relative, target)
        (checkout / ".lake").mkdir()
        (checkout / ".lake/packages").symlink_to((ROOT / ".lake/packages").resolve())
        shutil.copytree(ROOT / ".lake/build", checkout / ".lake/build")
        baseline = run(checkout, TARGET)
        assert baseline.returncode == 0, baseline.stdout
        results.append({"case": "unchanged_positive_control", "accepted": True})
        for name, replacement in variants.items():
            (checkout / CORE).write_text(source[:start] + replacement + source[end:])
            core = run(checkout, "MathEconLib.Mechanism.Core.BayesianIC")
            assert core.returncode == 0, (name, "mutant itself did not compile", core.stdout)
            contract = run(checkout, TARGET)
            assert contract.returncode != 0, (name, "contract incorrectly accepted mutation")
            assert "BayesianICContract.lean:" in contract.stdout, (name, contract.stdout)
            assert "Type mismatch" in contract.stdout or "type mismatch" in contract.stdout, (
                name, contract.stdout)
            results.append({"case": name, "core_compiles": True, "pin_rejects": True})
    assert (ROOT / CORE).read_text() == source
    print(json.dumps({"result": "BIC_CONTRACT_MUTATIONS_PASSED", "checks": results}, indent=2))


if __name__ == "__main__":
    main()
