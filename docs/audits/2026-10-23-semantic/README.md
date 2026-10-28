# Semantic audit preservation record

This directory preserves the audit of revision
[`1d9f8cc233cdaeee0364b51befb84feea657a4da`](https://github.com/matheconlib/matheconlib/commit/1d9f8cc233cdaeee0364b51befb84feea657a4da).
It follows [design umbrella #211](https://github.com/matheconlib/matheconlib/issues/211)
and [evidence issue #218](https://github.com/matheconlib/matheconlib/issues/218).

Start with [the six confirmed findings](REPORT.md) and [the repair/migration table](MIGRATION.md).
The area notes preserve the declaration-to-concept assessments, including rejected alarms and
intentional restrictions. Those notes describe the audited revision; audit-time candidates are
not additional confirmed findings or current design decisions.

## Coverage and evidence

- [inventory.json](inventory.json): all 430 definition-like declarations, with source file,
  one-based line and assigned area.
- [source-snapshot.json](source-snapshot.json): fingerprints and coverage for all 128 library
  modules, including eight import-only modules.
- [scopes.json](scopes.json): the ten disjoint area assignments.
- [REPORT.md](REPORT.md): intended concepts, assumptions, both implication directions,
  minimal witnesses, exact source locations and proposed corrections for F1–F6.
- [verification/auction-candidates.md](verification/auction-candidates.md): independent
  analytic reconstruction of the six confirmed finding groups.
- [SemanticCounterexamples.lean](../../../MathEconLibTest/Audit/SemanticCounterexamples.lean):
  the twelve original supporting lemmas, preserved once in the canonical test tree.
- [AxiomChecks.lean](../../../MathEconLibTest/Audit/AxiomChecks.lean): their axiom-report driver,
  moved into the test tree so the required all-source proof-integrity check can build it.
- [verification.json](verification.json): original proof limits and initial publication checks.

The original independent reviews were separate automated workstreams. Neither their agreement
nor this publication supplies the required maintainer review. The original source compilation
covered the 128 library modules and root umbrella; it was not a full default project build.
The publication branch's build is a separate check.

The twelve Lean statements certify an actual zero-density signal environment and its
IPV/affiliation/mass properties, the global strict-positive-value obstruction, and the decisive
real arithmetic. They do not certify every complete probabilistic countermodel. In particular,
the uniform/constant atomlessness witness and the density-version/off-support arguments retain
their explicit analytic proofs. The complete repaired auction regressions are in PR #210;
[MIGRATION.md](MIGRATION.md) links their exact published source.

## Reproduce

Use the dependencies pinned by the evidence checkout. The initial publication commit
[`b12f9a20`](https://github.com/matheconlib/matheconlib/commit/b12f9a20e3c900d93ca5d7cfc31f038166a93b55)
used Lean/Mathlib 4.28.0; the refreshed branch uses the project's 4.35.0 pins.
The original audited revision, fingerprints and initial verification record remain historical;
fresh compatibility checks are recorded on PR #232. From the repository root:

```sh
lake exe cache get
python3 docs/audits/2026-10-23-semantic/check_coverage.py --self-test
python3 docs/audits/2026-10-23-semantic/check_record.py
python3 docs/audits/2026-10-23-semantic/verification/check_auction_candidates.py
python3 docs/audits/2026-10-23-semantic/areas/auctions/correlation_verify.py
python3 docs/audits/2026-10-23-semantic/areas/auction_models/evidence/check_allpurchase.py
python3 docs/audits/2026-10-23-semantic/areas/auction_models/affiliation-evidence/check_finite.py
bash scripts/update-imports.sh --check
bash scripts/check-headers.sh
lake --no-ansi build
python3 scripts/check-proof-integrity.py
lake env lean MathEconLibTest/Audit/AxiomChecks.lean
```

The coverage verifier reads the frozen audited Git objects rather than silently substituting
a later checkout. Its self-test confirms that a missing declaration or changed fingerprint
fails. The record checker verifies portable local links, immutable source line references,
the twelve preserved theorem names and the absence of workstation paths.

Exact Python calculations use rational arithmetic and no third-party dependencies. Their finite
enumerations certify only the encoded cases. Continuum incentive claims use the displayed real
identities and universal Lean statements; a bid grid is not a proof of BIC.

Future signal repairs may deliberately invalidate historical characterization lemmas. Preserve
the immutable evidence commit and migrate the live regression to the repaired contract, rather
than weakening a repair to retain an obsolete statement.

## Closure

Publishing this record completes preservation, not all six repairs. F1's all-purchase adapter,
F3–F6, later migration entries and final reviewed/merged SHAs remain open under their own issues.
The verification record distinguishes implemented, reviewed and merged status.
