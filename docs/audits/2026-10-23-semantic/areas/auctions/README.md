> Historical concept assessment at the audited revision. The [publication and proof-scope record](../../README.md) and [repair/migration table](../../MIGRATION.md) distinguish confirmed findings from candidates and current repairs.

# Auction audit coverage index

Read-only source revision: `1d9f8cc233cdaeee0364b51befb84feea657a4da`.

All **28** definition-like declarations assigned to `auctions` in [`inventory.json`](../../inventory.json) are covered, with their accompanying results and interpretation dependencies:

| Files | Inventoried definitions | Coverage note |
| --- | ---: | --- |
| `Auction/Basic.lean`, `Auction/Typeclasses.lean` | 23 | [core.md](core.md) |
| `Auction/ValueDistribution.lean`, `Auction/SymmetricIPV.lean` | 4 | [probability.md](probability.md) |
| `Auction/StrictMonotonicity.lean` | 1 | [revenue.md](revenue.md) |
| `Auction/IdenticalTypes.lean`, `Auction/RevenueEquivalence.lean` | 0; results also audited | [revenue.md](revenue.md) |

Substantive candidates for root independent verification: C1 (unconditional versus conditional interim quantities; BIC and IR fail in both directions), C2 (expected revenue differs from actual revenue), and C3 (atomlessness tests only bidder zero). These are described with exact source locations, explicit witnesses, both directions, and corrections in `core.md`.

The standalone `HasPosDensity` mixture witness is retained in `revenue.md` as a local-versus-global contract ambiguity; it does not contradict its public theorem uses, which add bounded support. No other local semantic defect was found in the scoped probability or revenue modules. Totalized integrals, common strategies, declared endpoints, smooth bounded IPV, and strict-highest-bid tie loss are identified as explicit restrictions.

Reproduce exact arithmetic from the repository root:

```sh
python3 docs/audits/2026-10-23-semantic/areas/auctions/correlation_verify.py
python3 docs/audits/2026-10-23-semantic/areas/auctions/revenue_check.py
```

The area notes record four passes: declaration inventory, concept/equivalence analysis, hostile witness search, and verification/rejected-alarm review. Rational scripts verify only the encoded exact identities; universal claims are justified analytically in the notes. No fresh source compilation is claimed.
