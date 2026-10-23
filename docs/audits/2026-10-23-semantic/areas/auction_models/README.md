> Historical concept assessment at the audited revision. The [publication and proof-scope record](../../README.md) and [repair/migration table](../../MIGRATION.md) distinguish confirmed findings from candidates and current repairs.

# Auction models audit: coverage and findings

Source revision: `1d9f8cc233cdaeee0364b51befb84feea657a4da`.
All 12 scoped modules were read. The final comment-aware inventory contains
48 definition-like declarations: 35 in AllPurchase and 13 in Affiliation.
The former inventory's `Affiliation/Basic.lean:162` entry was a docstring
fragment, not a declaration, and is excluded from the final count.

| Source family | Detailed concept coverage | Findings and qualifications |
| --- | --- | --- |
| `Auction/AllPurchase/{Basic,LinearScarcity,ExplicitSolutions,UniformDistribution,RevenueDecomposition,WelfareDecomposition,OptimalPricing}.lean` | [All-purchase audit](allpurchase.md), every one of the 35 declarations; theorem-only uniform module included | AP-C1 is the correlated-interim defect inherited from the auction core; consolidate with that root finding. No other verified substantive defect. Stationary Cournot quantities, unconstrained quadratic optima, supplied moment expressions, and necessary strategy formulas are explicitly scoped. |
| `Auction/Affiliation/{Basic,LogSupermodular,FiniteCondExp,MonotoneCondExp,WinnersCurse}.lean` | [Affiliation audit](affiliation.md), every one of the 13 declarations; theorem-only log module included | AFF-1: global valuation restrictions exclude standard bounded-support private values, and global private-value classification can depend on off-support extensions. AFF-2: joint-density packaging admits zero mass. AFF-3: pointwise signal predicates reject independent/affiliated laws after null-set density modifications. Algebraic predicates and finite weighted-average theorems remain correct within their declared scopes. |

Every candidate has an explicit witness, exact source lines, both semantic
directions, a correction, analytic verification, and independent review in the
linked notes. Root-level independent verification and final triage are separate
from this area's completion gates. This area makes no project-compilation claim.

Reproducible evidence:

- `evidence/check_allpurchase.py` and `evidence/allpurchase-results.json`:
  exact rational two-state correlated counterexample and rejected scope probes.
- `affiliation-evidence/check_finite.py` and
  `affiliation-evidence/check_finite.output.json`: exact density-value witnesses
  and 5,760 finite conditional-average comparisons. The continuous normalization
  and null-set arguments are analytic and are not inferred from those grids.
- `evidence/check_coverage.py` and `coverage.json`: final inventory reconciliation,
  naming every inventoried declaration and its detailed note. This check verifies
  coverage presence only; semantic assessments remain manually reviewed.

Four passes are recorded in both detailed notes: complete source inventory,
domain-expert concept map, adversarial false-positive/false-negative search with
explicit witnesses, and independent review plus final reconciliation. The final
pass reran both exact computation scripts and checked all 48 source locations.
