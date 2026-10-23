> Historical concept assessment at the audited revision. The [publication and proof-scope record](../../README.md) and [repair/migration table](../../MIGRATION.md) distinguish confirmed findings from candidates and current repairs.

# Foundations semantic audit index

Source revision: `1d9f8cc233cdaeee0364b51befb84feea657a4da`. Scope: all **23 modules** under `MathEconLib/ForMathlib/` and `MathEconLib/Probability/`, including all **40** inventoried definition-like declarations and the public theorem contracts in helper-only files. Library source files were not changed. The initial inventory omitted `public def IsApproxSelection`; it was audited, reported to the root reviewer, and added to the shared inventory.

**Result:** no substantive false positive or false negative survived review under the stated intended domains and assumptions. The notes distinguish totalization/domain conventions from defects. A minor star-refinement comment promises an output property that the theorem does not expose; its concrete independently checked example and correction are retained in the selection note. It does not invalidate the theorem or downstream arguments.

| Coverage note | Source files covered | Inventory declarations |
| --- | --- | --- |
| [Helpers and finite order iteration](helpers.md) | `ForMathlib/Data/{PartialMatching,SetFiber}`, `ForMathlib/Order/{FixedPointLattice,IterateFixedPoint,IterateFiniteSet}`, `ForMathlib/{FinsetUpdate,Quasiconvex}` | 3 |
| [Selections and analytic measurability](selection.md), with [Scarf/Schauder details](selection-schauder.md) | `ForMathlib/{ApproximateSelection,Kakutani,Schauder}`, `ForMathlib/MeasureTheory/{AnalyticUniformization,AnalyticNullMeasurable,VonNeumannSelection}` | 13 |
| [Measure foundations](measure.md) | `ForMathlib/{AbsolutelyContinuous,IndepFun,MeasureTheory,ProbabilityMeasure,StochasticOrder}` | 5 |
| [Finite probability](finite_prob.md) | `Probability/FinDist/{Basic,ConditionalOn,Expect,Measure,Simplex}` | 19 |

`coverage.json` maps every one of the 40 inventory entries to its exact source line and responsible note. All 40 recorded declaration texts were matched against the actual source lines during final reconciliation. Each note gives the standard mathematical concept, both semantic implications, assumptions, edge cases, exact locations, and the disposition of hostile counterexample attempts.

Verification combines formula-level mathematical review, independent hostile reviewers for finite probability, likelihood-ratio order, Scarf/Schauder and probability-measure helpers, and retained exact bounded computations. The integrator independently read and reran every retained script. The scripts test their displayed finite encodings; no general result is inferred from their finite bounds. No Lean elaboration/build success is claimed: this checkout lacks installed mathlib packages and built project oleans. Existing mathlib source files in a separate local clone were used read-only to inspect primitive definitions.

The four required passes were: full source/inventory review; comparison of each concept in both directions; hostile search over boundary and quantifier cases with exact checks where useful; final evidence, source-location, and convention reconciliation.
