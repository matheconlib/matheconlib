> Historical concept assessment at the audited revision. The [publication and proof-scope record](../../README.md) and [repair/migration table](../../MIGRATION.md) distinguish confirmed findings from candidates and current repairs.

# Mechanisms, bidder problems, and single-parameter models

Source revision: `1d9f8cc233cdaeee0364b51befb84feea657a4da`; audit date 2026-10-23.

## Verdict

No substantive semantic false positive or false negative was established in this area. All 51 inventoried definition-like declarations across 19 files were assessed against their documented concepts in both directions. The primitive transfer signs, DSIC quantifiers, participation normalization, restricted action deviations, reduction/revelation domains, envelope constants, and purchase ties are consistent.

This conclusion is confined to the specified models: deterministic mechanisms, quasilinear utility, allocation probabilities in `[0,1]`, single-agent reduced choice data where applicable, and the stated type/report domains. It is not a claim that the library represents every general mechanism or that a definition alone proves equilibrium.

## Coverage ledger

| Subarea | Definitions | Files | Detailed concept map and assessment |
| --- | ---: | ---: | --- |
| Mechanism core and auction specification | 23 | 9 | [core.md](core.md) |
| BidderProblem | 11 | 4 | [bidderproblem.md](bidderproblem.md) |
| SingleParameter | 17 | 6 | [singleparameter.md](singleparameter.md) |
| Total | 51 | 19 | `coverage.json` records every inventory entry. |

The six single-parameter files are `Basic`, `IC`, `EnvelopeIC`, `Payment`, `PostedPrice`, and `Revelation`. The four bidder files are `Basic`, `EnvelopeIC`, `TypeDeviationIC`, and `UniversalIC`. The nine mechanism files are `Core/{Profile,Mechanism,Environment,SolutionConcepts,Comap,Strategic,Bayesian}` and `Auctions/{Allocation,AllPurchase/Spec}`. The theorem-only `SingleParameter/EnvelopeIC` and `SingleParameter/Payment` were reviewed as part of the definitions' analytic interpretation, even though they contribute no inventory declarations.

The inventory initially missed annotated `utilityGame` and `inducedBayesianGame` declarations; both are included in the current inventory and detailed map.

## Scope checks and lower-priority clarifications

1. `HasEnvelopeIC` and `HasTypeDeviationIC` are exactly equivalent after substituting `U(v)=v*q(v)-p(v)`. The “three levels” presentation could state this equivalence. No separating counterexample exists; the one-way implication in the source is true. Locations: `SingleParameter/IC.lean:14-28,55-64`; `BidderProblem/EnvelopeIC.lean:44-49`; `BidderProblem/TypeDeviationIC.lean:14-16,44-48`.
2. `BidderProblem.allPayBid` is the canonical payment with zero utility at the lowest type. With one bidder, `q=1`, types `[1,2]`, nonnegative all-pay bids, and strategy constantly zero, the true equilibrium bid is zero but the canonical function is one. The actual payment identity correctly subtracts `U(1)=1`, yielding zero. Thus the unqualified equilibrium wording deserves a normalization caveat; the formal payment definition and identity are correct. Exact witness, correction, and independent computations appear in [bidderproblem.md](bidderproblem.md). Location: `BidderProblem/TypeDeviationIC.lean:114-120,127-135`.
3. Two allocations `(1,1)` pass coordinate bounds but exceed single-item capacity; ties `(0,0)` allocate no object under the strict rule; all-purchase bids can be negative. Each is an explicit scope choice, not a hidden conceptual error. Exact witnesses, source clauses, and the extra conditions needed for the stronger concepts appear in [core.md](core.md).
4. Type-deviation IC does not rule out profitable unused actions. The explicit subsidy example in [singleparameter.md](singleparameter.md) verifies that universal IC is stronger in that respect and that reduction's report restriction is necessary. The library makes that restriction explicitly.

## Four-pass audit and independent verification

1. **Constructive mapping.** Read all 19 source modules and assign each definition to a standard mathematical/economic concept or an explicit custom specification. Detailed notes contain exact declaration locations and boundary assumptions.
2. **Adversarial search.** Attack both directions using unused deviations, subsidies, singleton/empty type and agent sets, interdependent valuations, truthful versus arbitrary reports, signs of payments/revenue, aggregate feasibility, zero-surplus ties, and lowest-type normalization. Rejected candidates are retained as evidence with their exact witnesses.
3. **Independent verification.** A separate verifier read all nine mechanism modules and independently found no surviving defect. Independent SingleParameter and BidderProblem reviewers expanded both directions of reduced-IC equivalence and the normalization example. The area lead reread their source declarations and independently recomputed the examples from primitive allocation/payment rules. `verify_scope_examples.py` supplies a further exact rational-arithmetic check of the displayed finite calculations; analytic extensions are justified in the notes rather than inferred from samples.
4. **Reconciliation.** Check all 51 inventory locations against current source; check declaration names against the corresponding detailed map; preserve exact file counts and distinguish meaningful limitations from actual failed definitions. Mark gates only once detailed reports and independent checks are complete.

No project-wide build or Lean-kernel verification is claimed. The SingleParameter reverse-IC LeanProbe attempt timed out and supplies no verification evidence. Any separate bidder check outcome is recorded in that note. All mathematical conclusions here are supported by source inspection and explicit exact algebra.
