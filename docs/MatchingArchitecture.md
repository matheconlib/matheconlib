# Choice and matching architecture

The public roots are `MathEconLib.Choice` and `MathEconLib.Matching`.
Both are exported by `MathEconLib`. Independent clients can import only
choice theory; its compile-time client check rejects a transitive dependency
on the matching-market layer (`MathEconLib.Matching`).

## Layers

| Layer | Responsibility |
| --- | --- |
| `MathEconLib.ForMathlib.Data` and `.Order` submodules | Generic graph, fiber-counting, fixed-point and iteration mathematics |
| `MathEconLib.Choice` | Abstract choices, optional conditions, preference-induced choice, mapping, hulls, repairs and completion |
| `MathEconLib.Matching.Contracts` submodules | Market data, stability, order, counting, fixed-point convergence and many-to-one completion reduction |
| `MathEconLib.Matching.Classical` submodules | Marriage preferences, contracts embedding, proposal algorithms and executable refinement |
| `MathEconLibTest.Choice` and `.Matching` | Counterexamples, dependency checks and public API clients |

The `Contracts` and `Classical` entries denote module families, not separate
umbrella files. Generic support preserves natural Mathlib declaration
namespaces. Economic declarations use `MathEconLib.Choice` or
`MathEconLib.Matching`.

## Choice interfaces

`Choice.Basic` contains the choice-function structure, pointwise inclusion
order and rejection primitives. Optional conditions and their relationships live in `Choice.Conditions`.
Topic sections cover consistency, substitutability, the law of aggregate demand,
unit demand, finite-valuedness, path independence and Chernoff's condition.
Matching terminology is explained beside the canonical definitions: for example,
irrelevance of rejected alternatives becomes irrelevance of rejected contracts
when the alternatives are contracts.
Canonical declaration names are unchanged; importing the public `Choice` root
exposes the complete development. The unused historical completion namespace
has been removed; its replacement map is recorded in
[PR103ReviewChanges.md](PR103ReviewChanges.md).

This development was built with reference to matching with contracts, but
these definitions and results apply to general choice functions. Matching
markets and preference orders are additional structures, not part of the
definition of a choice function. The conditions involving a map from
alternatives to partners are a separate extension; even those need no market.

`ChoiceFunction.substituteHullClosure` packages the existing explicit hull as
a closure operator on choice functions ordered by pointwise inclusion. Its
closed elements are exactly the substitutable rules. IRC preservation and
completion remain separate economic theorems.

`ChoiceFunction.mapOrderEmbedding` packages mapping along an embedding.
The existing pointwise map and its economic property-preservation lemmas
remain public.

`ChoiceFunction.optionMenu` and `bestOption` supply the common finite selector.
The marriage-level menu and best-partner names wrap this interface. Structural
choice on arbitrary sets remains independent of finite enumeration. The new
`IsGreatest` interfaces include feasibility and use the explicitly supplied
preference order. Cardinal utilities are not needed. A menu without a greatest
represented feasible bundle retains the existing empty fallback.

## Module organization

There are ten substantive modules beneath `Choice/`, exported by the public
`MathEconLib.Choice` root. General results are in the parent folder. The
`Matching` subfolder holds constructions and conditions that additionally use
a map from alternatives to matching partners; it does not require a market.

| Module under `Choice` | Contents |
| --- | --- |
| `Basic` | Choice functions, inclusion and rejection |
| `Conditions` | General conditions and their relationships, organized by topic sections |
| `Map` | Mapping choice functions and preservation results |
| `Induced` | General preference-induced choice |
| `FiniteOption` | Finite option selection |
| `SubstituteHull` | Hull construction, closure and IRC properties, accumulating repairs, terminal endpoints and finite convergence |
| `Matching.WeakSubstitutability` | Freshness and unilateral/bilateral substitutability |
| `Matching.Completion` | Completion, substitutable completability, the joint IRC-completion condition and elementary facts |
| `Matching.Relationships` | Contraction, hull characterizations and completion implications |
| `Matching.Preferences` | Feasible-bundle constructors and preference-induced completion results |

The shared predicates are defined once in `Conditions`; matching vocabulary
does not introduce parallel import-only modules. General preference-induced
choice remains independent of the matching-specific extension. The matching
folder's declarations still live in `MathEconLib.Choice.ChoiceFunction`, and
choice theory never imports the market layer `MathEconLib.Matching`.

`Completion` includes the definitions of substitutable completability.
`Relationships` connects weak substitutability, completion and the hull.
Bare substitutable completability and having one completion that satisfies
both substitutability and IRC remain separate predicates. `Preferences`
combines the feasible-bundle representation with its completion corollaries.

The five preference-completion corollaries produce choice-function completions
that can be supplied to the many-to-one market reduction in
`Matching.Contracts.Completion`. Unilateral substitutability remains a
hypothesis for the bundle results; finite preference maximization supplies IRC.
Specific applications such as cadet–branch matching remain on the
[#38 roadmap](https://github.com/matheconlib/matheconlib/issues/38).

`SubstituteHull` develops the construction and its repair characterization in
one file. Hull and terminal-endpoint results allow arbitrary alternative types;
existence and termination of strict repair sequences require a finite type.
The section headings separate these scopes without introducing another module.

| Matching-market module | Contents |
| --- | --- |
| `Matching.Contracts.ManyToOne` | Seller unit demand, buyer counterparty feasibility, outcome feasibility and construction from seller preferences |
| `Matching.Contracts.Completion` | Completed markets, stability transfer, stable existence and unilateral-substitutes corollaries |
| `Matching.Classical.Marriage.Preferences` | Market preference data, relabeling, acceptability, induced choice functions and finite maximization |
| `Matching.Classical.Marriage.RankPreferences` | Deterministic finite rankings, the existing preference adapter, side exchange and ordinal-rank statistics |
| `Matching.Classical.Marriage.Basic` | Matching, individual rationality, blocking, stability and optimality specifications |
| `Matching.Classical.Marriage.ToContracts` | Embedding the marriage model into contracts, graph/reconstruction and the preference dictionary |
| `Matching.Classical.Marriage.Existence` | The stable-matching existence theorem |
| `Matching.Contracts.FixedPointConvergence` and `Matching.Classical.Marriage.FixedPointConvergence` | General finite convergence and its marriage specialization |
| `Matching.Classical.Marriage.DeferredAcceptance`, `.DeferredAcceptanceFixedPoints`, `.DeferredAcceptanceComputable` | Proposal algorithm, fixed-point correctness route and executable refinement |
| `Matching.Classical.Marriage.RankPreferencesDA` | Deterministic short-side DA completeness and rank optimality, without probability |
| `Matching.Classical.Marriage.RandomPreferences` | Arbitrary joint profile laws, explicit-law expectations and independent individual-law specialization |
| `Matching.Classical.Marriage.RandomPreferencesUniform` | Independent uniform rankings, their product law, marginals and finite expectation formula |

Marriage preferences and their induced choices belong together. The embedding
into the contracts model lives in `ToContracts`, with the explicit constructor
name `toContractsMarket`; this avoids suggesting a newly induced choice
correspondence. `Existence` holds the existence theorem, while `FixedPointConvergence` holds
the iteration results previously in `GeneralizedDA`. The embedding module
depends only on the basic contracts model; existence introduces fixed-point
theory. Marriage `Preferences` and `Basic` remain independent of Contracts.

`RankPreferences` depends on marriage preference data and Mathlib finite orders and averages;
it imports neither probability nor DA. Its two population sizes vary independently. Average
proposer rank includes unmatched agents at the outside-option rank; receiver statistics reuse
the same definitions after side exchange. Weak preference comparisons connect the statistics
to existing matching optimality.

`RankPreferencesDA` combines those rankings with the existing executable proposer DA, keeping
short-side completeness and rank optimality independent of probability. The shared `PEquiv`
cardinality lemma supports completeness under no blocking pairs and the optional
`MarriageMarket.UniversallyAcceptable` condition; balanced stable matchings are a corollary.

`RandomPreferences` accepts any joint `PMF (RankProfile m n)`, including correlated rankings.
Expected average rank takes the law and outcome rule explicitly, with separate population sizes.
`independentProfile` specializes to arbitrary independent individual laws, and
`RandomPreferencesUniform` specializes further to independent uniform rankings. Its product-law
and expectation formulas use the shared lemmas in `ForMathlib.Uniform`.
`RankProfile.equivAgentRanks` identifies profiles with one unrestricted family of rankings across
both populations; the product law gives marginals and Mathlib's `iIndepFun`, including empty and
unequal populations. Discrete measurable structures stay in the probability layer.
`Probability.FinDist` also connects its uniform law to the same PMF and finite-average identity.

Sampling preference relations directly, constructing rankings sequentially, and drawing random
primitives are distinct procedures. Each must produce a strict complete profile, with a specified
tie-breaking rule where needed. Their induced joint laws are the common interface: `PMF.map`
handles discrete sources, or `Measure.map` and `Measure.toPMF` handle general measurable sources.
Comparing procedures requires proving equality of those laws rather than assuming equivalence.

`MarriageMarket.relabel` transports optional-partner orders along population equivalences;
`PEquiv.relabel` composes partial assignments with those equivalences. Identity, composition,
side exchange, and stability preservation hold without finite-population or acceptability
restrictions. `MathEconLibExamples.Matching.NamedMarriage` applies this interface to a stable
DA outcome with named participants. The wrappers compose Mathlib's existing equivalences and
order lifts. This transports outcomes and does not assert correspondence between algorithm
execution states. Reverse rank encodings and stable-outcome counting bridges
remain follow-ups in [#192](https://github.com/matheconlib/matheconlib/issues/192).

The canonical `MathEconLibExamples.Matching.RandomPreferences` example proves the exact `5/4`
proposer DA expectation and explains the two equally likely first-choice cases. Tests import that
example; a correlated law with the same individual uniform marginals gives expectation `3/2`.
Its checked marginals and dependence witness illustrate why the joint law matters. The core
contains the reusable statistics and laws. These benchmarks concern ordinal
positions, not cardinal welfare. Proposal bounds,
asymptotics, and matched-agent imbalance results remain later milestones under
[#166](https://github.com/matheconlib/matheconlib/issues/166). Weak preferences
([#200](https://github.com/matheconlib/matheconlib/issues/200)) and relabeling the full contracts
framework are separate follow-ups.

Use `map` for the choice-function operation along an embedding, and reserve
“transport” for transferring structure along an equivalence. A specialization
should retain its general operation's name or expose an explicit bridge lemma.
Public names use `ofOptionLinearOrder` for the optional-partner constructor,
`galeShapleyRoundBound` for the uniform round bound, and explicit
`deferredAcceptanceOperator`/`deferredAcceptanceOrderHom` names.
`DeferredAcceptanceComputable` contains the executable refinement. None of these
organizational steps removes finiteness assumptions. The many-to-one completion
reduction below is a separate mathematical extension.

## Many-to-one completion reduction

`Matching.Contracts.ManyToOne` specializes the existing `Market` and
`Stable` definitions. Sellers are unit-demand proposers; buyers are accepting
institutions. `SellersUnitDemand`, `BuyersCounterpartyFeasible` and
`ManyToOneFeasible` state separate restrictions. The constructor
`ofSellerPreferences` uses strict orders over each seller's own contracts
and the outside option. Its seller choices are unit demand on arbitrary types;
the IRC theorem assumes finite contracts.

`Matching.Contracts.Completion` constructs `withBuyerCompletions` using
the existing support-preservation theorem. Individual rationality agrees
between the original and completed markets on feasible outcomes.
`stable_of_withBuyerCompletions` transfers every stable completed outcome
to the original market under seller unit demand, original-market IRC, and
substitutability and IRC of the specified buyer completions.
`exists_stable_of_buyerCompletions` obtains a feasible stable outcome
when each buyer has one completion satisfying both conditions.

These results allow arbitrary agent and contract types under set-form IRC.
They require neither pointwise enlargement nor the law of aggregate demand,
and do not assert equality of the two markets' stable sets.
The unilateral-substitutes corollaries additionally assume buyer counterparty
feasibility and finite-valued buyer choices; a finite-contract specialization
is also provided. The public-API regression client
`MathEconLibTest/Matching/Completion.lean` applies the general reduction to
a non-unilaterally-substitutable buyer and transfers a concrete stable outcome.
Completion independence and agreement with cumulative offers remain follow-up
work in [#138](https://github.com/matheconlib/matheconlib/issues/138) and
[#139](https://github.com/matheconlib/matheconlib/issues/139).

## Stability and locality

`Market.FixedPointStates hsub` is the raw Knaster–Tarski lattice. It requires
substitutability but no IRC. Raw state projections, finite convergence and
conditional ambient-lattice comparisons retain that boundary.

`Market.StableOutcomes hsub hcons` exposes the economic interpretation and
requests IRC. It is a reducible abbreviation of the raw carrier, not a distinct
proof-carrying type. In particular, clients should not rely on its extra
parameter to make the raw carrier inaccessible. Named optimal outcomes also
request IRC; their proofs and `stableEquivFixedPoints` supply the actual
stability guarantees.

`Market.Local` expresses absence of menu externalities separately from support.
`Market.Consistent.local` derives it from IRC. The base `Market` remains
support-only, so existing results without IRC retain their scope.
`MarriageMarket.local_toContractsMarket` proves locality directly for arbitrary partner
types, independently of finiteness or global IRC.

## Public-name migration

The associated constructor/operator lemma families follow these same names.
The stage changes identifiers and file locations; it does not strengthen or
weaken their mathematical hypotheses.

| Previous name | Current name |
| --- | --- |
| `ChoiceFunction.ofLinearOrder` | `ChoiceFunction.ofOptionLinearOrder` |
| `MarriageMarket.toMarket` | `MarriageMarket.toContractsMarket` |
| `Market.daFun` | `Market.deferredAcceptanceOperator` |
| `Market.daHom` | `Market.deferredAcceptanceOrderHom` |
| `MarriageMarket.gsStoppingTime` | `MarriageMarket.galeShapleyRoundBound` |
| `MarriageMarket.gs_stoppingTime_terminal` | `MarriageMarket.galeShapleyRoundBound_terminal` |
| `MarriageMarket.StableMatching.contractsEquiv` | `MarriageMarket.StableMatching.fixedPointEquiv` |
| `MarriageMarket.StableMatching.contractsOrderIso` | `MarriageMarket.StableMatching.fixedPointOrderIso` |

The proposal-algorithm correctness lemmas use `_via_fixedPoints` for the
fixed-point proof route. The separate economic-order translation theorem keeps
`_via_contracts`, which describes that theorem's proof route accurately.
The endpoint aliases `deferredAcceptance` and `womanProposingDeferredAcceptance`
remain documented aliases of the canonical optimal matchings; the actual
proposal algorithms are `galeShapley` and `galeShapleyComputable`.

## Canonical theorem names

| Removed compatibility wrapper | Use instead |
| --- | --- |
| `Market.outcomeOf_daFun_of_stable` | `Market.outcomeOf_stateOf_of_stable` |
| `Market.outcomeOf_stateOf` | `Market.outcomeOf_stateOf_of_stable` |
| `Market.eq_of_isFixedPt_of_outcomeOf_eq` | `Market.eq_of_isFixedPt_of_outcomeOf_eq_state` |

The direct classical correctness proof, contracts-derived proof and executable
refinement remain public: they relate different mathematical objects.

## Verification

With Lean 4.28.0 and the locked dependencies available, run the repository's
normal import checks and `lake build`. The default targets already include the
production root, API pins and test root. The namespace guard therefore covers
the new production modules; both counterexample modules and the new client
checks are compiled through `MathEconLibTest`.

Preserve the explicit `Fintype.card (M × W)` rejection-update bound. Generic
eventual stationarity does not replace this executable step budget. The
arbitrary-fuel function may stop before stationarity.

The existing pull-request CI performs the compiled checks. Its result must be
associated with the actual checked-out commit; source inspection and structural
checks alone are not a successful Lean build.

The edition-specific reference map is in [MatchingReferences.md](MatchingReferences.md).
The review-to-commit record is in [PR103ReviewChanges.md](PR103ReviewChanges.md).
