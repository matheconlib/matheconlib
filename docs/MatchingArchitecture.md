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
| `MathEconLib.Matching.Contracts` submodules | Market data, stability, order, counting and fixed-point convergence |
| `MathEconLib.Matching.Classical` submodules | Marriage preferences, contracts embedding, proposal algorithms and executable refinement |
| `MathEconLibTest.Choice` and `.Matching` | Counterexamples, dependency checks and public API clients |

The `Contracts` and `Classical` entries denote module families, not separate
umbrella files. Generic support preserves natural Mathlib declaration
namespaces. Economic declarations use `MathEconLib.Choice` or
`MathEconLib.Matching`.

## Choice interfaces

`Choice.Basic` contains the choice-function structure, pointwise inclusion
order and rejection primitives. Optional conditions have canonical definitions in the topic modules under
`Choice.Conditions.General`, with implications between conditions in
`General.Relationships`. The `General` umbrella exposes consistency,
substitutability, the law of aggregate demand, unit demand, finite-valuedness,
path independence and Chernoff's condition.
Existing declaration names are unchanged; importing the public `Choice` root
still exposes them all.

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

`Choice.Conditions.General` and `Choice.Conditions.Matching` are documented
umbrellas. Topic modules let a reader find a condition directly or import just
its definitions and elementary facts. Definitions that make sense for arbitrary
alternatives are maintained once in `General`; their `Matching` entry points
import those same declarations and explain the contracts interpretation.

| Topic under `Choice.Conditions` | Canonical contents |
| --- | --- |
| `General.Substitutability` / `Matching.Substitutability` | Substitutability, Chernoff's condition, and their characterizations |
| `General.IrrelevanceOfRejectedAlternatives` / `Matching.IrrelevanceOfRejectedContracts` | The shared consistency predicate and idempotence |
| `General.LawOfAggregateDemand` / `Matching.LawOfAggregateDemand` | The law of aggregate demand on finite menus and its cardinality lemmas |
| `General.UnitDemand` / `Matching.UnitDemand` | At most one chosen alternative or contract |
| `General.FiniteValued` / `Matching.FiniteValued` | Finite chosen sets, including on infinite menus |
| `General.PathIndependence` / `Matching.PathIndependence` | Path independence and its elementary union lemmas |
| `General.Relationships` | Implications and equivalences between the general conditions |
| `Matching.WeakSubstitutability` | Freshness, unilateral/bilateral substitutability, and the implication chain from substitutability |
| `Matching.Completion` | Completion, substitutable completability, the joint IRC-completion condition, and elementary facts |
| `Matching.Relationships` | Contraction, substitute-hull characterizations, and implications connecting weak substitutability with completion |
| `Matching.Preferences` | Completion results for preference-induced choices |

The general topic modules use only choices and menus. Weak substitutability
and completion additionally use a map assigning each contract to its partner;
no matching market is required. `Matching` here identifies the motivating
interpretation inside choice theory, not a dependency on
`MathEconLib.Matching`. The matching topic entry points do not introduce duplicate
predicates or aliases. Their public declarations still live in
`MathEconLib.Choice.ChoiceFunction`.

`Completion` contains the basic definitions of substitutable completability,
so it is the starting point for that concept. Cross-condition implications
belong in `Relationships`, while preference-based applications belong in
`Preferences`. Bare substitutable completability and having one completion
that satisfies both substitutability and IRC remain separate predicates.

| Other module | Contents |
| --- | --- |
| `Choice.Induced.FeasibleBundles` | Preferences over bundles with at most one alternative per partner |
| `Matching.Classical.Marriage.Preferences` | Market preference data, acceptability, induced choice functions and finite maximization |
| `Matching.Classical.Marriage.Basic` | Matching, individual rationality, blocking, stability and optimality specifications |
| `Matching.Classical.Marriage.ToContracts` | Embedding the marriage model into contracts, graph/reconstruction and the preference dictionary |
| `Matching.Classical.Marriage.Existence` | The stable-matching existence theorem |
| `Matching.Contracts.FixedPointConvergence` and `Matching.Classical.Marriage.FixedPointConvergence` | General finite convergence and its marriage specialization |
| `Matching.Classical.Marriage.DeferredAcceptance`, `.DeferredAcceptanceFixedPoints`, `.DeferredAcceptanceComputable` | Proposal algorithm, fixed-point correctness route and executable refinement |

The topic organization replaces the earlier `Conditions.Individual` and
`Conditions.WithPartners` paths. Imports and documentation follow the new paths;
declaration names, assumptions and proofs are unchanged.

Marriage preferences and their induced choices belong together. The embedding
into the contracts model lives in `ToContracts`, with the explicit constructor
name `toContractsMarket`; this avoids suggesting a newly induced choice
correspondence. `Existence` holds the existence theorem, while `FixedPointConvergence` holds
the iteration results previously in `GeneralizedDA`. The embedding module
depends only on the basic contracts model; existence introduces fixed-point
theory. Marriage `Preferences` and `Basic` remain independent of Contracts.

Use `map` for the choice-function operation along an embedding, and reserve
“transport” for transferring structure along an equivalence. A specialization
should retain its general operation's name or expose an explicit bridge lemma.
Public names use `ofOptionLinearOrder` for the optional-partner constructor,
`galeShapleyRoundBound` for the uniform round bound, and explicit
`deferredAcceptanceOperator`/`deferredAcceptanceOrderHom` names.
`DeferredAcceptanceComputable` contains the executable refinement. None of these
organizational steps removes finiteness assumptions or supplies a new market
existence reduction under weak substitutability.

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
