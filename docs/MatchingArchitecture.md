# Choice and matching architecture

The public roots are `MathEconLib.Choice` and `MathEconLib.Matching`.
Both are exported by `MathEconLib`. Independent clients can import only
choice theory; its compile-time client check rejects a transitive dependency
on matching.

## Layers

| Layer | Responsibility |
| --- | --- |
| `MathEconLib.ForMathlib.Data` and `.Order` submodules | Generic graph, fiber-counting, fixed-point and iteration mathematics |
| `MathEconLib.Choice` | Abstract choices, optional conditions, preference-induced choice, mapping, hulls, repairs and completion |
| `MathEconLib.Matching.Contracts` submodules | Market data, stability, order, counting and generalized iteration |
| `MathEconLib.Matching.Classical` submodules | Marriage translation, classical algorithms and executable refinement |
| `MathEconLibTest.Choice` and `.Matching` | Counterexamples, dependency checks and public API clients |

The `Contracts` and `Classical` entries denote module families, not separate
umbrella files. Generic support preserves natural Mathlib declaration
namespaces. Economic declarations use `MathEconLib.Choice` or
`MathEconLib.Matching`.

## Choice interfaces

`Choice.Basic` contains the choice-function structure, pointwise inclusion
order and rejection primitives. The seven optional conditions and their
general relationships live in `Choice.Conditions.Individual`. Import this
module when using consistency, substitutability, the law of aggregate demand,
unit demand, finite-valuedness, path independence or Chernoff's condition.
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

## Staged module organization

The first stage separates `Choice.Basic` from
`Choice.Conditions.Individual` and corrects scope descriptions. The following
stages reorganize existing declarations without changing their mathematical
assumptions. The destinations below are the agreed plan, not claims that the
later moves have already occurred.

| Stage | Destination | Contents |
| --- | --- | --- |
| 2 | `Choice.Conditions.WithPartners.Basic` | Freshness, unilateral/bilateral substitutability, completion, substitutable completability, and consistent completion definitions |
| 2 | `Choice.Conditions.WithPartners.Relationships` | Contraction, substitute-hull characterizations and implications between conditions |
| 2 | `Choice.Conditions.WithPartners.Preferences` | Completion results for preference-induced choices |
| 2 | `Choice.Induced.FeasibleBundles` | Preferences over bundles with at most one alternative per partner |
| 3 | `Matching.Classical.Marriage.Preferences` | Market preference data, acceptability, induced choice functions and finite maximization |
| 3 | `Matching.Classical.Marriage.Basic` | Matching, individual rationality, blocking, stability and optimality specifications |
| 3 | `Matching.Classical.Marriage.ToContracts` | Embedding the marriage model into contracts, graph/reconstruction and the preference dictionary |
| 3 | `Matching.Classical.Marriage.Existence` | The actual stable-matching existence theorem |
| 3 | `Matching.Contracts.FixedPointConvergence` and `Matching.Classical.Marriage.FixedPointConvergence` | General finite convergence and its marriage specialization |
| 4 | Marriage algorithm modules and public names | Put marriage-specific algorithms and stable order in the marriage folder; make operation names and specialization names consistent |

Both condition families concern one choice function. `Individual` needs only
its choices and menus; `WithPartners` additionally uses a map assigning each
alternative to a partner. The latter name does not introduce a new market
structure. Its `Basic` module includes the completion definitions, so readers
can find the definitions before the implication theorems in `Relationships`.

Marriage preferences and their induced choices belong together. The embedding
into the contracts model belongs in `ToContracts`, with the explicit constructor
name `toContractsMarket`; this avoids suggesting a newly induced choice
correspondence. `Existence` should hold the existence theorem, while
`FixedPointConvergence` describes the content currently in `GeneralizedDA`.

Use `map` for the choice-function operation along an embedding, and reserve
“transport” for transferring structure along an equivalence. A specialization
should retain its general operation's name or expose an explicit bridge lemma.
Public-name cleanup also includes `ofOptionLinearOrder` for the optional-partner
constructor, `galeShapleyRoundBound` for the uniform round bound, and
`DeferredAcceptanceComputable` for the executable refinement. None of these
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
`MarriageMarket.local_toMarket` proves locality directly for arbitrary partner
types, independently of finiteness or global IRC.

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
