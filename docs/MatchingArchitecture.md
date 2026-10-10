# Choice and matching architecture

The public roots are `MathEconLib.Choice` and `MathEconLib.Matching`.
Both are exported by `MathEconLib`. Independent clients can import only
choice theory; its compile-time client check rejects a transitive dependency
on matching.

## Layers

| Layer | Responsibility |
| --- | --- |
| `MathEconLib.ForMathlib.Data` and `.Order` submodules | Generic graph, fiber-counting, fixed-point and iteration mathematics |
| `MathEconLib.Choice` | Abstract choices, induced preferences, transport, hulls, repairs and completion |
| `MathEconLib.Matching.Contracts` submodules | Market data, stability, order, counting and generalized iteration |
| `MathEconLib.Matching.Classical` submodules | Marriage translation, classical algorithms and executable refinement |
| `MathEconLibTest.Choice` and `.Matching` | Counterexamples, dependency checks and public API clients |

The `Contracts` and `Classical` entries denote module families, not separate
umbrella files. Generic support preserves natural Mathlib declaration
namespaces. Economic declarations use `MathEconLib.Choice` or
`MathEconLib.Matching`.

## Choice interfaces

`ChoiceFunction.substituteHullClosure` packages the existing explicit hull as
a closure operator on choice functions ordered by pointwise inclusion. Its
closed elements are exactly the substitutable rules. IRC preservation and
completion remain separate economic theorems.

`ChoiceFunction.mapOrderEmbedding` packages transport along an embedding.
The existing pointwise map and its economic property-preservation lemmas
remain public.

`ChoiceFunction.optionMenu` and `bestOption` supply the common finite selector.
The marriage-level menu and best-partner names wrap this interface. Structural
choice on arbitrary sets remains independent of finite enumeration. The new
`IsGreatest` interfaces include feasibility and use the explicitly supplied
preference order. Cardinal utilities are not needed. A menu without a greatest
represented feasible bundle retains the existing empty fallback.

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
