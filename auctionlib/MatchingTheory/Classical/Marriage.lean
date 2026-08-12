/-
Matching with contracts, classical layer: the marriage market.
-/
import Matching.Contracts.FixedPoint
import Mathlib.Data.PEquiv

/-!
# The classical marriage market (Gale–Shapley 1962)

The **statement layer** for one-to-one stable matching (SPEC D5): classical
definitions in Gale–Shapley's own vocabulary — men `M` and women `W`, with
men proposing — and every proof routed through the contracts framework via
`toMarket`. Nothing here is proved natively except the translation itself.

**Dictionary** (fixed throughout the classical layer):

  men = sellers = proposers,   women = buyers = receivers.

Contracts are pairs `M × W` with `seller := Prod.fst`; consequently
`Market.sellerOptimal` transports to the classical **man-optimal** stable
matching, recovering Gale–Shapley's result that man-proposing deferred
acceptance is optimal for men (and, by the lattice opposition of interests,
pessimal for women). The gender-neutral many-to-one vocabulary
(hospitals/doctors) lives in `Classical/CollegeAdmissions.lean`.

Design (imported from Proposal B, implemented on mathlib primitives):

* A partial matching is a `PEquiv` (`M ≃. W`) — the bundled
  two-`Option`-functions-with-coherence design *is* `PEquiv`, so `symm`,
  `trans` and extensionality come for free.
* Preferences are per-agent **data-level** `LinearOrder (Option partner)`
  with `none` = remaining single, so acceptability is `none < some w` and
  individual rationality is `none ≤ μ m`. No separate acceptability data and
  no ℕ-rank encodings (SPEC D6.2).
* These orders are data, so instance search will not find them; statements
  use the helper relations `mkt.ltM`/`mkt.leM`/`mkt.ltW`/`mkt.leW` (scoped
  notation pending taste testing, SPEC §8 Q4), and proofs may `letI` the
  order.

## Main definitions

* `MarriageMarket M W`; `MarriageMarket.IsBlockingPair`,
  `MarriageMarket.IndividuallyRational`, `MarriageMarket.IsStableMatching`.
* `MarriageMarket.graphOf : (M ≃. W) → Set (M × W)` and
  `MarriageMarket.toMarket : Market W M (M × W)`.

## Main statements

* `isStableMatching_iff_stable_graphOf` — the translation theorem, the only
  genuinely new proof content in this file.
* `exists_stableMatching`, `exists_manOptimal_stableMatching`,
  `isSome_iff_of_stable` (lone wolf) — instances of the contracts theorems.
-/

open Function

universe u v

variable {M : Type u} {W : Type v}

/-- A classical **marriage market**: each man and each woman carries a strict
preference over `Option` partner, with `none` = remaining single. Any linear
order is allowed; the position of `none` encodes which partners are
acceptable. -/
structure MarriageMarket (M : Type u) (W : Type v) where
  /-- Man `m`'s preference over women-or-single. -/
  prefM : M → LinearOrder (Option W)
  /-- Woman `w`'s preference over men-or-single. -/
  prefW : W → LinearOrder (Option M)

namespace MarriageMarket

variable (mkt : MarriageMarket M W)

/-! ### Preference relations as data

`LinearOrder` here is a structure field, not an instance, so `<`/`≤` will not
elaborate against it directly; these helpers are the statement-level API. -/

/-- Strict preference of man `m`. -/
def ltM (m : M) (y z : Option W) : Prop := letI := mkt.prefM m; y < z

/-- Weak preference of man `m`. -/
def leM (m : M) (y z : Option W) : Prop := letI := mkt.prefM m; y ≤ z

/-- Strict preference of woman `w`. -/
def ltW (w : W) (y z : Option M) : Prop := letI := mkt.prefW w; y < z

/-- Weak preference of woman `w`. -/
def leW (w : W) (y z : Option M) : Prop := letI := mkt.prefW w; y ≤ z

-- Candidate scoped notation (SPEC §8 Q4), pending taste testing:
-- scoped notation:50 y " ≺ᵐ[" mkt ", " m "] " z => MarriageMarket.ltM mkt m y z
-- scoped notation:50 y " ≺ʷ[" mkt ", " w "] " z => MarriageMarket.ltW mkt w y z

/-- `w` is acceptable to `m`. -/
def AcceptableM (m : M) (w : W) : Prop := mkt.ltM m none (some w)

/-- `m` is acceptable to `w`. -/
def AcceptableW (w : W) (m : M) : Prop := mkt.ltW w none (some m)

/-! ### Matchings and classical stability

A matching is a `PEquiv`; `μ m : Option W` is `m`'s partner and `μ.symm w`
is `w`'s, with coherence built in. -/

/-- Individual rationality: no agent is matched below their outside option. -/
def IndividuallyRational (μ : M ≃. W) : Prop :=
  (∀ m, mkt.leM m none (μ m)) ∧ ∀ w, mkt.leW w none (μ.symm w)

/-- `(m, w)` is a **blocking pair** for `μ`: each strictly prefers the other
to their current assignment. -/
def IsBlockingPair (μ : M ≃. W) (m : M) (w : W) : Prop :=
  mkt.ltM m (μ m) (some w) ∧ mkt.ltW w (μ.symm w) (some m)

/-- Classical stability of a matching. -/
def IsStableMatching (μ : M ≃. W) : Prop :=
  mkt.IndividuallyRational μ ∧ ∀ m w, ¬ mkt.IsBlockingPair μ m w

/-! ### Translation into the contracts framework

Contracts are man–woman pairs; men sell (propose) and women buy (receive).
Each agent's choice function picks the best acceptable available partner.
The induced-choice constructor and its `UnitDemand` / `Consistent` lemmas
belong in `Matching.Choice.Induced`; stubs here mark the interface.
Finiteness enters only through argmax existence. -/

section ToMarket

variable [Fintype M] [Fintype W]

/-- Man `m`'s induced unit-demand choice on contracts: the best acceptable
available partner under `mkt.prefM m`, if any. Implementation in
`Matching.Choice.Induced`. -/
noncomputable def inducedChoiceM (m : M) : ChoiceFunction (M × W) := by
  sorry

/-- Woman `w`'s induced unit-demand choice on contracts. -/
noncomputable def inducedChoiceW (w : W) : ChoiceFunction (M × W) := by
  sorry

/-- The contracts market induced by a marriage market. Per the dictionary,
women are the buyers `B := W` and men the sellers `S := M`, so the
seller-proposing machinery of `Contracts/FixedPoint.lean` *is* man-proposing
deferred acceptance. -/
noncomputable def toMarket : Market W M (M × W) where
  buyer := Prod.snd
  seller := Prod.fst
  choiceB := mkt.inducedChoiceW
  choiceS := mkt.inducedChoiceM
  buyer_eq_of_mem := by sorry
  seller_eq_of_mem := by sorry

/-- Induced choice satisfies IRC (preference-induced choice always does). -/
theorem consistent_toMarket : mkt.toMarket.Consistent := by
  sorry

/-- Induced choice is substitutable: instance of
`ChoiceFunction.UnitDemand.substitutable`. -/
theorem substitutable_toMarket : mkt.toMarket.Substitutable := by
  sorry

/-- Induced choice satisfies the law of aggregate demand: instance of
`ChoiceFunction.UnitDemand.sizeMonotone`. -/
theorem sizeMonotone_toMarket : mkt.toMarket.SizeMonotone := by
  sorry

/-- The set-of-contracts graph of a matching. -/
def graphOf (μ : M ≃. W) : Set (M × W) := {p | μ p.1 = some p.2}

/-- Individually rational outcomes of the induced (unit-demand) market are
graphs of partial matchings; this packages the passage back. -/
noncomputable def matchingOfStable {A : Set (M × W)}
    (hA : mkt.toMarket.Stable A) : M ≃. W := by
  sorry

/-- **Translation theorem**: classical stability coincides with stability of
the graph in the induced contracts market. The only genuinely new proof
content of the classical layer; everything below instantiates. -/
theorem isStableMatching_iff_stable_graphOf (μ : M ≃. W) :
    mkt.IsStableMatching μ ↔ mkt.toMarket.Stable (mkt.graphOf μ) := by
  sorry

/-! ### Classical corollaries -/

/-- **Gale–Shapley existence**, as an instance of `Market.exists_stable`. -/
theorem exists_stableMatching : ∃ μ : M ≃. W, mkt.IsStableMatching μ := by
  sorry

/-- **Man-optimality**: there is a stable matching simultaneously weakly best
for every man among stable matchings — `Market.sellerOptimal` transported
through the translation, with `SellerChosen` read pointwise via unit demand.
(Its woman-pessimality, the opposition of interests, is a planned companion
statement once the order file lands.) -/
theorem exists_manOptimal_stableMatching :
    ∃ μ : M ≃. W, mkt.IsStableMatching μ ∧
      ∀ ν : M ≃. W, mkt.IsStableMatching ν → ∀ m, mkt.leM m (ν m) (μ m) := by
  sorry

/-- **Lone wolf** (rural hospitals at unit demand): a man matched in one
stable matching is matched in every stable matching. Instance of
`Market.ncard_sellerSide_eq_of_stable`; the women's version follows via
`PEquiv.symm`. -/
theorem isSome_iff_of_stable {μ ν : M ≃. W} (hμ : mkt.IsStableMatching μ)
    (hν : mkt.IsStableMatching ν) (m : M) :
    (μ m).isSome ↔ (ν m).isSome := by
  sorry

end ToMarket

/-! ### Decidability

`LinearOrder` bundles decidable `≤`/`<`, so classical stability over finite
sides is decidable by unfolding; Gale–Shapley's own worked examples then
close by `decide` and double as tests. -/

section Decide

variable [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]

instance : DecidablePred mkt.IsStableMatching := by
  sorry

end Decide

/-! ### TODO

* `Matching.Choice.Induced`: the general argmax constructor and its lemmas.
* `Classical/CollegeAdmissions.lean`: responsive (top-`q`) choice is
  substitutable and size-monotone, in hospital/doctor vocabulary — buys the
  classical many-to-one theory.
* `Classical/GraphBridge.lean`: unit-demand stable outcomes induce
  `SimpleGraph.Subgraph.IsMatching` (bridge only; graphs are never the base).
* `PEquiv` API gaps discovered here (graph view, constructor from an
  injective-on-`some` function) become upstream PRs.
-/

end MarriageMarket
