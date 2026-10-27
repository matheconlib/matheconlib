/-
Copyright (c) 2026 Scott Duke Kominers, Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers, Bo Cowgill
-/
import MathEconLib.Matching.Contracts.Basic
import MathEconLib.Choice.Induced
import MathEconLib.Choice.Map

/-!
# Many-to-one matching with contracts

Sellers are the unit-demand proposers (doctors); buyers are the accepting
institutions (hospitals). We specialize the existing `Market` rather than
introducing another stability concept. An outcome is feasible when its seller
map is injective. `SellersUnitDemand` and `BuyersCounterpartyFeasible` record
the two associated choice restrictions separately.


`ofSellerPreferences` constructs a market from strict preferences over each
seller's own contracts and the outside option, and supported buyer choices.
It does not assume (seller-)feasibility of buyer choices, so it also represents
completed markets. IRC of the induced seller choices is proved for finite
contract types; unit demand is well-defined without finiteness hypotheses.

`HasSellerOptimum` and `Declines` apply the strict choice predicates to a seller's own-contract
subtype menu. The latter means that the outside option is optimal under the supplied order and
itself guarantees attainment. An empty seller choice can also result from nonattainment.

## Participation statements

* `choiceS_ofSellerPreferences_eq_empty_iff`: empty seller choice reflects nonattainment or
  optimal nonparticipation on the seller's own available contracts.
* `choiceS_ofSellerPreferences_eq_empty_iff_of_hasSellerOptimum`: under attainment, empty seller
  choice is equivalent to `Declines`.
* `choiceS_ofSellerPreferences_nonempty_iff_of_hasSellerOptimum`: under attainment, a seller
  participates exactly when the outside option is not optimal.
* `hasSellerOptimum_of_finite_ownMenu`: only the seller's own menu needs to be finite.

Contracts belonging to other sellers are ignored, as in `ofSellerPreferences`. Use the actual
supplied strict order, including its priorities when preferences have been refined.

## References

John William Hatfield and Scott Duke Kominers (2025), *The theory of matching
with contracts*, Handbook of the Economics of Matching 2, 409–487, §6.1.
https://doi.org/10.1016/bs.hesmat.2025.10.005.
-/

namespace MathEconLib.Matching

open MathEconLib.Choice

namespace Market

variable {B S X : Type*} (M : Market B S X)

/-- Every seller chooses at most one contract from any menu. -/
def SellersUnitDemand : Prop := ∀ s, (M.choiceS s).UnitDemand

/-- A buyer chooses at most one contract with each seller. This restriction
applies to many-to-one choice functions, not necessarily their completions. -/
def BuyersCounterpartyFeasible : Prop :=
  ∀ b Y, Set.InjOn M.seller (M.choiceB b Y)

/-- A feasible many-to-one outcome assigns at most one contract to each seller. -/
def ManyToOneFeasible (A : Set X) : Prop := Set.InjOn M.seller A

/-- Individual rationality and seller unit demand imply outcome feasibility. -/
theorem IndRational.manyToOneFeasible (hunit : M.SellersUnitDemand)
    {A : Set X} (hA : M.IndRational A) : M.ManyToOneFeasible A := by
  intro x hx y hy hxy
  have hxC := M.mem_choiceS_of_indRational hA hx
  have hyC := M.mem_choiceS_of_indRational hA hy
  rw [← hxy] at hyC
  exact hunit (M.seller x) A hxC hyC

/-- Seller unit demand makes every stable outcome feasible. -/
theorem Stable.manyToOneFeasible (hunit : M.SellersUnitDemand)
    {A : Set X} (hA : M.Stable A) : M.ManyToOneFeasible A :=
  hA.1.manyToOneFeasible M hunit

/-- IRC supplies substitutability for unit-demand sellers. -/
theorem SellersUnitDemand.substitutable (hunit : M.SellersUnitDemand)
    (hcons : ∀ s, (M.choiceS s).Consistent) :
    ∀ s, (M.choiceS s).Substitutable :=
  fun s => (hunit s).substitutable (hcons s)

/-- Construct a market from buyer choices and strict preferences over each
seller's own contracts plus the outside option. Higher alternatives are better.
On infinite menus without a greatest acceptable contract, the underlying
preference selector returns the empty set. -/
def ofSellerPreferences (buyer : X → B) (seller : X → S)
    (choiceB : B → ChoiceFunction X)
    (hB : ∀ ⦃b Y x⦄, x ∈ choiceB b Y → buyer x = b)
    (pref : ∀ s, LinearOrder (Option {x : X // seller x = s})) :
    Market B S X where
  buyer := buyer
  seller := seller
  choiceB := choiceB
  choiceS s := (ChoiceFunction.ofOptionLinearOrder (pref s)).map
    (Function.Embedding.subtype (fun x => seller x = s))
  buyer_eq_of_mem := hB
  seller_eq_of_mem := by
    rintro s Y x ⟨y, _, rfl⟩
    exact y.property

/-! ## Seller attainment and optimal nonparticipation -/

/-- A greatest option exists among a seller's own available contracts and the outside option. -/
def HasSellerOptimum (seller : X → S)
    (pref : ∀ s, LinearOrder (Option {x : X // seller x = s})) (s : S) (Y : Set X) : Prop :=
  ChoiceFunction.HasBundleOptimum (pref s) ChoiceFunction.optionBundle
    ((Subtype.val : {x : X // seller x = s} → X) ⁻¹' Y)

/-- The outside option is optimal among a seller's own available contracts.
This describes the supplied preference, independently of totalized empty choice. -/
def Declines (seller : X → S)
    (pref : ∀ s, LinearOrder (Option {x : X // seller x = s})) (s : S) (Y : Set X) : Prop :=
  ChoiceFunction.OutsideOptionOptimal (pref s)
    ((Subtype.val : {x : X // seller x = s} → X) ⁻¹' Y)

/-- Declining compares only contracts owned by this seller and present in the menu. -/
theorem declines_iff (seller : X → S)
    (pref : ∀ s, LinearOrder (Option {x : X // seller x = s})) (s : S) (Y : Set X) :
    Declines seller pref s Y ↔
      ∀ x : {x : X // seller x = s}, (x : X) ∈ Y → (pref s).le (some x) none := Iff.rfl

/-- An optimal outside option is an attained seller optimum, even on an infinite menu. -/
theorem Declines.hasSellerOptimum {seller : X → S}
    {pref : ∀ s, LinearOrder (Option {x : X // seller x = s})} {s : S} {Y : Set X}
    (h : Declines seller pref s Y) : HasSellerOptimum seller pref s Y :=
  ChoiceFunction.OutsideOptionOptimal.hasBundleOptimum h

/-- Finiteness of the seller's own available contracts suffices; other menus may be infinite. -/
theorem hasSellerOptimum_of_finite_ownMenu (seller : X → S)
    (pref : ∀ s, LinearOrder (Option {x : X // seller x = s})) (s : S) {Y : Set X}
    (hY : ((Subtype.val : {x : X // seller x = s} → X) ⁻¹' Y).Finite) :
    HasSellerOptimum seller pref s Y :=
  ChoiceFunction.hasBundleOptimum_optionBundle_of_finite (pref s) hY

/-- A finite contract menu supplies attainment without a finite contract carrier. -/
theorem hasSellerOptimum_of_finite (seller : X → S)
    (pref : ∀ s, LinearOrder (Option {x : X // seller x = s})) (s : S) {Y : Set X}
    (hY : Y.Finite) : HasSellerOptimum seller pref s Y :=
  hasSellerOptimum_of_finite_ownMenu seller pref s
    (hY.preimage_embedding (Function.Embedding.subtype (fun x ↦ seller x = s)))

variable (buyer : X → B) (seller : X → S)
    (choiceB : B → ChoiceFunction X)
    (hB : ∀ ⦃b Y x⦄, x ∈ choiceB b Y → buyer x = b)
    (pref : ∀ s, LinearOrder (Option {x : X // seller x = s}))

/-- The preference constructor has unit-demand sellers on arbitrary types. -/
theorem sellersUnitDemand_ofSellerPreferences :
    (ofSellerPreferences buyer seller choiceB hB pref).SellersUnitDemand :=
  fun s => (ChoiceFunction.unitDemand_ofOptionLinearOrder (pref s)).map _

/-- Finite own-contract menus give IRC of the induced seller choices. -/
theorem consistent_choiceS_ofSellerPreferences [Finite X] (s : S) :
    ((ofSellerPreferences buyer seller choiceB hB pref).choiceS s).Consistent :=
  (ChoiceFunction.consistent_ofOptionLinearOrder (pref s)).map _

/-- Empty seller choice is caused by nonattainment or optimal nonparticipation. -/
theorem choiceS_ofSellerPreferences_eq_empty_iff (s : S) (Y : Set X) :
    (ofSellerPreferences buyer seller choiceB hB pref).choiceS s Y = ∅ ↔
      ¬ HasSellerOptimum seller pref s Y ∨ Declines seller pref s Y :=
  (Set.image_eq_empty (f := fun x : {x : X // seller x = s} ↦ (x : X))).trans
    (ChoiceFunction.ofOptionLinearOrder_eq_empty_iff (pref s) _)

/-- Under own-menu attainment, empty seller choice means that the outside option is optimal. -/
theorem choiceS_ofSellerPreferences_eq_empty_iff_of_hasSellerOptimum (s : S) {Y : Set X}
    (h : HasSellerOptimum seller pref s Y) :
    (ofSellerPreferences buyer seller choiceB hB pref).choiceS s Y = ∅ ↔
      Declines seller pref s Y :=
  (Set.image_eq_empty (f := fun x : {x : X // seller x = s} ↦ (x : X))).trans
    (ChoiceFunction.ofOptionLinearOrder_eq_empty_iff_of_hasBundleOptimum (pref s) h)

/-- Under attainment, a seller participates exactly when the outside option is not optimal. -/
theorem choiceS_ofSellerPreferences_nonempty_iff_of_hasSellerOptimum (s : S) {Y : Set X}
    (h : HasSellerOptimum seller pref s Y) :
    ((ofSellerPreferences buyer seller choiceB hB pref).choiceS s Y).Nonempty ↔
      ¬ Declines seller pref s Y :=
  Set.nonempty_iff_ne_empty.trans
    (not_congr (choiceS_ofSellerPreferences_eq_empty_iff_of_hasSellerOptimum
      buyer seller choiceB hB pref s h))

/-- Preference for the outside option implies empty choice without a separate attainment premise. -/
theorem choiceS_ofSellerPreferences_eq_empty_of_declines (s : S) {Y : Set X}
    (h : Declines seller pref s Y) :
    (ofSellerPreferences buyer seller choiceB hB pref).choiceS s Y = ∅ :=
  (choiceS_ofSellerPreferences_eq_empty_iff_of_hasSellerOptimum
    buyer seller choiceB hB pref s h.hasSellerOptimum).mpr h

end Market

end MathEconLib.Matching
