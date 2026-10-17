/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
import MathEconLib.Matching.Contracts.Basic
import MathEconLib.Choice.Induced
import MathEconLib.Choice.Map

/-!
# Many-to-one matching with contracts

Sellers are the unit-demand proposers (doctors); buyers are the accepting
institutions (hospitals). We specialize the existing `Market` rather than
introduce another stability notion. `SellersUnitDemand` and
`BuyersCounterpartyFeasible` record the two choice restrictions separately.
An outcome is feasible when its seller map is injective.

`ofSellerPreferences` constructs a market from strict preferences over each
seller's own contracts and the outside option, and supported buyer choices.
It does not assume substitutability or feasibility of buyer choices, so it
also represents completed markets. IRC of the induced seller choices is
proved for finite contract types; unit demand holds without finiteness.

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
applies to original many-to-one choices, not necessarily their completions. -/
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

end Market

end MathEconLib.Matching
