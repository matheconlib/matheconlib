/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLib.Matching.Contracts.ManyToOne

/-!
# Seller participation with and without attainment

Two sellers each own countably many contracts, indexed by natural numbers, with one buyer who
accepts every offered contract. Under increasing strict ranks, every own contract is preferable
to the outside option but there is no greatest one. The seller choice is empty by nonattainment.
Reversing the ranks makes the outside option greatest, giving an attained empty choice.

## Main definitions

* `Contract` and `OwnContract`: seller identity and a natural-number contract index.
* `increasing` and `outsideFirst`: strict preferences induced by opposite orders on option ranks.
* `increasingMarket` and `decliningMarket`: markets with these seller preferences.

## Main statements

* `increasing_unattained`, `increasing_not_declines`, and `increasing_empty`: empty choice
  despite strict preference for every own contract over nonparticipation.
* `outside_declines`, `outside_attains`, and `outside_empty`: attained nonparticipation.
* `mixed_attains` and `mixed_participates`: an infinite global menu with just one own contract
  attains and induces participation, regardless of the other seller's unbounded menu.

These statements concern seller choice and make no stability or equilibrium claim.
-/

namespace MathEconLibExamples.Matching.SellerParticipation

open MathEconLib.Choice MathEconLib.Choice.ChoiceFunction MathEconLib.Matching

abbrev Contract := Bool × ℕ

def buyer (_ : Contract) : Unit := ()

def seller (x : Contract) : Bool := x.1

abbrev OwnContract (s : Bool) := {x : Contract // seller x = s}

/-- Seller `s`'s contract with natural-number index `n`. -/
def contract (s : Bool) (n : ℕ) : OwnContract s := ⟨(s, n), rfl⟩

/-- Own-contract indices are injective because the seller identity is fixed. -/
def ownIndex (s : Bool) : OwnContract s ↪ ℕ where
  toFun x := x.val.2
  inj' a b h := Subtype.ext (Prod.ext (a.property.trans b.property.symm) h)

/-- The outside option has rank zero; contract `n` has rank `n + 1`. -/
def rank (s : Bool) : Option (OwnContract s) ↪ ℕ where
  toFun o := o.elim 0 (fun x ↦ ownIndex s x + 1)
  inj' a b := match a, b with
    | none, none => fun _ ↦ rfl
    | none, some _ => fun h ↦ False.elim (Nat.noConfusion h)
    | some _, none => fun h ↦ False.elim (Nat.noConfusion h)
    | some _, some _ => fun h ↦ congrArg some ((ownIndex s).injective (Nat.succ.inj h))

@[instance_reducible] def increasing (s : Bool) : LinearOrder (Option (OwnContract s)) :=
  LinearOrder.lift' (rank s) (rank s).injective

@[instance_reducible] def outsideFirst (s : Bool) : LinearOrder (Option (OwnContract s)) :=
  LinearOrder.lift' (fun o ↦ OrderDual.toDual (rank s o)) (rank s).injective

/-- The single buyer accepts its entire menu. -/
def buyerChoice (_ : Unit) : ChoiceFunction Contract :=
  ⟨id, fun _ ↦ Set.Subset.rfl⟩

theorem buyerSupport ⦃b : Unit⦄ ⦃Y : Set Contract⦄ ⦃x : Contract⦄
    (_ : x ∈ buyerChoice b Y) : buyer x = b := Subsingleton.elim _ _

def market (pref : ∀ s, LinearOrder (Option (OwnContract s))) : Market Unit Bool Contract :=
  Market.ofSellerPreferences buyer seller buyerChoice buyerSupport pref

def increasingMarket : Market Unit Bool Contract := market increasing

def decliningMarket : Market Unit Bool Contract := market outsideFirst

/-- Every own contract is strictly preferred to the outside option. -/
theorem increasing_acceptable (s : Bool) (x : OwnContract s) :
    (increasing s).lt none (some x) := Nat.zero_lt_succ (ownIndex s x)

/-- Every feasible option on the full menu has a strictly better own contract. -/
theorem increasing_unattained (s : Bool) :
    ¬ Market.HasSellerOptimum seller increasing s Set.univ :=
  fun ⟨o, _, hmax⟩ ↦ match o with
    | none => Nat.not_succ_le_self 0
        (@hmax (some (contract s 0)) (Set.subset_univ _))
    | some x => Nat.not_succ_le_self (ownIndex s x + 1)
        (@hmax (some (contract s (ownIndex s x + 1))) (Set.subset_univ _))

theorem increasing_not_declines (s : Bool) : ¬ Market.Declines seller increasing s Set.univ :=
  fun h ↦ Nat.not_succ_le_self 0 (h (contract s 0) (Set.mem_univ _))

/-- Empty seller choice can result from nonattainment rather than a preference to stay out. -/
theorem increasing_empty (s : Bool) : increasingMarket.choiceS s Set.univ = ∅ :=
  (Market.choiceS_ofSellerPreferences_eq_empty_iff buyer seller buyerChoice buyerSupport
    increasing s Set.univ).mpr (Or.inl (increasing_unattained s))

/-- With reversed ranks, the outside option is preferred to all own available contracts. -/
theorem outside_declines (s : Bool) (Y : Set Contract) :
    Market.Declines seller outsideFirst s Y := fun x _ ↦ Nat.zero_le (ownIndex s x + 1)

theorem outside_attains (s : Bool) (Y : Set Contract) :
    Market.HasSellerOptimum seller outsideFirst s Y := (outside_declines s Y).hasSellerOptimum

/-- Here empty choice is certified by optimal nonparticipation, even on the infinite full menu. -/
theorem outside_empty (s : Bool) (Y : Set Contract) : decliningMarket.choiceS s Y = ∅ :=
  Market.choiceS_ofSellerPreferences_eq_empty_of_declines buyer seller buyerChoice buyerSupport
    outsideFirst s (outside_declines s Y)

/-- One contract for seller false, together with every contract belonging to seller true. -/
def mixedMenu : Set Contract := insert (false, 0) {x | seller x = true}

theorem mixed_infinite : mixedMenu.Infinite :=
  (Set.infinite_range_of_injective (f := fun n : ℕ ↦ (true, n))
    (fun _ _ h ↦ congrArg Prod.snd h)).mono
    (show Set.range (fun n : ℕ ↦ (true, n)) ⊆ mixedMenu from
      fun _ ⟨n, h⟩ ↦ h ▸ (show (true, n) ∈ mixedMenu from Or.inr rfl))

/-- Mapping to the own-contract subtype removes every other seller's contract. -/
theorem mixed_ownMenu_eq :
    (Subtype.val : OwnContract false → Contract) ⁻¹' mixedMenu = {contract false 0} := by
  ext x
  simp [mixedMenu, x.property, Subtype.ext_iff, contract]

theorem mixed_attains : Market.HasSellerOptimum seller increasing false mixedMenu :=
  Market.hasSellerOptimum_of_finite_ownMenu seller increasing false
    (mixed_ownMenu_eq.symm ▸ Set.finite_singleton _)

theorem mixed_not_declines : ¬ Market.Declines seller increasing false mixedMenu :=
  fun h ↦ Nat.not_succ_le_self 0 (h (contract false 0) (Or.inl rfl))

/-- Finite own-menu attainment certifies participation on this infinite global menu. -/
theorem mixed_participates : (increasingMarket.choiceS false mixedMenu).Nonempty :=
  (Market.choiceS_ofSellerPreferences_nonempty_iff_of_hasSellerOptimum
    buyer seller buyerChoice buyerSupport increasing false mixed_attains).mpr mixed_not_declines

/-- The selected contract belongs to seller false; the other seller's menu is ignored. -/
theorem mixed_choice_eq : increasingMarket.choiceS false mixedMenu = {(false, 0)} :=
  have hsub : increasingMarket.choiceS false mixedMenu ⊆ {(false, 0)} := fun _ hx ↦
    match (increasingMarket.choiceS false).choose_subset mixedMenu hx with
    | Or.inl heq => heq
    | Or.inr hother =>
      False.elim (Bool.noConfusion ((increasingMarket.seller_eq_of_mem hx).symm.trans hother))
  have hchosen : (false, 0) ∈ increasingMarket.choiceS false mixedMenu :=
    let ⟨_, hx⟩ := mixed_participates
    (Set.mem_singleton_iff.mp (hsub hx)) ▸ hx
  Set.Subset.antisymm hsub (Set.singleton_subset_iff.mpr hchosen)

/-- An unrelated seller's contracts give no available own contract to compare with staying out. -/
theorem foreign_declines (s : Bool) :
    Market.Declines seller increasing s {x | seller x ≠ s} :=
  fun x hx ↦ (hx x.property).elim

theorem foreign_empty (s : Bool) : increasingMarket.choiceS s {x | seller x ≠ s} = ∅ :=
  Market.choiceS_ofSellerPreferences_eq_empty_of_declines buyer seller buyerChoice buyerSupport
    increasing s (foreign_declines s)

end MathEconLibExamples.Matching.SellerParticipation
