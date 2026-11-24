/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Matching.Contracts.Completion
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Order.WithBot

/-!
# Assignments on a fixed doctor roster

A roster `W` is a specified set of doctors, the sellers in `Market`.
`RosterAssignment seller W` gives each doctor in `W` one own contract.
Its `terms` map identifies these assignments with contract sets containing
exactly one contract for each roster doctor and none for other doctors.

This separates staffing from contract terms: two assignments can employ
the same doctors at different wages, shifts, or duties. The assignment
type itself assumes neither stability nor preferences.

Holding the roster fixed lets us compare contract sets and stable outcomes on that roster across
completions without invoking rural-hospitals invariance.

Once doctors rank their own terms, with better terms higher, Mathlib's
pointwise order compares assignments doctor by doctor. Their meet gives
each doctor the worse of their two terms.

The later single-hospital model adds a staffing rule that depends only
on the doctors represented in a menu and derives the roster employed at
stable outcomes. Its doctor preferences place unemployment below every
own contract.
-/

@[expose] public section

namespace MathEconLib.Matching

open MathEconLib.Choice

/-- An assignment of one contract to every doctor on the given roster. -/
abbrev RosterAssignment {S X : Type*} (seller : X → S) (W : Set S) :=
  ∀ i : W, {x : X // seller x = i.1}

namespace RosterAssignment

variable {S X : Type*} {seller : X → S} {W : Set S}

/-- The contracts assigned to the doctors on the roster. -/
def terms (A : RosterAssignment seller W) : Set X :=
  Set.range fun i ↦ (A i).1

theorem term_mem_terms (A : RosterAssignment seller W) (i : W) : (A i).1 ∈ A.terms :=
  ⟨i, rfl⟩

theorem mem_terms_iff {A : RosterAssignment seller W} {x : X} (i : W)
    (h : seller x = i.1) : x ∈ A.terms ↔ (A i).1 = x := by
  constructor
  · rintro ⟨j, hj⟩
    have hji : j = i := Subtype.ext ((A j).2.symm.trans ((congrArg seller hj).trans h))
    subst j
    exact hj
  · exact fun hA ↦ ⟨i, hA⟩

@[simp] theorem image_terms (A : RosterAssignment seller W) : seller '' A.terms = W := by
  ext i
  constructor
  · rintro ⟨x, ⟨j, hj⟩, hi⟩
    have hj' : j.1 = i := (A j).2.symm.trans ((congrArg seller hj).trans hi)
    exact hj' ▸ j.2
  · intro hi
    let j : W := ⟨i, hi⟩
    exact ⟨(A j).1, A.term_mem_terms j, (A j).2⟩

theorem injOn_terms (A : RosterAssignment seller W) : Set.InjOn seller A.terms := by
  intro x hx y hy hxy
  obtain ⟨i, rfl⟩ := hx
  exact (mem_terms_iff i (hxy.symm.trans (A i).2)).mp hy

theorem terms_injective :
    Function.Injective (terms (seller := seller) (W := W)) := by
  intro A B h
  funext i
  apply Subtype.ext
  exact (mem_terms_iff i (B i).2).mp (h.symm ▸ B.term_mem_terms i)

theorem exists_terms_eq {Y : Set X} (hY : Set.InjOn seller Y) (hR : seller '' Y = W) :
    ∃ A : RosterAssignment seller W, A.terms = Y := by
  have hex (i : W) : ∃ x ∈ Y, seller x = i.1 := by
    have hi : i.1 ∈ seller '' Y := hR.symm ▸ i.2
    exact hi
  choose x hx hs using hex
  let A : RosterAssignment seller W := fun i ↦ ⟨x i, hs i⟩
  refine ⟨A, Set.Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact hx i
  · intro y hy
    have hi : seller y ∈ W := hR ▸ Set.mem_image_of_mem seller hy
    let i : W := ⟨seller y, hi⟩
    exact ⟨i, hY (hx i) hy (hs i)⟩

variable [∀ i, LinearOrder {x : X // seller x = i}]

/-- Incumbents, weakly preferred terms for roster doctors, and every term of
doctors outside the roster. -/
def improvementMenu (A : RosterAssignment seller W) : Set X :=
  {x | ∀ i : W, ∀ h : seller x = i.1,
    A i ≤ (⟨x, h⟩ : {y : X // seller y = i.1})}

theorem terms_subset_improvementMenu_iff {A B : RosterAssignment seller W} :
    B.terms ⊆ A.improvementMenu ↔ A ≤ B := by
  constructor
  · intro h i
    exact h (B.term_mem_terms i) i (B i).2
  · intro h x hx i hxi
    have heq : B i = (⟨x, hxi⟩ : {y : X // seller y = i.1}) :=
      Subtype.ext ((mem_terms_iff i hxi).mp hx)
    exact heq ▸ h i

theorem terms_subset_improvementMenu (A : RosterAssignment seller W) :
    A.terms ⊆ A.improvementMenu :=
  terms_subset_improvementMenu_iff.mpr le_rfl

theorem improvementMenu_antitone :
    Antitone (improvementMenu (seller := seller) (W := W)) := by
  intro A B hAB x hx i hi
  exact (hAB i).trans (hx i hi)

/-- The meet assigns each doctor a term already present in one input assignment. -/
theorem terms_inf_subset (A B : RosterAssignment seller W) :
    (A ⊓ B).terms ⊆ A.terms ∪ B.terms := by
  rintro _ ⟨i, rfl⟩
  change ((A i ⊓ B i).1 : X) ∈ A.terms ∪ B.terms
  rcases le_total (A i) (B i) with h | h
  · rw [inf_eq_left.mpr h]
    exact Or.inl (A.term_mem_terms i)
  · rw [inf_eq_right.mpr h]
    exact Or.inr (B.term_mem_terms i)

theorem exists_favourite_term [Finite X] (hW : W ⊆ Set.range seller) (i : W) :
    ∃ x : {x : X // seller x = i.1}, ∀ y : {x : X // seller x = i.1}, y ≤ x := by
  obtain ⟨x, hx⟩ := hW i.2
  let : Nonempty {x : X // seller x = i.1} := ⟨⟨x, hx⟩⟩
  exact Finite.exists_max id

/-- Give each hired doctor their favourite contract. -/
noncomputable def favourite [Finite X] (hW : W ⊆ Set.range seller) :
    RosterAssignment seller W :=
  fun i ↦ Classical.choose (exists_favourite_term hW i)

theorem le_favourite_apply [Finite X] (hW : W ⊆ Set.range seller) (i : W)
    (x : {x : X // seller x = i.1}) : x ≤ favourite hW i :=
  Classical.choose_spec (exists_favourite_term hW i) x

theorem le_favourite [Finite X] (hW : W ⊆ Set.range seller)
    (A : RosterAssignment seller W) : A ≤ favourite hW :=
  fun i ↦ le_favourite_apply hW i (A i)

end RosterAssignment

section SingleHospital

variable {S X : Type*} (seller : X → S) (C : ChoiceFunction X)
  [∀ i, LinearOrder {x : X // seller x = i}]

/-- The single-hospital market in which each doctor accepts every one of their terms. -/
def rosterMarket : Market Unit S X :=
  Market.ofSellerPreferences (fun _ ↦ ()) seller (fun _ ↦ C)
    (by intro b _ _ _; cases b; rfl)
    (fun i ↦ inferInstanceAs (LinearOrder (WithBot {x : X // seller x = i})))

theorem rosterMarket_sellersUnitDemand : (rosterMarket seller C).SellersUnitDemand :=
  Market.sellersUnitDemand_ofSellerPreferences _ _ _ _ _

theorem rosterMarket_consistent_choiceS [Finite X] (i : S) :
    ((rosterMarket seller C).choiceS i).Consistent :=
  Market.consistent_choiceS_ofSellerPreferences _ _ _ _ _ i

theorem mem_rosterMarket_choiceS_iff {i : S} {Y : Set X} {x : X} :
    x ∈ (rosterMarket seller C).choiceS i Y ↔
      x ∈ Y ∧ ∃ h : seller x = i, ∀ y ∈ Y, ∀ hy : seller y = i,
        (⟨y, hy⟩ : {z : X // seller z = i}) ≤ ⟨x, h⟩ := by
  let pref : LinearOrder (Option {z : X // seller z = i}) :=
    inferInstanceAs (LinearOrder (WithBot {z : X // seller z = i}))
  let e := Function.Embedding.subtype (fun z : X ↦ seller z = i)
  change x ∈ (ChoiceFunction.ofOptionLinearOrder pref).map e Y ↔ _
  rw [ChoiceFunction.mem_map_iff]
  constructor
  · rintro ⟨⟨z, hz⟩, hzY, rfl⟩
    have hh := (ChoiceFunction.mem_ofOptionLinearOrder pref).mp hzY
    refine ⟨hh.1, hz, fun y hy hyi ↦ ?_⟩
    exact WithBot.coe_le_coe.mp (hh.2.2 ⟨y, hyi⟩ hy)
  · rintro ⟨hx, hxi, hmax⟩
    refine ⟨⟨x, hxi⟩, (ChoiceFunction.mem_ofOptionLinearOrder pref).mpr ?_, rfl⟩
    refine ⟨hx, ?_, fun y hy ↦ WithBot.coe_le_coe.mpr (hmax y.1 hy y.2)⟩
    exact bot_le (α := WithBot {z : X // seller z = i}) (a := Option.some ⟨x, hxi⟩)

private theorem contract_le_congr {i j : S} (h : i = j) {x y : X}
    {hxi : seller x = i} {hyi : seller y = i} {hxj : seller x = j} {hyj : seller y = j} :
    ((⟨x, hxi⟩ : {z : X // seller z = i}) ≤ ⟨y, hyi⟩) ↔
      ((⟨x, hxj⟩ : {z : X // seller z = j}) ≤ ⟨y, hyj⟩) := by
  subst j
  rfl

theorem rosterMarket_toBuyers_terms {W : Set S} (A : RosterAssignment seller W) :
    (rosterMarket seller C).toBuyers A.terms = A.improvementMenu := by
  ext x
  rw [Market.mem_toBuyers, mem_rosterMarket_choiceS_iff]
  constructor
  · rintro ⟨_, _, hmax⟩
    intro i hi
    exact (contract_le_congr seller hi).mp
      (hmax (A i).1 (Set.mem_insert_of_mem _ (A.term_mem_terms i)) ((A i).2.trans hi.symm))
  · intro hx
    refine ⟨Set.mem_insert _ _, rfl, ?_⟩
    intro y hy hyx
    rcases Set.mem_insert_iff.mp hy with rfl | ⟨i, rfl⟩
    · exact le_rfl
    · exact (contract_le_congr seller (hyx.symm.trans (A i).2)).mpr
        (hx i (hyx.symm.trans (A i).2))

end SingleHospital

end MathEconLib.Matching
