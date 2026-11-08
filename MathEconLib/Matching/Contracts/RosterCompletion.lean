/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Matching.Contracts.RosterAssignments
public import Mathlib.Order.SupClosed
import Mathlib.Order.Preorder.Finite

/-!
# Cutoff completions for roster choice

Fix the hospital's roster-choice rule `R` and a family of target assignments
on the roster selected when every doctor is represented. For each offer
menu, the cutoff completion selects doctors using `R`. It keeps each
offered term that is weakly worse for its doctor than their term in every
target contained in the menu. With finitely many contracts and a meet-closed
target family, a nonempty set of eligible targets has a least element
determining the cutoff.
-/

@[expose] public section

namespace MathEconLib.Matching

open MathEconLib.Choice

variable {S X : Type*} {seller : X → S} {R : ChoiceFunction S}
  [∀ i, LinearOrder {x : X // seller x = i}]

/-- Choose the roster from represented doctors and keep their terms unless a
target assignment contained in the menu requires rejecting a better term. -/
def rosterCompletion (seller : X → S) (R : ChoiceFunction S)
    [∀ i, LinearOrder {x : X // seller x = i}]
    (T : Set (RosterAssignment seller (R (Set.range seller)))) : ChoiceFunction X where
  toFun Y := {x ∈ Y | seller x ∈ R (seller '' Y) ∧
    ∀ A ∈ T, A.terms ⊆ Y → ∀ i : R (Set.range seller), ∀ h : seller x = i.1,
      (⟨x, h⟩ : {y : X // seller y = i.1}) ≤ A i}
  choose_subset := fun _ _ hx ↦ hx.1

variable {T : Set (RosterAssignment seller (R (Set.range seller)))}

omit [∀ i, LinearOrder {x : X // seller x = i}] in
/-- A menu containing an assignment of the full roster selects that roster. -/
theorem roster_eq_of_terms_subset {Y : Set X} {A : RosterAssignment seller (R (Set.range seller))}
    (hR : R.Consistent) (hAY : A.terms ⊆ Y) : R (seller '' Y) = R (Set.range seller) := by
  apply hR _ (Set.image_subset_range _ _)
  rw [← A.image_terms]
  exact Set.image_mono hAY

/-- With a nonempty family of eligible targets closed under meets, there is a
least eligible target. -/
theorem exists_rosterCompletion_cutoff [Finite X] {Y : Set X}
    (hT : InfClosed T) (hY : ∃ A ∈ T, A.terms ⊆ Y) :
    ∃ K ∈ T, K.terms ⊆ Y ∧ ∀ A ∈ T, A.terms ⊆ Y → K ≤ A := by
  let U : Set (RosterAssignment seller (R (Set.range seller))) := {A ∈ T | A.terms ⊆ Y}
  let : Finite (RosterAssignment seller (R (Set.range seller))) :=
    Finite.of_injective _ RosterAssignment.terms_injective
  obtain ⟨K, hK⟩ := (Set.toFinite U).exists_minimal (show U.Nonempty from hY)
  refine ⟨K, hK.1.1, hK.1.2, fun A hA hAY ↦ ?_⟩
  have hKA : K ⊓ A ∈ U :=
    ⟨hT hK.1.1 hA, (K.terms_inf_subset A).trans (Set.union_subset hK.1.2 hAY)⟩
  exact (hK.2 hKA inf_le_left).trans inf_le_right

/-- The terms of an available lower bound of the eligible targets are kept. -/
theorem rosterCompletion_terms_subset {Y : Set X}
    {K : RosterAssignment seller (R (Set.range seller))}
    (hR : R.Consistent) (hKY : K.terms ⊆ Y)
    (hbound : ∀ A ∈ T, A.terms ⊆ Y → K ≤ A) :
    K.terms ⊆ rosterCompletion seller R T Y := by
  rintro _ ⟨i, rfl⟩
  refine ⟨hKY (K.term_mem_terms i), ?_, ?_⟩
  · rw [roster_eq_of_terms_subset hR hKY, (K i).2]
    exact i.2
  · intro A hA hAY j hj
    have hij : i = j := Subtype.ext ((K i).2.symm.trans hj)
    subst j
    exact hbound A hA hAY i

/-- A contract is kept at an eligible least target's cutoff exactly when it is
offered to a roster doctor and is weakly worse than their cutoff term. -/
theorem mem_rosterCompletion_iff_of_cutoff {Y : Set X} {x : X}
    {K : RosterAssignment seller (R (Set.range seller))}
    (hR : R.Consistent) (hKT : K ∈ T) (hKY : K.terms ⊆ Y)
    (hbound : ∀ A ∈ T, A.terms ⊆ Y → K ≤ A) :
    x ∈ rosterCompletion seller R T Y ↔
      x ∈ Y ∧ ∃ i : (R (Set.range seller)), ∃ h : seller x = i.1,
        (⟨x, h⟩ : {y : X // seller y = i.1}) ≤ K i := by
  constructor
  · rintro ⟨hx, hs, hle⟩
    rw [roster_eq_of_terms_subset hR hKY] at hs
    let i : (R (Set.range seller)) := ⟨seller x, hs⟩
    exact ⟨hx, i, rfl, hle K hKT hKY i rfl⟩
  · rintro ⟨hx, i, hi, hxi⟩
    refine ⟨hx, ?_, ?_⟩
    · rw [roster_eq_of_terms_subset hR hKY, hi]
      exact i.2
    · intro A hA hAY j hj
      have hji : j = i := Subtype.ext (hj.symm.trans hi)
      subst j
      exact hxi.trans (hbound A hA hAY i)

/-- On a target's improvement menu, the cutoff keeps exactly that assignment. -/
theorem rosterCompletion_eq_terms_on_improvementMenu
    (hR : R.Consistent) {A : RosterAssignment seller (R (Set.range seller))} (hA : A ∈ T) :
    rosterCompletion seller R T A.improvementMenu = A.terms := by
  have hbound (B : RosterAssignment seller (R (Set.range seller))) (_ : B ∈ T)
      (hB : B.terms ⊆ A.improvementMenu) : A ≤ B :=
    RosterAssignment.terms_subset_improvementMenu_iff.mp hB
  refine Set.Subset.antisymm ?_ (rosterCompletion_terms_subset hR
    A.terms_subset_improvementMenu hbound)
  intro x hx
  obtain ⟨hxY, i, hi, hxi⟩ :=
    (mem_rosterCompletion_iff_of_cutoff hR hA A.terms_subset_improvementMenu hbound).mp hx
  exact (RosterAssignment.mem_terms_iff i hi).mpr
    (congrArg Subtype.val (le_antisymm (hxY i hi) hxi))

/-- Shrinking a menu preserves a retained doctor's roster place and can only
remove targets that constrain their terms. -/
theorem rosterCompletion_substitutable (hR : R.Substitutable) :
    (rosterCompletion seller R T).Substitutable := by
  refine ChoiceFunction.substitutable_iff_chernoff.mpr ?_
  intro Y Z hYZ x hx
  exact ⟨hx.2, hR.mem_of_subset (Set.image_mono hYZ) hx.1.2.1 ⟨x, hx.2, rfl⟩,
    fun A hA hAY ↦ hx.1.2.2 A hA (hAY.trans hYZ)⟩

private theorem image_rosterCompletion [Finite X] (hR : R.Consistent) (hT : InfClosed T)
    (Y : Set X) :
    seller '' (rosterCompletion seller R T Y) = R (seller '' Y) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hx.2.1
  · by_cases hY : ∃ A ∈ T, A.terms ⊆ Y
    · obtain ⟨K, _, hKY, hbound⟩ := exists_rosterCompletion_cutoff hT hY
      rw [roster_eq_of_terms_subset hR hKY, ← K.image_terms]
      exact Set.image_mono (rosterCompletion_terms_subset hR hKY hbound)
    · intro i hi
      obtain ⟨x, hx, rfl⟩ := R.choose_subset _ hi
      exact ⟨x, ⟨hx, hi, fun A hA hAY ↦ (hY ⟨A, hA, hAY⟩).elim⟩, rfl⟩

/-- Retaining the chosen terms retains both the selected roster and the least
eligible target, when a target is eligible. -/
theorem rosterCompletion_consistent [Finite X] (hR : R.Consistent) (hT : InfClosed T) :
    (rosterCompletion seller R T).Consistent := by
  intro Y V hDV hVY
  have hroster : R (seller '' V) = R (seller '' Y) := by
    apply hR _ (Set.image_mono hVY)
    rw [← image_rosterCompletion hR hT Y]
    exact Set.image_mono hDV
  apply Set.Subset.antisymm
  · intro x hx
    refine ⟨hVY hx.1, hroster ▸ hx.2.1, ?_⟩
    intro A hA hAY i hi
    obtain ⟨K, hKT, hKY, hbound⟩ := exists_rosterCompletion_cutoff hT ⟨A, hA, hAY⟩
    have hKV : K.terms ⊆ V := (rosterCompletion_terms_subset hR hKY hbound).trans hDV
    exact (hx.2.2 K hKT hKV i hi).trans (hbound A hA hAY i)
  · intro x hx
    exact ⟨hDV hx, hroster.symm ▸ hx.2.1, fun A hA hAV ↦ hx.2.2 A hA (hAV.trans hVY)⟩

/-- A feasible cutoff choice agrees with the original contract choice. A
binding cutoff is itself a target, so original IRC applies from its
improvement menu to the actual menu. -/
theorem rosterCompletion_isCompletionOf [Finite X] {C : ChoiceFunction X}
    (hR : R.Consistent) (hC : C.Consistent)
    (hRoster : ∀ Y, seller '' (C Y) = R (seller '' Y)) (hT : InfClosed T)
    (hStable : ∀ A ∈ T, C A.improvementMenu = A.terms) :
    C.IsCompletionOf seller (rosterCompletion seller R T) := by
  classical
  intro Y
  by_cases hD : Set.InjOn seller (rosterCompletion seller R T Y)
  · left
    by_cases hY : ∃ A ∈ T, A.terms ⊆ Y
    · obtain ⟨K, hKT, hKY, hbound⟩ := exists_rosterCompletion_cutoff hT hY
      have hKD := rosterCompletion_terms_subset hR hKY hbound
      have hcut (x : X) := mem_rosterCompletion_iff_of_cutoff (x := x) hR hKT hKY hbound
      have hDK : rosterCompletion seller R T Y = K.terms := by
        apply Set.Subset.antisymm _ hKD
        intro x hx
        obtain ⟨_, i, hi, _⟩ := (hcut x).mp hx
        exact ⟨i, (hD hx (hKD (K.term_mem_terms i)) (hi.trans (K i).2.symm)).symm⟩
      have hYI : Y ⊆ K.improvementMenu := by
        intro x hx i hi
        rcases le_total (K i) (⟨x, hi⟩ : {y : X // seller y = i.1}) with h | h
        · exact h
        · have hxD := (hcut x).mpr ⟨hx, i, hi, h⟩
          exact le_of_eq (Subtype.ext (hD (hKD (K.term_mem_terms i)) hxD
            ((K i).2.trans hi.symm)))
      rw [hDK]
      exact ((hC (hStable K hKT ▸ hKY) hYI).trans (hStable K hKT)).symm
    · have hCD : C Y ⊆ rosterCompletion seller R T Y := by
        intro x hx
        have hxR : seller x ∈ R (seller '' Y) :=
          hRoster Y ▸ Set.mem_image_of_mem seller hx
        exact ⟨C.choose_subset Y hx, hxR, fun A hA hAY ↦ (hY ⟨A, hA, hAY⟩).elim⟩
      refine Set.Subset.antisymm ?_ hCD
      intro x hx
      have hxR : seller x ∈ seller '' (C Y) := (hRoster Y).symm ▸ hx.2.1
      obtain ⟨z, hz, hzx⟩ := hxR
      rw [hD hx (hCD hz) hzx.symm]
      exact hz
  · right
    unfold Set.InjOn at hD
    push Not at hD
    obtain ⟨x, hx, y, hy, heq, hne⟩ := hD
    exact ⟨x, hx, y, hy, hne, heq⟩

end MathEconLib.Matching
