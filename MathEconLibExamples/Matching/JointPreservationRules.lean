/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Choice.Matching.Preferences
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.FinCases

/-!
# Hospital choices in the three-doctor example

Each doctor has two contracts. The original choice accepts one contract per represented
doctor. Doctors 1 and 2 have priority for their a-term. Doctor 3 has priority for their
a-term except when both earlier a-terms are offered.

The three witness completions are indexed by the doctor whose target they sacrifice.
-/

@[expose] public section

namespace MathEconLib.Examples.Matching.JointPreservation

open MathEconLib.Choice
open ChoiceFunction

/-- Two possible terms for each of three doctors. -/
inductive Contract
  | a1 | b1 | a2 | b2 | a3 | b3
  deriving DecidableEq

open Contract

instance : Fintype Contract where
  elems := {a1, b1, a2, b2, a3, b3}
  complete x := by cases x <;> simp

/-- The counterparty map, indexed by doctor number minus one. -/
def worker : Contract → Fin 3
  | a1 | b1 => 0
  | a2 | b2 => 1
  | a3 | b3 => 2

/-- The hospital's priority test for an offered contract. -/
def originalAccepts (Y : Set Contract) : Contract → Prop
  | a1 | a2 => True
  | b1 => a1 ∉ Y
  | b2 => a2 ∉ Y
  | a3 => ¬ (a1 ∈ Y ∧ a2 ∈ Y ∧ b3 ∈ Y)
  | b3 => a3 ∉ Y ∨ (a1 ∈ Y ∧ a2 ∈ Y)

/-- Original choice, using the menu-dependent third-doctor priority. -/
def original : ChoiceFunction Contract where
  toFun Y := {x ∈ Y | originalAccepts Y x}
  choose_subset _ _ hx := hx.1

@[simp] theorem mem_original {Y : Set Contract} {x : Contract} :
    x ∈ original Y ↔ x ∈ Y ∧ originalAccepts Y x :=
  Iff.rfl

/-- The priority test for the completion sacrificing doctor j's target. -/
def pairAccepts (j : Fin 3) (Y : Set Contract) : Contract → Prop
  | a1 | a2 | a3 => True
  | b1 => j = 0 ∨ a1 ∉ Y
  | b2 => j = 1 ∨ a2 ∉ Y
  | b3 => j = 2 ∨ a3 ∉ Y ∨ (if j = 0 then b1 else b2) ∉ Y

/-- Select both terms of doctor j when offered, modifying doctor 3's priority
so that the other two targets survive. -/
def pairCompletion (j : Fin 3) : ChoiceFunction Contract where
  toFun Y := {x ∈ Y | pairAccepts j Y x}
  choose_subset _ _ hx := hx.1

@[simp] theorem mem_pairCompletion {j : Fin 3} {Y : Set Contract} {x : Contract} :
    x ∈ pairCompletion j Y ↔ x ∈ Y ∧ pairAccepts j Y x :=
  Iff.rfl

/-- No doctor has two contracts in the original hospital choice. -/
theorem original_feasible (Y : Set Contract) : Set.InjOn worker (original Y) := by
  intro x hx y hy hxy
  cases x <;> cases y <;> simp [worker] at hxy ⊢ <;>
    simp only [mem_original, originalAccepts] at hx hy <;> tauto

/-- The original hospital accepts every term on a feasible menu. -/
theorem original_apply_of_feasible {Y : Set Contract} (hY : Set.InjOn worker Y) :
    original Y = Y := by
  apply Set.Subset.antisymm (original.choose_subset Y)
  intro x hx
  have different {a b : Contract} (ha : a ∈ Y) (hw : worker a = worker b)
      (hne : a ≠ b) : b ∉ Y := fun hb ↦ hne (hY ha hb hw)
  refine mem_original.mpr ⟨hx, ?_⟩
  cases x with
  | a1 | a2 => trivial
  | b1 => exact different hx rfl (by decide)
  | b2 => exact different hx rfl (by decide)
  | a3 => exact fun h ↦ different (b := b3) hx rfl (by decide) h.2.2
  | b3 => exact Or.inl (different hx rfl (by decide))

/-- A sole offer from a doctor cannot witness failure of unilateral substitutes. -/
theorem original_unilaterallySubstitutable :
    original.UnilaterallySubstitutable worker := by
  intro x _ Y hfresh hrej
  exfalso
  apply hrej
  have otherAbsent {z : Contract} (hw : worker z = worker x) (hne : z ≠ x) :
      z ∉ insert x Y := by
    intro hz
    exact (Set.mem_insert_iff.mp hz).elim hne (fun h ↦ hfresh _ h hw)
  refine mem_original.mpr ⟨Set.mem_insert _ _, ?_⟩
  cases x with
  | a1 | a2 => trivial
  | b1 => exact otherAbsent rfl (by decide)
  | b2 => exact otherAbsent rfl (by decide)
  | a3 => exact fun h ↦ otherAbsent (z := b3) rfl (by decide) h.2.2
  | b3 => exact Or.inl (otherAbsent rfl (by decide))

/-- Retaining every selected contract retains the earlier a-terms and thus
doctor 3's priority. -/
theorem original_consistent : original.Consistent := by
  intro Y Z hretain hsub
  have keep (x : Contract) : x ∈ Y → originalAccepts Y x → x ∈ Z :=
    fun hx ha ↦ hretain (mem_original.mpr ⟨hx, ha⟩)
  have h1 : a1 ∈ Z ↔ a1 ∈ Y := ⟨fun h ↦ hsub h, fun h ↦ keep a1 h trivial⟩
  have h2 : a2 ∈ Z ↔ a2 ∈ Y := ⟨fun h ↦ hsub h, fun h ↦ keep a2 h trivial⟩
  apply Set.Subset.antisymm
  · intro x hx
    rw [mem_original] at hx ⊢
    refine ⟨hsub hx.1, ?_⟩
    have ha := hx.2
    cases x with
    | a1 | a2 => trivial
    | b1 => exact fun h ↦ ha (h1.mpr h)
    | b2 => exact fun h ↦ ha (h2.mpr h)
    | a3 =>
        intro h
        exact ha ⟨h1.mpr h.1, h2.mpr h.2.1, keep b3 h.2.2 (Or.inr ⟨h.1, h.2.1⟩)⟩
    | b3 =>
        by_cases h : a1 ∈ Y ∧ a2 ∈ Y
        · exact Or.inr h
        · refine Or.inl fun ha3 ↦ ?_
          have ha3Z := keep a3 ha3 (fun hb ↦ h ⟨hb.1, hb.2.1⟩)
          exact ha.elim (fun hna ↦ hna ha3Z) (fun hab ↦ h ⟨h1.mp hab.1, h2.mp hab.2⟩)
  · intro x hx
    have hxZ := hretain hx
    rw [mem_original] at hx ⊢
    refine ⟨hxZ, ?_⟩
    have ha := hx.2
    cases x with
    | a1 | a2 => trivial
    | b1 => exact fun h ↦ ha (h1.mp h)
    | b2 => exact fun h ↦ ha (h2.mp h)
    | a3 => exact fun h ↦ ha ⟨h1.mp h.1, h2.mp h.2.1, hsub h.2.2⟩
    | b3 => exact ha.imp (fun h hy ↦ h (hsub hy)) (fun h ↦ ⟨h1.mpr h.1, h2.mpr h.2⟩)

/-- Every witness is substitutable because all of its rejection conditions
persist under enlargement of the menu. -/
theorem pairCompletion_substitutable (j : Fin 3) : (pairCompletion j).Substitutable := by
  apply substitutable_iff_chernoff.mpr
  intro Y Z hsub x hx
  rcases mem_pairCompletion.mp hx.1 with ⟨_, h⟩
  apply mem_pairCompletion.mpr
  refine ⟨hx.2, ?_⟩
  cases x with
  | a1 | a2 | a3 => trivial
  | b1 => exact h.imp_right (fun ha hy ↦ ha (hsub hy))
  | b2 => exact h.imp_right (fun ha hy ↦ ha (hsub hy))
  | b3 => exact h.imp_right (fun h ↦ h.imp (fun ha hy ↦ ha (hsub hy))
      (fun hb hy ↦ hb (hsub hy)))

/-- A witness that alters a feasible original choice takes both terms of
some doctor. -/
theorem pairCompletion_isCompletion (j : Fin 3) :
    original.IsCompletionOf worker (pairCompletion j) := by
  classical
  intro Y
  by_cases hD : ∃ x ∈ pairCompletion j Y, ∃ y ∈ pairCompletion j Y,
      x ≠ y ∧ worker x = worker y
  · exact Or.inr hD
  · left
    have conflicting {x y : Contract} (hw : worker x = worker y) (hne : x ≠ y) :
        ¬ (x ∈ pairCompletion j Y ∧ y ∈ pairCompletion j Y) :=
      fun h ↦ hD ⟨x, h.1, y, h.2, hne, hw⟩
    have h1 := conflicting (x := a1) (y := b1) rfl (by decide)
    have h2 := conflicting (x := a2) (y := b2) rfl (by decide)
    have h3 := conflicting (x := a3) (y := b3) rfl (by decide)
    clear conflicting hD
    fin_cases j
    all_goals
      ext x
      cases x <;> simp [pairAccepts, originalAccepts] at h1 h2 h3 ⊢ <;> tauto

private def originalAcceptsDecidable (Y : Finset Contract) (x : Contract) :
    Decidable (originalAccepts (Y : Set Contract) x) := by
  cases x <;> simp only [originalAccepts, Finset.mem_coe] <;> infer_instance

private def pairAcceptsDecidable (j : Fin 3) (Y : Finset Contract) (x : Contract) :
    Decidable (pairAccepts j (Y : Set Contract) x) := by
  cases x <;> simp only [pairAccepts, Finset.mem_coe] <;> infer_instance

private def originalFinset (Y : Finset Contract) : Finset Contract :=
  @Finset.filter _ (originalAccepts (Y : Set Contract)) (originalAcceptsDecidable Y) Y

private def pairFinset (j : Fin 3) (Y : Finset Contract) : Finset Contract :=
  @Finset.filter _ (pairAccepts j (Y : Set Contract)) (pairAcceptsDecidable j Y) Y

private theorem sizeMonotone_of_insert_check {C : ChoiceFunction Contract}
    (f : Finset Contract → Finset Contract)
    (hf : ∀ Y, (f Y : Set Contract) = C (Y : Set Contract))
    (h : ∀ (Y : Finset Contract) (x : Contract), (f Y).card ≤ (f (insert x Y)).card) :
    C.SizeMonotone := by
  classical
  have step (W : Set Contract) (x : Contract) : (C W).ncard ≤ (C (insert x W)).ncard := by
    let F := (Set.toFinite W).toFinset
    have hF : (F : Set Contract) = W := Set.Finite.coe_toFinset _
    simpa only [← Set.ncard_coe_finset, hf, Finset.coe_insert, hF] using h F x
  intro Y Z hZ hYZ
  have unionStep (T : Set Contract) (hT : T.Finite) :
      (C Y).ncard ≤ (C (Y ∪ T)).ncard := by
    induction T, hT using Set.Finite.induction_on with
    | empty => simp
    | @insert x T _ _ ih =>
        rw [Set.union_insert]
        exact ih.trans (step (Y ∪ T) x)
  simpa only [Set.union_eq_self_of_subset_left hYZ] using unionStep Z hZ

/-- Original choice satisfies the law of aggregate demand.
The kernel checks one added offer on every menu of the six contracts. -/
theorem original_sizeMonotone : original.SizeMonotone := by
  apply sizeMonotone_of_insert_check originalFinset
  · intro Y
    ext x
    simp [originalFinset]
  · decide

/-- Each pair witness satisfies the law of aggregate demand.
The kernel checks one added offer on every menu of the six contracts. -/
theorem pairCompletion_lawOfAggregateDemand (j : Fin 3) : (pairCompletion j).SizeMonotone := by
  apply sizeMonotone_of_insert_check (pairFinset j)
  · intro Y
    ext x
    simp [pairFinset]
  · have h : ∀ (i : Fin 3) (Y : Finset Contract) (x : Contract),
        (pairFinset i Y).card ≤ (pairFinset i (insert x Y)).card := by decide
    exact h j

/-- Substitutability and aggregate demand imply IRC for these finite witnesses. -/
theorem pairCompletion_consistent (j : Fin 3) : (pairCompletion j).Consistent :=
  (pairCompletion_substitutable j).consistent_of_sizeMonotone
    (pairCompletion_lawOfAggregateDemand j)

end MathEconLib.Examples.Matching.JointPreservation
