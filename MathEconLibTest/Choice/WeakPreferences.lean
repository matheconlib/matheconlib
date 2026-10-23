/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLib.Choice
import MathEconLibExamples.Choice.WeakPreferences
import Lean.Elab.Tactic.Omega

/-!
# Weak-preference choice clients

Empty and unattained feasible menus distinguish an empty correspondence from the represented
outside option. A finite incomplete preference shows why existence requires completeness.
An infinite all-tied example has weak optima but no optimum after increasing-priority refinement.
The worked utility and participation examples are imported, not reconstructed.
-/

open MathEconLib.Choice

namespace MathEconLibTest.Choice.WeakPreferences

/-- The infinite feasible menu of natural numbers has no greatest element. -/
theorem unattained : maximizers (inferInstance : Preorder ℕ) Set.univ = ∅ := by
  ext n
  simp only [Set.mem_empty_iff_false, iff_false]
  intro h
  have hnext := h.2 (Set.mem_univ (n + 1))
  omega

/-- A preorder that only compares equal alternatives is incomplete on this two-element type. -/
def incomparable : Preorder (Fin 2) where
  le := Eq
  lt := fun a b ↦ a = b ∧ ¬b = a
  le_refl := Eq.refl
  le_trans := fun _ _ _ hab hbc ↦ hab.trans hbc

/-- Finiteness alone does not ensure a greatest alternative under incomplete preferences. -/
theorem incomplete_no_maximizer : maximizers incomparable Set.univ = ∅ := by
  ext n
  simp only [Set.mem_empty_iff_false, iff_false]
  intro h
  have hzero : (0 : Fin 2) = n := h.2 (Set.mem_univ 0)
  have hone : (1 : Fin 2) = n := h.2 (Set.mem_univ 1)
  exact (by decide : (0 : Fin 2) ≠ 1) (hzero.trans hone.symm)

namespace InfiniteTies

/-- Every natural-number singleton is represented, with no represented empty bundle. -/
def bundle : ℕ ↪ Set ℕ where
  toFun n := {n}
  inj' := Set.singleton_injective

/-- All represented bundles are indifferent. -/
def pref : Preorder ℕ := Preorder.lift fun _ : ℕ ↦ (0 : ℕ)

theorem complete : Std.Total pref.le :=
  ⟨fun _ _ ↦ Or.inl (show (0 : ℕ) ≤ 0 from le_rfl)⟩

/-- Every singleton is a weak optimum on the infinite menu. -/
theorem singleton_mem (n : ℕ) : {n} ∈ optimalBundles pref bundle Set.univ :=
  (mem_optimalBundles_iff pref bundle).mpr
    ⟨n, rfl, Set.subset_univ _, fun _ _ ↦ (show (0 : ℕ) ≤ 0 from le_rfl)⟩

/-- Weak preferences attain an optimum despite the infinite feasible family. -/
theorem optimal_nonempty : (optimalBundles pref bundle Set.univ).Nonempty :=
  ⟨{0}, singleton_mem 0⟩

/-- Increasing natural-number priorities have no greatest feasible index. -/
theorem refined_unattained :
    maximizers (MathEconLib.Order.tieBreakOrder pref complete
      (Function.Embedding.refl ℕ)).toPreorder Set.univ = ∅ := by
  ext b
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hb
  have h := (MathEconLib.Order.tieBreakOrder_le_iff pref complete
    (Function.Embedding.refl ℕ) (b + 1) b).mp (hb.2 (Set.mem_univ (b + 1)))
  have hnext : b + 1 ≤ b := h.2
    ⟨(show (0 : ℕ) ≤ 0 from le_rfl), (show (0 : ℕ) ≤ 0 from le_rfl)⟩
  exact Nat.not_succ_le_self b hnext

/-- The existing selector totalizes refinement nonattainment to the empty set. -/
theorem selected_empty :
    ChoiceFunction.ofWeakBundleOrder pref complete (Function.Embedding.refl ℕ)
      bundle Set.univ = ∅ := by
  ext x
  simp only [ChoiceFunction.ofWeakBundleOrder, ChoiceFunction.mem_ofBundleOrder,
    Set.mem_empty_iff_false, iff_false]
  rintro ⟨b, _, _, hmax⟩
  have hb : b ∈ maximizers (MathEconLib.Order.tieBreakOrder pref complete
      (Function.Embedding.refl ℕ)).toPreorder Set.univ :=
    ⟨Set.mem_univ _, fun c _ ↦ hmax c (Set.subset_univ _)⟩
  simp only [refined_unattained, Set.mem_empty_iff_false] at hb

/-- Totalization is not a weak optimum: the empty bundle is not represented. -/
theorem empty_not_optimal : ∅ ∉ optimalBundles pref bundle Set.univ := by
  intro h
  obtain ⟨b, heq, _, _⟩ := (mem_optimalBundles_iff pref bundle).mp h
  have hmem := congrArg (fun S : Set ℕ ↦ b ∈ S) heq
  simp [bundle] at hmem

/-- Existence of weak optima alone does not guarantee optimality of the refined selection. -/
theorem selected_not_optimal :
    ChoiceFunction.ofWeakBundleOrder pref complete (Function.Embedding.refl ℕ)
      bundle Set.univ ∉ optimalBundles pref bundle Set.univ := by
  rw [selected_empty]
  exact empty_not_optimal

end InfiniteTies

open MathEconLibExamples.Choice.WeakPreferences

example : {(0 : Fin 2)} ∈ optimalBundles Contracts.pref ChoiceFunction.optionBundle Set.univ :=
  Contracts.singleton_mem 0

example :
    ¬(⋃₀ optimalBundles Contracts.pref ChoiceFunction.optionBundle Set.univ).Subsingleton :=
  Contracts.union_not_subsingleton

example : ChoiceFunction.ofWeakBundleOrder OutsideTie.pref OutsideTie.complete
    OutsideTie.outsidePriority ChoiceFunction.optionBundle Set.univ = ∅ :=
  OutsideTie.selected_outside

example : ∅ ∈ optimalBundles OutsideTie.pref ChoiceFunction.optionBundle (∅ : Set (Fin 2)) :=
  OutsideTie.empty_mem_empty_menu

example : optimalBundles Bundles.pref Bundles.bundle ∅ = ∅ := Bundles.empty_menu

#print axioms mem_maximizers_lift
#print axioms mem_optimalBundles_iff
#print axioms optimalBundles_nonempty_of_finite_feasible
#print axioms ChoiceFunction.ofBundleOrder_mem_optimalBundles_of_finite_feasible
#print axioms MathEconLib.Order.tieBreakOrder_le_iff
#print axioms MathEconLib.Order.tieBreakOrder_of_linearOrder
#print axioms maximizers_nonempty_of_finite
#print axioms optimalBundles_nonempty_of_finite
#print axioms ChoiceFunction.ofWeakBundleOrder_mem_optimalBundles_of_finite
#print axioms ChoiceFunction.ofWeakBundleOrder_linearOrder
#print axioms ChoiceFunction.bestOption_mem_maximizers
#print axioms Contracts.union_not_subsingleton
#print axioms Contracts.selected_eq
#print axioms OutsideTie.selected_outside
#print axioms OutsideTie.selected_contract
#print axioms Bundles.selected_mem
#print axioms Bundles.selected_eq
#print axioms unattained
#print axioms incomplete_no_maximizer
#print axioms FiniteFamily.selected_mem
#print axioms InfiniteTies.singleton_mem
#print axioms InfiniteTies.optimal_nonempty
#print axioms InfiniteTies.refined_unattained
#print axioms InfiniteTies.selected_empty
#print axioms InfiniteTies.empty_not_optimal
#print axioms InfiniteTies.selected_not_optimal

end MathEconLibTest.Choice.WeakPreferences
