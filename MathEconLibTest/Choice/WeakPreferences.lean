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

end MathEconLibTest.Choice.WeakPreferences
