/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLib.Choice.WeakPreferences
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Finite choices with ties

Two contracts give gross values 4 and 6 at prices 3 and 5. Both yield net utility 1;
the outside option yields 0. The best-bundle family retains both singleton contracts.
Taking their union violates unit demand; a fixed priority instead selects one singleton.

When all utilities are zero, the outside option ties with both contracts. Two fixed priorities
give different participation decisions, both consistent with the same weak preferences.
These are finite choice examples, not matching stability or incentive results.
-/

namespace MathEconLibExamples.Choice.WeakPreferences

open MathEconLib.Choice MathEconLib.Preferences

namespace Contracts

/-- Gross values of two contracts. -/
def value (i : Fin 2) : ℤ := if i = 0 then 4 else 6

/-- Payments for the two contracts. -/
def price (i : Fin 2) : ℤ := if i = 0 then 3 else 5

/-- Quasilinear net utility, with zero utility from nonparticipation. -/
def utility : Option (Fin 2) → ℤ
  | none => 0
  | some i => value i - price i

@[simp] theorem utility_none : utility none = 0 := rfl

@[simp] theorem utility_some (i : Fin 2) : utility (some i) = 1 := by
  fin_cases i <;> norm_num [utility, value, price]

/-- Utility induces a complete preorder that keeps the two contracts distinct. -/
@[instance_reducible] def pref : CompletePreference (Option (Fin 2)) :=
  CompletePreference.ofUtility utility

theorem complete : Std.Total pref.le := ⟨fun a b ↦ le_total (utility a) (utility b)⟩

/-- Fixed priority: contract 1, then contract 0, then the outside option. -/
def priority : Option (Fin 2) ↪ Fin 3 := (finSuccEquiv 2).symm.toEmbedding

/-- Each tied acceptable singleton remains a possible best bundle. -/
theorem singleton_mem (i : Fin 2) :
    {i} ∈ optimalBundles pref.toPreference ChoiceFunction.optionBundle Set.univ := by
  apply (mem_optimalBundles_iff pref.toPreference ChoiceFunction.optionBundle).mpr
  refine ⟨some i, rfl, Set.subset_univ _, ?_⟩
  change ∀ o, ChoiceFunction.optionBundle o ⊆ Set.univ → utility o ≤ utility (some i)
  simp [Option.forall]

/-- The union of all optimal bundles is not a unit-demand holding. -/
theorem union_not_subsingleton :
    ¬(⋃₀ optimalBundles pref.toPreference ChoiceFunction.optionBundle Set.univ).Subsingleton := by
  intro h
  have hzero : (0 : Fin 2) ∈
      ⋃₀ optimalBundles pref.toPreference ChoiceFunction.optionBundle Set.univ :=
    Set.mem_sUnion.mpr ⟨{0}, singleton_mem 0, Set.mem_singleton 0⟩
  have hone : (1 : Fin 2) ∈
      ⋃₀ optimalBundles pref.toPreference ChoiceFunction.optionBundle Set.univ :=
    Set.mem_sUnion.mpr ⟨{1}, singleton_mem 1, Set.mem_singleton 1⟩
  exact (by decide : (0 : Fin 2) ≠ 1) (h hzero hone)

/-- The general finite-choice theorem certifies that the selected bundle is weakly optimal. -/
theorem selected_mem :
    ChoiceFunction.ofWeakBundleOrder pref priority ChoiceFunction.optionBundle Set.univ ∈
      optimalBundles pref.toPreference ChoiceFunction.optionBundle Set.univ :=
  ChoiceFunction.ofWeakBundleOrder_mem_optimalBundles_of_finite pref priority
    ChoiceFunction.optionBundle Set.finite_univ ⟨none, Set.empty_subset _⟩

/-- Fixed priority selects contract 1 from the two equally good contracts. -/
theorem selected_eq :
    ChoiceFunction.ofWeakBundleOrder pref priority ChoiceFunction.optionBundle Set.univ =
      {(1 : Fin 2)} := by
  apply ChoiceFunction.ofWeakBundleOrder_eq_of_max pref priority
    ChoiceFunction.optionBundle (b := some 1)
  case hpriority => simp [priority, Option.forall]
  case hb => exact Set.subset_univ _
  case hmax =>
    change ∀ c, ChoiceFunction.optionBundle c ⊆ Set.univ → utility c ≤ utility (some 1)
    simp [Option.forall]

end Contracts

namespace OutsideTie

/-- Both contracts and nonparticipation yield zero utility. -/
@[instance_reducible] def pref : CompletePreference (Option (Fin 2)) :=
  CompletePreference.ofUtility fun _ ↦ (0 : ℤ)

theorem complete : Std.Total pref.le := ⟨fun _ _ ↦ Or.inl (show (0 : ℤ) ≤ 0 from le_rfl)⟩

/-- Fixed priority puts nonparticipation above the contracts. -/
def outsidePriority : Option (Fin 2) ↪ Fin 3 := finSuccEquivLast.symm.toEmbedding

/-- Every represented bundle, including the empty one, is weakly optimal. -/
theorem bundle_mem (o : Option (Fin 2)) :
    ChoiceFunction.optionBundle o ∈
      optimalBundles pref.toPreference ChoiceFunction.optionBundle Set.univ :=
  (mem_optimalBundles_iff pref.toPreference ChoiceFunction.optionBundle).mpr
    ⟨o, rfl, Set.subset_univ _, fun _ _ ↦ (show (0 : ℤ) ≤ 0 from le_rfl)⟩

/-- One fixed tie-break chooses nonparticipation. -/
theorem selected_outside :
    ChoiceFunction.ofWeakBundleOrder pref outsidePriority ChoiceFunction.optionBundle
      Set.univ = ∅ := by
  apply ChoiceFunction.ofWeakBundleOrder_eq_of_max pref outsidePriority
    ChoiceFunction.optionBundle (b := none)
  case hpriority => simp [outsidePriority, Option.forall]
  case hb => exact Set.subset_univ _
  case hmax => exact fun _ _ ↦ (show (0 : ℤ) ≤ 0 from le_rfl)

/-- A different fixed tie-break chooses participation under the same weak preferences. -/
theorem selected_contract :
    ChoiceFunction.ofWeakBundleOrder pref Contracts.priority ChoiceFunction.optionBundle
      Set.univ = {(1 : Fin 2)} := by
  apply ChoiceFunction.ofWeakBundleOrder_eq_of_max pref Contracts.priority
    ChoiceFunction.optionBundle (b := some 1)
  case hpriority => simp [Contracts.priority, Option.forall]
  case hb => exact Set.subset_univ _
  case hmax => exact fun _ _ ↦ (show (0 : ℤ) ≤ 0 from le_rfl)

/-- At an empty menu, the represented outside option is still an optimal bundle. -/
theorem empty_mem_empty_menu :
    ∅ ∈ optimalBundles pref.toPreference ChoiceFunction.optionBundle (∅ : Set (Fin 2)) :=
  (mem_optimalBundles_iff pref.toPreference ChoiceFunction.optionBundle).mpr
    ⟨none, rfl, Set.empty_subset _, fun _ _ ↦ (show (0 : ℤ) ≤ 0 from le_rfl)⟩

end OutsideTie

namespace Bundles

/-- Two feasible consumption bundles, one containing two goods and the other one good. -/
def bundle : Fin 2 ↪ Set (Fin 3) where
  toFun i := if i = 0 then {0, 1} else {2}
  inj' := by
    intro i j h
    have hzero := congrArg (fun A : Set (Fin 3) ↦ (0 : Fin 3) ∈ A) h
    clear h
    fin_cases i <;> fin_cases j <;> simp_all

/-- The bundles have values 7 and 9 at transfers 2 and 4, hence the same net utility. -/
def utility (i : Fin 2) : ℤ := (if i = 0 then 7 else 9) - (if i = 0 then 2 else 4)

@[simp] theorem utility_eq (i : Fin 2) : utility i = 5 := by
  fin_cases i <;> norm_num [utility]

@[instance_reducible] def pref : CompletePreference (Fin 2) := CompletePreference.ofUtility utility

theorem complete : Std.Total pref.le := ⟨fun a b ↦ le_total (utility a) (utility b)⟩

/-- Both different bundles remain in the correspondence. -/
theorem bundle_mem (i : Fin 2) : bundle i ∈ optimalBundles pref.toPreference bundle Set.univ :=
  (mem_optimalBundles_iff pref.toPreference bundle).mpr
    ⟨i, rfl, Set.subset_univ _, fun j _ ↦ by change utility j ≤ utility i; simp⟩

/-- The selected consumption bundle is a member of the weak correspondence. -/
theorem selected_mem :
    ChoiceFunction.ofWeakBundleOrder pref (Function.Embedding.refl (Fin 2)) bundle
      Set.univ ∈ optimalBundles pref.toPreference bundle Set.univ :=
  ChoiceFunction.ofWeakBundleOrder_mem_optimalBundles_of_finite pref _ bundle
    Set.finite_univ ⟨0, Set.subset_univ _⟩

/-- Priority selects the one-good bundle while retaining the two-good bundle as an alternative. -/
theorem selected_eq :
    ChoiceFunction.ofWeakBundleOrder pref (Function.Embedding.refl (Fin 2)) bundle
      Set.univ = {(2 : Fin 3)} := by
  apply ChoiceFunction.ofWeakBundleOrder_eq_of_max pref
    (Function.Embedding.refl (Fin 2)) bundle (b := 1)
  case hb => exact Set.subset_univ _
  case hmax =>
    change ∀ c, bundle c ⊆ Set.univ → utility c ≤ utility 1
    simp
  case hpriority => exact fun c _ _ ↦ Fin.le_last c

/-- No represented bundle is feasible at the empty menu, so the correspondence is empty. -/
theorem empty_menu : optimalBundles pref.toPreference bundle ∅ = ∅ := by
  ext A
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hA
  obtain ⟨i, rfl, h, _⟩ := (mem_optimalBundles_iff pref.toPreference bundle).mp hA
  have hnonempty : (bundle i).Nonempty := by
    change (if i = 0 then {0, 1} else {2} : Set (Fin 3)).Nonempty
    split_ifs <;> simp
  exact hnonempty.not_subset_empty h

end Bundles

namespace FiniteFamily

/-- Only two singleton bundles are represented, although the menu contains all natural numbers. -/
def bundle : Fin 2 ↪ Set ℕ where
  toFun i := {i.val}
  inj' := fun _ _ h ↦ Fin.val_injective (Set.singleton_injective h)

/-- The ordinary order on the two indices refines the all-tied weak preferences. -/
theorem selected_mem :
    ChoiceFunction.ofBundleOrder (inferInstance : LinearOrder (Fin 2)) bundle Set.univ ∈
      optimalBundles (Preference.ofUtility fun _ : Fin 2 ↦ (0 : ℕ)) bundle Set.univ :=
  ChoiceFunction.ofBundleOrder_mem_optimalBundles_of_finite_feasible _ _
    (fun _ _ _ ↦ (show (0 : ℕ) ≤ 0 from le_rfl)) bundle (Set.toFinite _)
    ⟨0, Set.subset_univ _⟩

end FiniteFamily

end MathEconLibExamples.Choice.WeakPreferences
