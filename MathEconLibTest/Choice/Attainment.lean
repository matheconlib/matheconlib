/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLib.Choice
import MathEconLibTest.Choice.WeakPreferences

/-!
# Strict attainment and nonparticipation regressions

Use the existing injective natural-number priorities to construct strict orders. Increasing rank
has no optimum on the infinite menu, while decreasing rank makes the outside option greatest.
The same empty choice has different attainment and correspondence certificates in these cases.
Finite menus over the infinite carrier still attain and agree with executable option choice.
The IRC equivalence detects the first order's failure and certifies the second order on all menus.
-/

open MathEconLib.Choice MathEconLib.Choice.ChoiceFunction MathEconLib.Preferences
open MathEconLibTest.Choice.WeakPreferences.OutsideOptionNonattainment

namespace MathEconLibTest.Choice.Attainment

/-- A strict order with the outside option lowest and later contracts better. -/
@[instance_reducible] def increasingOrder : LinearOrder (Option ℕ) :=
  LinearOrder.lift' increasingPriority increasingPriority.injective

/-- Every feasible option has a strictly better successor. -/
theorem strict_unattained : ¬ HasBundleOptimum increasingOrder optionBundle Set.univ :=
  fun ⟨b, _, hmax⟩ ↦ match b with
    | none => Nat.not_succ_le_self 0 (@hmax (some 0) (Set.subset_univ _))
    | some n => Nat.not_succ_le_self (n + 1) (@hmax (some (n + 1)) (Set.subset_univ _))

/-- Empty strict choice is caused by nonattainment. -/
theorem strict_selected_empty : ofOptionLinearOrder increasingOrder Set.univ = ∅ :=
  (ofOptionLinearOrder_eq_empty_iff increasingOrder Set.univ).mpr (Or.inl strict_unattained)

/-- Every contract is strictly better than the outside option in the increasing order. -/
theorem strict_outside_not_optimal : ¬ OutsideOptionOptimal increasingOrder Set.univ :=
  fun h ↦ Nat.not_succ_le_self 0 (h 0 (Set.mem_univ _))

/-- Nonattainment leaves the strict optimum correspondence empty. -/
theorem strict_correspondence_empty :
    optimalBundles (Preference.ofPreorder increasingOrder.toPreorder) optionBundle Set.univ = ∅ :=
  Set.not_nonempty_iff_eq_empty.mp fun h ↦ strict_unattained
    ((hasBundleOptimum_iff_optimalBundles_nonempty increasingOrder optionBundle Set.univ).mpr h)

/-- The empty selection is not an optimal empty bundle. -/
theorem strict_empty_not_optimal :
    ∅ ∉ optimalBundles (Preference.ofPreorder increasingOrder.toPreorder) optionBundle Set.univ :=
  fun h ↦ strict_outside_not_optimal
    ((outsideOptionOptimal_iff_empty_mem_optimalBundles increasingOrder Set.univ).mpr h)

/-- The all-menu IRC condition excludes this unattained infinite menu. -/
theorem strict_not_consistent : ¬ (ofOptionLinearOrder increasingOrder).Consistent :=
  fun h ↦ strict_unattained
    ((consistent_ofOptionLinearOrder_iff_hasBundleOptimum increasingOrder).mp h Set.univ)

/-- Reverse the rank: the outside option is now greatest on every menu. -/
@[instance_reducible] def outsideFirstOrder : LinearOrder (Option ℕ) :=
  LinearOrder.lift' decreasingPriority decreasingPriority.injective

theorem outside_optimal (Y : Set ℕ) : OutsideOptionOptimal outsideFirstOrder Y :=
  fun n _ ↦ Nat.zero_le (n + 1)

/-- Infinite-menu nonparticipation can be an attained optimum. -/
theorem outside_attains (Y : Set ℕ) : HasBundleOptimum outsideFirstOrder optionBundle Y :=
  (outside_optimal Y).hasBundleOptimum

/-- The attained empty choice is certified by outside-option optimality. -/
theorem outside_selected_empty : ofOptionLinearOrder outsideFirstOrder Set.univ = ∅ :=
  (ofOptionLinearOrder_eq_empty_iff_of_hasBundleOptimum outsideFirstOrder
    (outside_attains Set.univ)).mpr (outside_optimal Set.univ)

/-- Successful nonparticipation contains an optimal empty bundle. -/
theorem outside_empty_optimal :
    ∅ ∈ optimalBundles (Preference.ofPreorder outsideFirstOrder.toPreorder) optionBundle Set.univ :=
  (outsideOptionOptimal_iff_empty_mem_optimalBundles outsideFirstOrder Set.univ).mp
    (outside_optimal Set.univ)

/-- Attainment on every menu certifies IRC on the infinite contract carrier. -/
theorem outside_consistent : (ofOptionLinearOrder outsideFirstOrder).Consistent :=
  (consistent_ofOptionLinearOrder_iff_hasBundleOptimum outsideFirstOrder).mpr outside_attains

/-- Menu finiteness suffices even though the carrier of contracts is infinite. -/
theorem finite_menu_attains (pref : LinearOrder (Option ℕ)) (A : Finset ℕ) :
    HasBundleOptimum pref optionBundle (A : Set ℕ) :=
  hasBundleOptimum_optionBundle_of_finite pref A.finite_toSet

/-- Finite attained choice agrees with the executable finite selector. -/
theorem finite_menu_bestOption (pref : LinearOrder (Option ℕ)) (A : Finset ℕ) :
    ofOptionLinearOrder pref (A : Set ℕ) = optionBundle (bestOption pref A) := by
  ext x
  cases h : bestOption pref A
  all_goals simpa [h, eq_comm] using
    (bestOption_eq_some_iff_mem_ofOptionLinearOrder pref A (x := x)).symm

/-- The finite menu selects its greatest contract under the increasing strict order. -/
theorem finite_menu_accepts :
    ofOptionLinearOrder increasingOrder (↑({2, 7} : Finset ℕ)) = {7} :=
  (finite_menu_bestOption increasingOrder {2, 7}).trans
    (congrArg optionBundle (by decide : bestOption increasingOrder {2, 7} = some 7))

/-- On a finite menu, empty choice can always be interpreted as optimal nonparticipation. -/
theorem finite_menu_empty_iff (pref : LinearOrder (Option ℕ)) (A : Finset ℕ) :
    ofOptionLinearOrder pref (A : Set ℕ) = ∅ ↔ OutsideOptionOptimal pref (A : Set ℕ) :=
  ofOptionLinearOrder_eq_empty_iff_of_hasBundleOptimum pref (finite_menu_attains pref A)

/-- With no contracts, the outside option is always optimal. -/
theorem empty_menu_outside {α : Type*} (pref : LinearOrder (Option α)) :
    OutsideOptionOptimal pref ∅ := fun _ hx ↦ hx.elim

theorem empty_menu_attains {α : Type*} (pref : LinearOrder (Option α)) :
    HasBundleOptimum pref optionBundle ∅ :=
  (empty_menu_outside pref).hasBundleOptimum

theorem empty_menu_choice {α : Type*} (pref : LinearOrder (Option α)) :
    ofOptionLinearOrder pref ∅ = ∅ :=
  (ofOptionLinearOrder_eq_empty_iff_of_hasBundleOptimum pref (empty_menu_attains pref)).mpr
    (empty_menu_outside pref)

/-- The executable selector also returns the outside option on the empty menu. -/
theorem empty_menu_bestOption (pref : LinearOrder (Option ℕ)) : bestOption pref ∅ = none :=
  optionBundle.injective ((finite_menu_bestOption pref ∅).symm.trans
    (by simpa only [Finset.coe_empty, optionBundle_none] using empty_menu_choice pref))

/-- A general bundle family need not represent an option feasible on the empty menu. -/
theorem singleton_empty_unattained :
    ¬ HasBundleOptimum (inferInstance : LinearOrder ℕ)
      MathEconLibTest.Choice.WeakPreferences.InfiniteTies.bundle ∅ :=
  fun ⟨b, hb, _⟩ ↦ hb (Set.mem_singleton b)

end MathEconLibTest.Choice.Attainment
