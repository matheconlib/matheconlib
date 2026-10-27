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
The `Option ℕ` regression represents the outside option explicitly and gives it strictly lower
utility than every contract. Reversing priorities restores attainment on this infinite menu,
but well-founded priorities alone do not supply a missing weak optimum.
The worked utility and participation examples are imported, not reconstructed.
-/

open MathEconLib.Choice MathEconLib.Preferences

namespace MathEconLibTest.Choice.WeakPreferences

/-- The infinite feasible menu of natural numbers has no greatest element. -/
theorem unattained :
    maximizers (Preference.ofPreorder (inferInstance : Preorder ℕ)) Set.univ = ∅ := by
  ext n
  simp only [Set.mem_empty_iff_false, iff_false]
  intro h
  have hnext := h.2 (Set.mem_univ (n + 1))
  omega

/-- A preorder that only compares equal alternatives is incomplete on this two-element type. -/
@[instance_reducible] def incomparable : Preference (Fin 2) where
  le := Eq
  isPreorder := { refl := Eq.refl, trans := fun _ _ _ hab hbc ↦ hab.trans hbc }

/-- Finiteness alone does not ensure a greatest alternative under incomplete preferences. -/
theorem incomplete_no_maximizer : maximizers incomparable Set.univ = ∅ := by
  ext n
  simp only [Set.mem_empty_iff_false, iff_false]
  intro h
  have hzero : (0 : Fin 2) = n := h.2 (Set.mem_univ 0)
  have hone : (1 : Fin 2) = n := h.2 (Set.mem_univ 1)
  exact (by decide : (0 : Fin 2) ≠ 1) (hzero.trans hone.symm)

/-- Both alternatives are maximal, although `incomplete_no_maximizer` excludes a greatest one. -/
theorem incomparable_maximal (a : Fin 2) :
    ∀ x, incomparable.le a x → incomparable.le x a := fun _ h ↦ h.symm

namespace InfiniteTies

/-- Every natural-number singleton is represented, with no represented empty bundle. -/
def bundle : ℕ ↪ Set ℕ where
  toFun n := {n}
  inj' := Set.singleton_injective

/-- All represented bundles are indifferent. -/
@[instance_reducible] def pref : CompletePreference ℕ :=
  CompletePreference.ofUtility fun _ : ℕ ↦ (0 : ℕ)

theorem complete : Std.Total pref.le :=
  ⟨fun _ _ ↦ Or.inl (show (0 : ℕ) ≤ 0 from le_rfl)⟩

/-- Every singleton is a weak optimum on the infinite menu. -/
theorem singleton_mem (n : ℕ) : {n} ∈ optimalBundles pref.toPreference bundle Set.univ :=
  (mem_optimalBundles_iff pref.toPreference bundle).mpr
    ⟨n, rfl, Set.subset_univ _, fun _ _ ↦ (show (0 : ℕ) ≤ 0 from le_rfl)⟩

/-- Weak preferences attain an optimum despite the infinite feasible family. -/
theorem optimal_nonempty : (optimalBundles pref.toPreference bundle Set.univ).Nonempty :=
  ⟨{0}, singleton_mem 0⟩

/-- Increasing natural-number priorities have no greatest feasible index. -/
theorem refined_unattained :
    maximizers (Preference.ofPreorder (pref.tieBreak
      (Function.Embedding.refl ℕ)).toPreorder) Set.univ = ∅ := by
  ext b
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hb
  have h := (pref.tieBreak_le_iff
    (Function.Embedding.refl ℕ) (b + 1) b).mp (hb.2 (Set.mem_univ (b + 1)))
  have hnext : b + 1 ≤ b := h.2
    ⟨(show (0 : ℕ) ≤ 0 from le_rfl), (show (0 : ℕ) ≤ 0 from le_rfl)⟩
  exact Nat.not_succ_le_self b hnext

/-- The existing selector totalizes refinement nonattainment to the empty set. -/
theorem selected_empty :
    ChoiceFunction.ofWeakBundleOrder pref (Function.Embedding.refl ℕ)
      bundle Set.univ = ∅ := by
  apply ChoiceFunction.ofBundleOrder_eq_empty_of_maximizers_eq_empty
  simpa only [Set.subset_univ, Set.ofPred_true] using refined_unattained

/-- Totalization is not a weak optimum: the empty bundle is not represented. -/
theorem empty_not_optimal : ∅ ∉ optimalBundles pref.toPreference bundle Set.univ := by
  intro h
  obtain ⟨b, heq, _, _⟩ := (mem_optimalBundles_iff pref.toPreference bundle).mp h
  have hmem := congrArg (fun S : Set ℕ ↦ b ∈ S) heq
  simp [bundle] at hmem

/-- Existence of weak optima alone does not guarantee optimality of the refined selection. -/
theorem selected_not_optimal :
    ChoiceFunction.ofWeakBundleOrder pref (Function.Embedding.refl ℕ)
      bundle Set.univ ∉ optimalBundles pref.toPreference bundle Set.univ := by
  rw [selected_empty]
  exact empty_not_optimal

end InfiniteTies

namespace OutsideOptionNonattainment

/-- Every contract is strictly better than the represented outside option. -/
def utility : Option ℕ → ℕ
  | none => 0
  | some _ => 1

@[instance_reducible] def pref : CompletePreference (Option ℕ) :=
  CompletePreference.ofUtility utility

/-- Contracts have unbounded increasing priorities; the outside option has priority zero. -/
def increasingPriority : Option ℕ ↪ ℕ where
  toFun
    | none => 0
    | some n => n + 1
  inj' := by
    intro a b h
    cases a <;> cases b <;> simp_all

/-- The outside option is represented and feasible on the infinite menu. -/
theorem outside_feasible : ChoiceFunction.optionBundle (none : Option ℕ) ⊆ Set.univ :=
  Set.subset_univ _

/-- Every contract singleton is a weak optimum, regardless of its priority. -/
theorem singleton_mem (n : ℕ) :
    {n} ∈ optimalBundles pref.toPreference ChoiceFunction.optionBundle Set.univ := by
  refine (mem_optimalBundles_iff pref.toPreference ChoiceFunction.optionBundle).mpr
    ⟨some n, rfl, Set.subset_univ _, ?_⟩
  intro c _
  change utility c ≤ utility (some n)
  cases c <;> simp [utility]

theorem optimal_nonempty :
    (optimalBundles pref.toPreference ChoiceFunction.optionBundle Set.univ).Nonempty :=
  ⟨{0}, singleton_mem 0⟩

/-- The empty bundle is feasible but is strictly worse than any contract. -/
theorem empty_not_optimal :
    ∅ ∉ optimalBundles pref.toPreference ChoiceFunction.optionBundle Set.univ := by
  intro h
  obtain ⟨b, heq, _, hmax⟩ :=
    (mem_optimalBundles_iff pref.toPreference ChoiceFunction.optionBundle).mp h
  cases b with
  | none =>
    have h := hmax (some 0) (Set.subset_univ _)
    change 1 ≤ 0 at h
    omega
  | some n =>
    have hmem := congrArg (fun S : Set ℕ ↦ n ∈ S) heq
    simp at hmem

/-- No contract wins the increasing-priority tie, and the outside option loses on utility. -/
theorem refined_unattained :
    maximizers (Preference.ofPreorder (pref.tieBreak increasingPriority).toPreorder)
      Set.univ = ∅ := by
  ext b
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hb
  cases b with
  | none =>
    have h := (pref.tieBreak_le_iff increasingPriority (some 0) none).mp
      (hb.2 (Set.mem_univ (some 0)))
    have hweak : (1 : ℕ) ≤ 0 := h.1
    omega
  | some n =>
    have h := (pref.tieBreak_le_iff increasingPriority (some (n + 1)) (some n)).mp
      (hb.2 (Set.mem_univ (some (n + 1))))
    have hpriority := h.2 ⟨(show (1 : ℕ) ≤ 1 from le_rfl), le_rfl⟩
    change n + 1 + 1 ≤ n + 1 at hpriority
    omega

/-- The priority image fails to attain despite the existence of weak optima. -/
theorem priority_unattained :
    ¬∃ p, IsGreatest (increasingPriority '' maximizers pref.toPreference Set.univ) p := by
  exact fun h ↦
    let ⟨b, hb⟩ := (maximizers_tieBreak_nonempty_iff pref increasingPriority Set.univ).mpr h
    Set.notMem_empty b (refined_unattained ▸ hb)

/-- The selector returns the empty set even though the represented outside option is suboptimal. -/
theorem selected_empty :
    ChoiceFunction.ofWeakBundleOrder pref increasingPriority
      ChoiceFunction.optionBundle Set.univ = ∅ := by
  apply ChoiceFunction.ofBundleOrder_eq_empty_of_maximizers_eq_empty
  simpa only [Set.subset_univ, Set.ofPred_true] using refined_unattained

theorem selected_not_optimal :
    ChoiceFunction.ofWeakBundleOrder pref increasingPriority
      ChoiceFunction.optionBundle Set.univ ∉
        optimalBundles pref.toPreference ChoiceFunction.optionBundle Set.univ := by
  rw [selected_empty]
  exact empty_not_optimal

/-- Reversing the same numeric priorities gives the tied contracts a greatest priority. -/
def decreasingPriority : Option ℕ ↪ ℕᵒᵈ where
  toFun b := OrderDual.toDual (increasingPriority b)
  inj' := increasingPriority.injective

/-- Strict improvement in this priority codomain is well-founded. -/
theorem priority_wellFounded : WellFoundedGT ℕᵒᵈ := inferInstance

/-- An infinite menu can attain a winner: contract zero has the greatest reversed priority. -/
theorem reversed_selected :
    ChoiceFunction.ofWeakBundleOrder pref decreasingPriority
      ChoiceFunction.optionBundle Set.univ = {0} := by
  apply ChoiceFunction.ofWeakBundleOrder_eq_of_max pref decreasingPriority
    ChoiceFunction.optionBundle (b := some 0) (Set.subset_univ _)
  · intro c _
    change utility c ≤ utility (some 0)
    cases c <;> simp [utility]
  · intro c _ h
    cases c with
    | none =>
      have hweak : (1 : ℕ) ≤ 0 := h.2
      omega
    | some n =>
      change 1 ≤ n + 1
      omega

theorem reversed_selected_optimal :
    ChoiceFunction.ofWeakBundleOrder pref decreasingPriority
      ChoiceFunction.optionBundle Set.univ ∈
        optimalBundles pref.toPreference ChoiceFunction.optionBundle Set.univ :=
  ChoiceFunction.ofWeakBundleOrder_mem_optimalBundles_of_wellFoundedGT
    pref decreasingPriority ChoiceFunction.optionBundle optimal_nonempty

end OutsideOptionNonattainment

namespace MissingWeakOptimum

open OutsideOptionNonattainment (increasingPriority decreasingPriority)

/-- Utility now strictly increases with the contract index, so there is no weak optimum. -/
@[instance_reducible] def pref : CompletePreference (Option ℕ) :=
  CompletePreference.ofUtility increasingPriority

/-- The same well-founded reversed priorities cannot fix nonattainment in the weak preference. -/
theorem weak_unattained : maximizers pref.toPreference Set.univ = ∅ := by
  ext b
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hb
  cases b with
  | none =>
    have h : (1 : ℕ) ≤ 0 := hb.2 (Set.mem_univ (some 0))
    omega
  | some n =>
    have h : n + 1 + 1 ≤ n + 1 := hb.2 (Set.mem_univ (some (n + 1)))
    omega

theorem optimal_empty :
    optimalBundles pref.toPreference ChoiceFunction.optionBundle Set.univ = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro A hA
  obtain ⟨b, _, _, hmax⟩ :=
    (mem_optimalBundles_iff pref.toPreference ChoiceFunction.optionBundle).mp hA
  have hb : b ∈ maximizers pref.toPreference Set.univ :=
    ⟨Set.mem_univ _, fun c _ ↦ hmax c (Set.subset_univ _)⟩
  simp only [weak_unattained, Set.mem_empty_iff_false] at hb

theorem refined_unattained :
    maximizers (Preference.ofPreorder (pref.tieBreak decreasingPriority).toPreorder)
      Set.univ = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  exact fun b hb ↦
    let ⟨c, hc⟩ := (maximizers_tieBreak_nonempty_iff_of_wellFoundedGT
      pref decreasingPriority Set.univ).mp ⟨b, hb⟩
    Set.notMem_empty c (weak_unattained ▸ hc)

theorem selected_empty :
    ChoiceFunction.ofWeakBundleOrder pref decreasingPriority
      ChoiceFunction.optionBundle Set.univ = ∅ := by
  apply ChoiceFunction.ofBundleOrder_eq_empty_of_maximizers_eq_empty
  simpa only [Set.subset_univ, Set.ofPred_true] using refined_unattained

end MissingWeakOptimum

open MathEconLibExamples.Choice.WeakPreferences

namespace OutsideOptionTies

/-- All indices, including the outside option, are weakly optimal under the same preference. -/
theorem weak_max (o : Option (Fin 2)) :
    o ∈ maximizers OutsideTie.pref.toPreference
      {b | ChoiceFunction.optionBundle b ⊆ (Set.univ : Set (Fin 2))} :=
  ⟨Set.subset_univ _, fun _ _ ↦ (show (0 : ℤ) ≤ 0 from le_rfl)⟩

/-- The outside option wins only with the priority that ranks it highest. -/
theorem outside_refined :
    none ∈ maximizers (Preference.ofPreorder
      (OutsideTie.pref.tieBreak OutsideTie.outsidePriority).toPreorder)
      {b | ChoiceFunction.optionBundle b ⊆ (Set.univ : Set (Fin 2))} :=
  (mem_maximizers_tieBreak_iff OutsideTie.pref OutsideTie.outsidePriority).mpr
    ⟨weak_max none, fun o _ ↦
      (show OutsideTie.outsidePriority o ≤ (2 : Fin 3) from Fin.le_last _)⟩

theorem contract_refined :
    some (1 : Fin 2) ∈ maximizers (Preference.ofPreorder
      (OutsideTie.pref.tieBreak Contracts.priority).toPreorder)
      {b | ChoiceFunction.optionBundle b ⊆ (Set.univ : Set (Fin 2))} :=
  (mem_maximizers_tieBreak_iff OutsideTie.pref Contracts.priority).mpr
    ⟨weak_max (some 1), fun o _ ↦
      (show Contracts.priority o ≤ (2 : Fin 3) from Fin.le_last _)⟩

/-- Weak optimality of the outside option does not imply it wins the refined participation
decision. -/
theorem outside_not_refined :
    none ∉ maximizers (Preference.ofPreorder
      (OutsideTie.pref.tieBreak Contracts.priority).toPreorder)
      {b | ChoiceFunction.optionBundle b ⊆ (Set.univ : Set (Fin 2))} := by
  exact fun h ↦
    (by decide : ¬ Contracts.priority (some 1) ≤ Contracts.priority none)
      (((mem_maximizers_tieBreak_iff OutsideTie.pref Contracts.priority).mp h).2
        (some 1) (weak_max (some 1)))

theorem selected_outside :
    ChoiceFunction.ofWeakBundleOrder OutsideTie.pref OutsideTie.outsidePriority
      ChoiceFunction.optionBundle Set.univ = ∅ :=
  ChoiceFunction.ofWeakBundleOrder_eq_of_mem_maximizers
    OutsideTie.pref OutsideTie.outsidePriority ChoiceFunction.optionBundle outside_refined

theorem selected_contract :
    ChoiceFunction.ofWeakBundleOrder OutsideTie.pref Contracts.priority
      ChoiceFunction.optionBundle Set.univ = {(1 : Fin 2)} :=
  ChoiceFunction.ofWeakBundleOrder_eq_of_mem_maximizers
    OutsideTie.pref Contracts.priority ChoiceFunction.optionBundle contract_refined

theorem selected_contract_optimal :
    ChoiceFunction.ofWeakBundleOrder OutsideTie.pref Contracts.priority
      ChoiceFunction.optionBundle Set.univ ∈
        optimalBundles OutsideTie.pref.toPreference ChoiceFunction.optionBundle Set.univ :=
  ChoiceFunction.ofWeakBundleOrder_mem_optimalBundles_of_finite_maximizers
    OutsideTie.pref Contracts.priority ChoiceFunction.optionBundle (Set.toFinite _)
      ⟨∅, OutsideTie.bundle_mem none⟩

end OutsideOptionTies

example : {(0 : Fin 2)} ∈
    optimalBundles Contracts.pref.toPreference ChoiceFunction.optionBundle Set.univ :=
  Contracts.singleton_mem 0

example :
    ¬(⋃₀ optimalBundles Contracts.pref.toPreference
      ChoiceFunction.optionBundle Set.univ).Subsingleton :=
  Contracts.union_not_subsingleton

example : ChoiceFunction.ofWeakBundleOrder OutsideTie.pref
    OutsideTie.outsidePriority ChoiceFunction.optionBundle Set.univ = ∅ :=
  OutsideTie.selected_outside

example : ∅ ∈ optimalBundles OutsideTie.pref.toPreference
    ChoiceFunction.optionBundle (∅ : Set (Fin 2)) :=
  OutsideTie.empty_mem_empty_menu

example : optimalBundles Bundles.pref.toPreference Bundles.bundle ∅ = ∅ := Bundles.empty_menu

#print axioms mem_maximizers_ofUtility
#print axioms mem_maximizers_lift
#print axioms mem_optimalBundles_iff
#print axioms optimalBundles_nonempty_of_finite_feasible
#print axioms ChoiceFunction.ofBundleOrder_mem_optimalBundles_of_finite_feasible
#print axioms MathEconLib.Order.tieBreakOrder_le_iff
#print axioms MathEconLib.Order.tieBreakOrder_of_linearOrder
#print axioms maximizers_nonempty_of_finite
#print axioms optimalBundles_nonempty_of_finite
#print axioms ChoiceFunction.ofWeakBundleOrder_mem_optimalBundles_of_finite
#print axioms ChoiceFunction.ofWeakBundleOrder_of_linearOrder
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
#print axioms OutsideOptionNonattainment.singleton_mem
#print axioms OutsideOptionNonattainment.optimal_nonempty
#print axioms OutsideOptionNonattainment.empty_not_optimal
#print axioms OutsideOptionNonattainment.refined_unattained
#print axioms OutsideOptionNonattainment.priority_unattained
#print axioms OutsideOptionNonattainment.selected_empty
#print axioms OutsideOptionNonattainment.selected_not_optimal
#print axioms OutsideOptionNonattainment.priority_wellFounded
#print axioms OutsideOptionNonattainment.reversed_selected
#print axioms OutsideOptionNonattainment.reversed_selected_optimal
#print axioms MissingWeakOptimum.weak_unattained
#print axioms MissingWeakOptimum.optimal_empty
#print axioms MissingWeakOptimum.refined_unattained
#print axioms MissingWeakOptimum.selected_empty
#print axioms OutsideOptionTies.outside_refined
#print axioms OutsideOptionTies.contract_refined
#print axioms OutsideOptionTies.outside_not_refined
#print axioms OutsideOptionTies.selected_outside
#print axioms OutsideOptionTies.selected_contract
#print axioms OutsideOptionTies.selected_contract_optimal

end MathEconLibTest.Choice.WeakPreferences
