/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Welfare

/-!
# Feasible projects and consumption bundles

The project examples compare one household gaining while the other is indifferent with two
households favoring opposite decisions. The bundle example gives one consumer a unit of either
of two goods. The consumer compares quantities coordinatewise and ignores the bundle label.
-/

@[expose] public section

namespace MathEconLib.Welfare.Examples

open Preferences

section PublicProject

/-- Adoption gives household `true` one unit. Household `false` always receives zero. -/
def projectPayoff (household adopt : Bool) : ℕ := if household && adopt then 1 else 0

/-- Both households rank project decisions by their own payoffs. -/
def projectPreference (household : Bool) : Preference Bool :=
  Preference.ofUtility (projectPayoff household)

private theorem project_represented (i : Bool) :
    (projectPreference i).IsRepresentedBy (projectPayoff i) :=
  Preference.isRepresentedBy_ofUtility _

/-- The status quo is weakly efficient even though adoption is a Pareto improvement. -/
theorem statusQuo_isWeaklyParetoEfficient_and_not_isParetoEfficient :
    IsWeaklyParetoEfficient projectPreference Set.univ false ∧
      ¬ IsParetoEfficient projectPreference Set.univ false := by
  constructor
  · refine (isWeaklyParetoEfficient_iff_forall_not_strongLT project_represented).2
      ⟨Set.mem_univ _, fun y _ h ↦ ?_⟩
    exact (lt_irrefl (0 : ℕ)) (h false)
  · intro h
    apply ((isParetoEfficient_iff _ _ _).1 h).2 true (Set.mem_univ _)
    apply (paretoImprovement_iff_lt project_represented).2
    exact Pi.lt_def.2 ⟨fun i ↦ by simp [projectPayoff], true, Nat.zero_lt_one⟩

/-- When adoption is unavailable, the status quo is Pareto efficient. -/
theorem statusQuo_isParetoEfficient_singleton :
    IsParetoEfficient projectPreference {false} false := by
  apply (isParetoEfficient_iff_maximal _ _ _).2
  simp only [Set.mem_singleton_iff, maximal_eq_iff]

/-- Counting only the beneficiary makes adoption a unanimous strict improvement. -/
theorem statusQuo_not_isWeaklyParetoEfficient_for_beneficiary :
    ¬ IsWeaklyParetoEfficient (fun _ : Unit ↦ projectPreference true) Set.univ false :=
  fun h ↦ h.2 true (Set.mem_univ _) fun _ ↦
    (project_represented true).lt_iff_lt.2 Nat.zero_lt_one

/-- Each household can shift its utility origin independently and recover the same efficient set. -/
theorem project_efficiency_shift (offset : Bool → ℕ) (F : Set Bool) (x : Bool) :
    IsParetoEfficient projectPreference F x ↔
      MaximalFor (· ∈ F) (fun y i ↦ projectPayoff i y + offset i) x :=
  isParetoEfficient_iff_maximalFor fun i ↦
    (project_represented i).comp_strictMono (g := fun n ↦ n + offset i)
      (fun _ _ h ↦ Nat.add_lt_add_right h _)

/-- Each household strictly prefers the project with its own label. -/
def opposingProjectRanking (i : Bool) : CompletePreference Bool :=
  CompletePreference.ofUtility fun x : Bool ↦ (if x = i then 1 else 0 : ℕ)

/-- With opposing rankings, both projects are efficient and neither is unanimously greatest. -/
theorem opposingProjects_isParetoEfficient_and_not_mem_maximizers (x : Bool) :
    IsParetoEfficient (fun i ↦ (opposingProjectRanking i).toPreference) Set.univ x ∧
      x ∉ Choice.maximizers (unanimousPreference (fun i ↦ (opposingProjectRanking i).toPreference))
        Set.univ := by
  have eq_of_unanimous {a b : Bool}
      (h : (unanimousPreference (fun i ↦ (opposingProjectRanking i).toPreference)).le a b) :
      a = b := by
    by_contra hne
    have ha := h a
    change (if a = a then 1 else 0 : ℕ) ≤ (if b = a then 1 else 0) at ha
    simp [Ne.symm hne] at ha
  constructor
  · refine ⟨Set.mem_univ _, fun y _ hxy ↦ ?_⟩
    rw [eq_of_unanimous hxy]
    exact (unanimousPreference _).le_rfl
  · intro h
    have heq := eq_of_unanimous (((Choice.mem_maximizers _).mp h).2 (!x) (Set.mem_univ _))
    cases x <;> contradiction

end PublicProject

section Bundles

/-- The first coordinate selects the good. The second labels the bundle. -/
def bundlePreference : Preference (Bool × Bool) :=
  Preference.ofUtility (fun x good ↦ if x.1 = good then 1 else 0 : _ → Bool → ℕ)

private theorem bundlePreference_le_iff (x y : Bool × Bool) :
    bundlePreference.le x y ↔ x.1 = y.1 := by
  constructor
  · intro h
    by_contra hne
    have hgood := h x.1
    change (if x.1 = x.1 then 1 else 0 : ℕ) ≤ (if y.1 = x.1 then 1 else 0) at hgood
    simp [Ne.symm hne] at hgood
  · intro h good
    change (if x.1 = good then 1 else 0 : ℕ) ≤ (if y.1 = good then 1 else 0)
    rw [h]

/-- Two labels for the same bundle tie. Bundles with different goods are incomparable. -/
theorem tied_labels_and_incomparable_goods :
    (false, false) ~[bundlePreference] (false, true) ∧
      ¬ bundlePreference.le (false, false) (true, false) ∧
      ¬ bundlePreference.le (true, false) (false, false) := by
  simp [AntisymmRel, bundlePreference_le_iff]

/-- Both goods, with either label, are Pareto efficient for this consumer. -/
theorem bundle_isParetoEfficient (x : Bool × Bool) :
    IsParetoEfficient (fun _ : Unit ↦ bundlePreference) Set.univ x := by
  apply (isParetoEfficient_iff _ _ _).2
  refine ⟨Set.mem_univ _, fun y _ h ↦ ?_⟩
  obtain ⟨i, hi⟩ := h.2
  exact hi.2 ((bundlePreference_le_iff y x).2 ((bundlePreference_le_iff x y).1 (h.1 i)).symm)

end Bundles

end MathEconLib.Welfare.Examples
