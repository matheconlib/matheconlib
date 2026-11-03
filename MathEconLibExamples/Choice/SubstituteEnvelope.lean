/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
module

public import MathEconLib.Choice

/-!
# Concrete substitute-envelope applications

Two contracts share one counterparty, and a unit-demand rule prefers `true` to
`false`. Both singleton menus are accepted, so both envelopes select every
available contract. They are completions despite selecting two contracts at the
full menu. The sandwich and greatestness results apply to this strict enlargement.

A second rule accepts two contracts only together. With distinct counterparties,
its singleton rejections give a certificate ruling out every substitutable
completion. No finite computation oracle is used.
-/

@[expose] public section

open MathEconLib.Choice MathEconLib.Choice.ChoiceFunction

namespace MathEconLib.Examples.Choice.SubstituteEnvelope

noncomputable def priority : ChoiceFunction Bool := by
  classical
  exact {
    toFun := fun Y => if true ∈ Y then {true} else Y
    choose_subset := by
      intro Y x hx
      by_cases h : true ∈ Y
      · rw [ite_eq_left h] at hx
        rw [Set.mem_singleton_iff.mp hx]
        exact h
      · simpa only [ite_eq_right h] using hx }

def allChoice : ChoiceFunction Bool where
  toFun Y := Y
  choose_subset := fun _ => Set.Subset.rfl

def partner (_ : Bool) : Unit := ()

theorem priority_apply_of_mem {Y : Set Bool} (h : true ∈ Y) : priority Y = {true} := by
  classical
  change (if true ∈ Y then {true} else Y) = {true}
  exact ite_eq_left h

theorem priority_apply_of_not_mem {Y : Set Bool} (h : true ∉ Y) : priority Y = Y := by
  classical
  change (if true ∈ Y then {true} else Y) = Y
  exact ite_eq_right h

theorem priority_pathIndependent : priority.PathIndependent := by
  intro Y Z
  by_cases hY : true ∈ Y
  · rw [priority_apply_of_mem hY,
      priority_apply_of_mem (Set.mem_union_left Z hY),
      priority_apply_of_mem (Set.mem_union_left Z (Set.mem_singleton true))]
  · rw [priority_apply_of_not_mem hY]

theorem allChoice_pathIndependent : allChoice.PathIndependent := fun _ _ => rfl

theorem priority_singleton (x : Bool) : priority {x} = {x} := by
  cases x
  · exact priority_apply_of_not_mem (by simp)
  · exact priority_apply_of_mem (Set.mem_singleton true)

/-- Feasible sub-menus containing a given contract are its singleton menu. -/
theorem envelope_eq_allChoice : substituteEnvelope partner priority = allChoice := by
  apply ChoiceFunction.ext
  intro Y
  ext x
  constructor
  · exact fun hx => hx.1
  · intro hx
    refine ⟨hx, ?_⟩
    intro V _ hfeas hxV
    have hV : V = {x} := by
      ext y
      constructor
      · intro hy
        exact Set.mem_singleton_iff.mpr (hfeas hy hxV rfl)
      · intro hy
        simpa only [Set.mem_singleton_iff.mp hy] using hxV
    rw [hV, priority_singleton]
    exact Set.mem_singleton x

theorem pathEnvelope_eq_allChoice : pathIndependentEnvelope partner priority = allChoice := by
  unfold pathIndependentEnvelope
  rw [envelope_eq_allChoice]
  exact allChoice_pathIndependent.pathIndependentMinorant_eq

/-- Apply the named sandwich theorem to a completion strictly enlarging priority choice. -/
theorem allChoice_completion : priority.IsCompletionOf partner allChoice := by
  apply ((enlarging_substitutable_completion_iff_sandwich
    (counterparty := partner) (D := allChoice) priority_pathIndependent.consistent).2 ?_).1
  refine ⟨allChoice_pathIndependent.substitutable, ?_, ?_⟩
  · exact substituteHull_le allChoice_pathIndependent.substitutable priority.choose_subset
  · rw [envelope_eq_allChoice]

theorem priority_completable : priority.HasConsistentSubstitutableCompletion partner :=
  ⟨allChoice, allChoice_completion, allChoice_pathIndependent.substitutable,
    allChoice_pathIndependent.consistent⟩

/-- The canonical envelope theorem identifies the greatest substitutable completion. -/
theorem allChoice_greatest :
    IsGreatest {D : ChoiceFunction Bool | priority.IsCompletionOf partner D ∧ D.Substitutable}
      allChoice := by
  rw [← envelope_eq_allChoice]
  exact isGreatest_substituteEnvelope priority_pathIndependent.consistent
    priority_completable.substitutablyCompletable

/-- The consistent-completion theorem gives the same greatest choice here. -/
theorem allChoice_greatest_consistent :
    IsGreatest {D : ChoiceFunction Bool |
      priority.IsCompletionOf partner D ∧ D.Substitutable ∧ D.Consistent} allChoice := by
  rw [← pathEnvelope_eq_allChoice]
  exact isGreatest_pathIndependentEnvelope priority_pathIndependent.consistent priority_completable

theorem priority_rejectionEvidence : priority.RejectionEvidence partner :=
  (substitutablyCompletable_iff_rejectionEvidence priority_pathIndependent.consistent).1
    priority_completable.substitutablyCompletable

/-- The completion adds the lower-ranked contract at the full menu. -/
theorem strict_enlargement : false ∈ allChoice Set.univ ∧ false ∉ priority Set.univ := by
  change false ∈ (Set.univ : Set Bool) ∧ false ∉ priority Set.univ
  rw [priority_apply_of_mem (Set.mem_univ true)]
  simp

/-- Complementary contracts are chosen only when both are available. -/
noncomputable def complements : ChoiceFunction Bool := by
  classical
  exact {
    toFun := fun Y => if false ∈ Y ∧ true ∈ Y then Y else ∅
    choose_subset := by
      intro Y
      split_ifs
      · exact Set.Subset.rfl
      · exact Set.empty_subset Y }

/-- One singleton rejection certifies failure of substitutable completability. -/
theorem complements_not_completable : ¬ complements.SubstitutablyCompletable id := by
  classical
  apply not_substitutablyCompletable_of_rejectionEvidence
    (Y := Set.univ) (R := {true}) (x := true)
  · intro x hx
    have he : x = true := Set.mem_singleton_iff.mp hx
    subst x
    refine ⟨{true}, Set.subset_univ _, ?_, ?_⟩
    · exact fun _ _ _ _ h => h
    · change true ∈ ({true} : Set Bool) ∧
        true ∉ (if false ∈ ({true} : Set Bool) ∧ true ∈ ({true} : Set Bool)
          then ({true} : Set Bool) else ∅)
      simp
  · exact fun _ _ _ _ h => h
  · change true ∈ (if false ∈ (Set.univ : Set Bool) ∧ true ∈ (Set.univ : Set Bool)
        then (Set.univ : Set Bool) else ∅)
    simp
  · exact Set.mem_singleton true

end MathEconLib.Examples.Choice.SubstituteEnvelope
