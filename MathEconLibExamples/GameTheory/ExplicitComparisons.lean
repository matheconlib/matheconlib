/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.GameTheory.Equilibrium.Problem

/-!
# Explicit preferences on two alternatives

One agent can select either Boolean alternative and weakly prefers `true`. Exact numerical
representation preserves equilibrium. Forgetting an irrelevant tag transports equilibrium, and
restricting deviations pulls it back. Restriction can also create an equilibrium.

Equality is an incomplete comparison between the two alternatives: no strict improvement exists,
but the agent is not weakly optimal. This controls the comparability hypothesis of the converse.
-/

@[expose] public section

open MathEconLib.GameTheory

namespace MathEconLibExamples.GameTheory.ExplicitComparisons

/-- Every alternative is an admissible deviation for the single agent. -/
def problem : EquilibriumProblem Bool Unit Bool where
  deviation _ _ _ := True
  value _ s := s

/-- The agent prefers `true` to `false`, allowing indifference to itself. -/
def prefersTrue (_ : Unit) (x y : Bool) : Prop := x = false ∨ y = true

/-- Choosing the preferred alternative is an ordinal equilibrium. -/
theorem true_isEquilibriumWith : problem.IsEquilibriumWith prefersTrue true :=
  fun _ _ _ ↦ Or.inr rfl

/-- The selected comparison is complete on these two alternatives. -/
theorem prefersTrue_total (s t : Bool) : prefersTrue () s t ∨ prefersTrue () t s := by
  cases s <;> cases t <;> simp [prefersTrue]

/-- Comparability justifies the converse from no strict improvement for this client. -/
theorem equilibrium_iff_no_strictImprovement (s : Bool) :
    problem.IsEquilibriumWith prefersTrue s ↔ ∀ i t, problem.deviation i s t →
      ¬ (prefersTrue i s t ∧ ¬ prefersTrue i t s) :=
  problem.isEquilibriumWith_iff_no_strictImprovement prefersTrue s
    (fun _ t _ ↦ prefersTrue_total t s)

/-- The same deviations evaluated by the numerical representation `false ↦ 0`, `true ↦ 1`. -/
def numericalProblem : EquilibriumProblem Bool Unit Nat where
  deviation _ _ _ := True
  value _ s := if s then 1 else 0

/-- The numerical representation agrees exactly with every ordinal comparison. -/
theorem prefersTrue_iff_le (i : Unit) (s t : Bool) :
    prefersTrue i s t ↔ numericalProblem.value i s ≤ numericalProblem.value i t := by
  cases s <;> cases t <;> simp [prefersTrue, numericalProblem]

/-- Applying the shared representation theorem preserves equilibrium in both directions. -/
theorem equilibrium_iff_numerical (s : Bool) :
    problem.IsEquilibriumWith prefersTrue s ↔
      numericalProblem.IsEquilibriumWith (fun _ x y ↦ x ≤ y) s :=
  problem.isEquilibriumWith_iff_of_comparisons numericalProblem prefersTrue
    (fun _ x y ↦ x ≤ y) (fun _ _ _ ↦ Iff.rfl)
    (fun i s t _ ↦ prefersTrue_iff_le i t s) s

/-- Exact representation and ordered recovery give the existing numerical equilibrium notion. -/
theorem true_isEquilibrium : numericalProblem.IsEquilibrium true :=
  (numericalProblem.isEquilibriumWith_le_iff true).1
    ((equilibrium_iff_numerical true).1 true_isEquilibriumWith)

/-- Numerical evaluation rejects the inferior alternative. -/
theorem false_not_isEquilibrium : ¬ numericalProblem.IsEquilibrium false :=
  fun h ↦ (by decide : ¬ (1 : Nat) ≤ 0) (h () true trivial)

/-- An irrelevant Boolean tag leaves the chosen consequence unchanged. -/
def taggedProblem : EquilibriumProblem (Bool × Bool) Unit Bool where
  deviation _ _ _ := True
  value _ s := s.1

/-- Every untagged deviation has a tagged lift; tags need not be recovered uniquely. -/
def forgetTag : GameMorphism taggedProblem problem where
  toFun := Prod.fst
  deviatorMap := id
  deviation_lifts _ s t _ := ⟨(t, s.2), trivial, rfl⟩
  value_eq _ _ := rfl

/-- The tagged preferred alternative is optimal irrespective of the irrelevant tag. -/
theorem tagged_true_isEquilibriumWith (tag : Bool) :
    taggedProblem.IsEquilibriumWith prefersTrue (true, tag) :=
  fun _ _ _ ↦ Or.inr rfl

/-- Apply the existing deviation-lifting morphism with explicit comparison preservation. -/
theorem true_isEquilibriumWith_of_transport : problem.IsEquilibriumWith prefersTrue true :=
  forgetTag.transportWith prefersTrue prefersTrue (fun _ _ _ _ h ↦ h)
    (tagged_true_isEquilibriumWith false)

/-- A restricted problem admits only deviations that leave the current alternative unchanged. -/
def restrictedProblem : EquilibriumProblem Bool Unit Bool where
  deviation _ s t := s = t
  value _ s := s

/-- Restricted deviations are also available in the original problem. -/
def restriction : GameComorphism restrictedProblem problem where
  toFun := id
  deviatorMap := id
  deviation_maps _ _ _ _ := trivial
  value_eq _ _ := rfl

/-- Apply comparison-aware pullback through the existing deviation-preserving map. -/
theorem restricted_true_isEquilibriumWith :
    restrictedProblem.IsEquilibriumWith prefersTrue true :=
  restriction.pullbackWith prefersTrue prefersTrue (fun _ _ _ _ h ↦ h)
    true_isEquilibriumWith

/-- The deviation-subset theorem gives the same restricted equilibrium directly. -/
theorem restricted_true_isEquilibriumWith_of_subset :
    restrictedProblem.IsEquilibriumWith prefersTrue true :=
  true_isEquilibriumWith.of_deviation_subset (fun _ _ _ _ ↦ trivial) rfl

/-- Restriction creates an equilibrium at `false`, although it fails in the numerical original. -/
theorem restricted_false_isEquilibriumWith :
    restrictedProblem.IsEquilibriumWith prefersTrue false :=
  fun _ _ ht ↦ Or.inl ht.symm

/-- Equality has no asymmetric strict improvement, even between distinct alternatives. -/
theorem equality_no_strictImprovement (s : Bool) :
    ∀ i t, problem.deviation i s t →
      ¬ (problem.value i s = problem.value i t ∧
        ¬ problem.value i t = problem.value i s) :=
  fun _ _ _ h ↦ h.2 h.1.symm

/-- Absence of a strict improvement does not imply weak equilibrium for incomplete comparisons. -/
theorem equality_not_isEquilibriumWith :
    ¬ problem.IsEquilibriumWith (fun _ x y ↦ x = y) false :=
  fun h ↦ Bool.noConfusion (h () true trivial)

end MathEconLibExamples.GameTheory.ExplicitComparisons

end
