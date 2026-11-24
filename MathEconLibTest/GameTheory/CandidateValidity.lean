/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import MathEconLib.GameTheory.Equilibrium.Problem
public import Mathlib.Data.Nat.Basic

/-!
# Candidate validity and admissible deviations

Boolean states distinguish candidate validity from deviation optimality. Invalid incumbents are
excluded even when no deviations are admitted, while improving deviations exclude valid incumbents
even when the target is invalid. Natural-number states admit downward deviations with decreasing
values. Coarsening states by division by two transports equilibrium when validity is preserved;
strengthening target validity alone can reject the image. Refinement excludes equilibrium state one
while retaining equilibrium state two. Doubling states reflects validity and allows equilibrium to
pull back.

## Main definitions

* `noDeviations`: Only the state `true` is valid, and no deviations are admitted.
* `improvingDeviation`: A valid incumbent admits an improving deviation to an invalid target.
* `descendingSource`, `descendingTarget`: Downward deviations with nonconstant candidate validity.
* `coarseningMorphism`: Division by two lifts target deviations and preserves validity.
* `stricterTarget`: The target refined to require candidate states at least two.
* `doublingComorphism`: Doubling maps deviations and reflects validity.

## Main statements

* `invalid_isDeviationOptimal`, `invalid_not_isEquilibrium`: Deviation optimality alone does not
  make an invalid incumbent an equilibrium.
* `improving_invalid_target_not_isEquilibrium`: Invalid targets can rule out equilibrium.
* `source_isEquilibrium`, `transport_equilibrium`: Coarsening transports a directly proved
  equilibrium with admissible deviations.
* `coarsening_lifts_stricterTarget`, `coarsening_value_eq_stricterTarget`: Strengthening target
  validity retains deviation lifting and reward agreement.
* `stricterTarget_not_isEquilibrium`: Those two properties alone do not transport equilibrium.
* `stricterTarget_isEquilibrium`: The refinement retains equilibrium state two.
* `pullback_equilibrium`: Doubling pulls equilibrium back with nontrivial validity and deviations.

## Tags

equilibrium, candidate validity, deviations, transport
-/

@[expose] public section

open MathEconLib.GameTheory

namespace MathEconLibTest.GameTheory.CandidateValidity

/-- Only `true` is a valid incumbent, and neither state admits a deviation. -/
def noDeviations : EquilibriumProblem Bool Unit Nat where
  deviation _ _ _ := False
  value _ _ := 0
  valid s := s = true

/-- The invalid state satisfies all admissible-deviation inequalities. -/
theorem invalid_isDeviationOptimal : noDeviations.IsDeviationOptimal false :=
  fun _ _ h => h.elim

/-- An invalid incumbent is not an equilibrium even when no deviations are admitted. -/
theorem invalid_not_isEquilibrium : ¬ noDeviations.IsEquilibrium false :=
  fun h => Bool.false_ne_true h.valid

/-- The valid state admits an improving deviation to the invalid state `false`. -/
def improvingDeviation : EquilibriumProblem Bool Unit Nat where
  deviation _ s t := s = true ∧ t = false
  value _ s := if s then 0 else 1
  valid s := s = true

/-- Improving deviations are compared even when their targets are invalid incumbents. -/
theorem improving_invalid_target_not_isEquilibrium :
    ¬ improvingDeviation.IsEquilibrium true := by
  intro h
  have hle : (1 : Nat) ≤ 0 := h.deviation_le () false ⟨rfl, rfl⟩
  exact Nat.not_succ_le_zero 0 hle

/-- States at least two are valid; deviations lower the state and values are half the state. -/
def descendingSource : EquilibriumProblem ℕ Unit ℕ where
  deviation _ s t := t < s
  value _ s := s / 2
  valid s := 2 ≤ s

/-- Positive states are valid; deviations lower the state and values equal the state. -/
def descendingTarget : EquilibriumProblem ℕ Unit ℕ where
  deviation _ s t := t < s
  value _ s := s
  valid s := 1 ≤ s

/-- State two is a valid source candidate and every downward deviation weakly lowers its value. -/
theorem source_isEquilibrium : descendingSource.IsEquilibrium 2 := by
  refine ⟨Nat.le_refl 2, ?_⟩
  intro _ t ht
  change t < 2 at ht
  change t / 2 ≤ 2 / 2
  omega

/-- Division by two preserves validity and lifts each target deviation to twice its state. -/
def coarseningMorphism : GameMorphism descendingSource descendingTarget where
  toFun s := s / 2
  deviatorMap := id
  deviation_lifts _ s t ht := by
    change t < s / 2 at ht
    refine ⟨2 * t, ?_, ?_⟩
    · change 2 * t < s
      omega
    · omega
  value_eq _ _ := rfl
  valid_preserves s hs := by
    change 2 ≤ s at hs
    change 1 ≤ s / 2
    omega

/-- Coarsening transports the source equilibrium to the concrete target state one. -/
theorem transport_equilibrium : descendingTarget.IsEquilibrium 1 :=
  coarseningMorphism.transport source_isEquilibrium

/-- Target rewards and deviations with candidate validity requiring states at least two. -/
def stricterTarget : EquilibriumProblem ℕ Unit ℕ :=
  descendingTarget.refine (fun s => 2 ≤ s)

/-- Coarsening still lifts deviations when the target's candidate validity is strengthened. -/
theorem coarsening_lifts_stricterTarget (i : Unit) (s t : ℕ)
    (ht : stricterTarget.deviation i (coarseningMorphism.toFun s) t) :
    ∃ s', descendingSource.deviation i s s' ∧ coarseningMorphism.toFun s' = t :=
  coarseningMorphism.deviation_lifts i s t ht

/-- Coarsening still preserves values when the target's candidate validity is strengthened. -/
theorem coarsening_value_eq_stricterTarget (i : Unit) (s : ℕ) :
    stricterTarget.value i (coarseningMorphism.toFun s) = descendingSource.value i s := rfl

/-- Deviation lifting and reward agreement do not transport equilibrium to an invalid image. -/
theorem stricterTarget_not_isEquilibrium :
    ¬ stricterTarget.IsEquilibrium (coarseningMorphism.toFun 2) := by
  intro h
  have hv : 2 ≤ 1 := h.valid.2
  omega

/-- Refinement retains state two, which is an equilibrium satisfying the added condition. -/
theorem stricterTarget_isEquilibrium : stricterTarget.IsEquilibrium 2 := by
  rw [stricterTarget, EquilibriumProblem.isEquilibrium_refine_iff]
  refine ⟨⟨show 1 ≤ 2 by decide, ?_⟩, by decide⟩
  intro _ t ht
  exact Nat.le_of_lt ht

/-- Doubling preserves downward deviations and reflects the source problem's validity. -/
def doublingComorphism : GameComorphism descendingTarget descendingSource where
  toFun s := 2 * s
  deviatorMap := id
  deviation_maps _ s t ht := by
    change t < s at ht
    change 2 * t < 2 * s
    omega
  value_eq _ s := by
    change 2 * s / 2 = s
    omega
  valid_reflects s hs := by
    change 2 ≤ 2 * s at hs
    change 1 ≤ s
    omega

/-- The equilibrium at state two pulls back along doubling to the valid state one. -/
theorem pullback_equilibrium : descendingTarget.IsEquilibrium 1 :=
  doublingComorphism.pullback source_isEquilibrium

end MathEconLibTest.GameTheory.CandidateValidity

end
