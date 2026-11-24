/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib
public import MathEconLibTest.GameTheory.CandidateValidity

/-!
# Candidate validity under explicit comparisons

Reuse the candidate-validity models to check the explicit-comparison API through the public
library umbrella. An invalid incumbent remains deviation-optimal, while an improving deviation
to an invalid target still excludes equilibrium. Representation and deviation restriction alone
do not repair mismatched candidate validity. Transport and pullback use the nontrivial validity
witnesses of the existing maps, without imposing validity on the deviation targets.
-/

@[expose] public section

open MathEconLib.GameTheory
open MathEconLibTest.GameTheory.CandidateValidity

namespace MathEconLibTest.GameTheory.ExplicitComparisonValidity

/-- With no deviations, even an invalid incumbent is optimal under arbitrary comparisons. -/
theorem invalid_isDeviationOptimalWith (R : Unit → Nat → Nat → Prop) :
    noDeviations.IsDeviationOptimalWith R false :=
  fun _ _ h ↦ h.elim

/-- Deviation optimality cannot certify equilibrium without candidate validity. -/
theorem invalid_not_isEquilibriumWith (R : Unit → Nat → Nat → Prop) :
    ¬ noDeviations.IsEquilibriumWith R false :=
  fun h ↦ Bool.false_ne_true h.valid

/-- No strict improvement is also insufficient at an invalid incumbent, even under comparability. -/
example :
    (∀ i t, noDeviations.deviation i false t →
      ¬ (noDeviations.value i false ≤ noDeviations.value i t ∧
        ¬ noDeviations.value i t ≤ noDeviations.value i false)) ∧
    ¬ noDeviations.IsEquilibriumWith (fun _ x y ↦ x ≤ y) false :=
  ⟨fun _ _ h ↦ h.elim, invalid_not_isEquilibriumWith _⟩

/-- The valid incumbent's improving deviation is admitted even though its target is invalid. -/
example : improvingDeviation.valid true ∧
    improvingDeviation.deviation () true false ∧ ¬ improvingDeviation.valid false :=
  ⟨rfl, ⟨rfl, rfl⟩, Bool.false_ne_true⟩

/-- Explicit comparisons must not filter admissible deviations by whole-profile target validity. -/
theorem improving_invalid_target_not_isEquilibriumWith :
    ¬ improvingDeviation.IsEquilibriumWith (fun _ x y ↦ x ≤ y) true := by
  intro h
  have hle : (1 : Nat) ≤ 0 := h.deviation_le () false ⟨rfl, rfl⟩
  exact Nat.not_succ_le_zero 0 hle

/-- Ordered recovery includes the validity of the source equilibrium. -/
theorem source_isEquilibriumWith :
    descendingSource.IsEquilibriumWith (fun _ x y ↦ x ≤ y) 2 :=
  (descendingSource.isEquilibriumWith_le_iff 2).2 source_isEquilibrium

/-- The explicit transport route uses the coarsening map's genuine validity-preservation proof. -/
theorem transport_equilibriumWith :
    descendingTarget.IsEquilibriumWith (fun _ x y ↦ x ≤ y) 1 :=
  coarseningMorphism.transportWith (fun _ x y ↦ x ≤ y) (fun _ x y ↦ x ≤ y)
    (fun _ _ _ _ h ↦ h) source_isEquilibriumWith

/-- The separate transport route needs only the admissible deviation comparisons. -/
example : descendingTarget.IsDeviationOptimalWith (fun _ x y ↦ x ≤ y) 1 :=
  coarseningMorphism.transport_isDeviationOptimalWith
    (fun _ x y ↦ x ≤ y) (fun _ x y ↦ x ≤ y)
    (fun _ _ _ _ h ↦ h) source_isEquilibriumWith.deviation_le

/-- Representation of the same rewards preserves deviation optimality despite stricter validity. -/
theorem stricter_isDeviationOptimalWith :
    stricterTarget.IsDeviationOptimalWith (fun _ x y ↦ x ≤ y) 1 :=
  (descendingTarget.isDeviationOptimalWith_iff_of_comparisons stricterTarget
    (fun _ x y ↦ x ≤ y) (fun _ x y ↦ x ≤ y)
    (fun _ _ _ ↦ Iff.rfl) (fun _ _ _ _ ↦ Iff.rfl) 1).1
      transport_equilibriumWith.deviation_le

/-- Equal rewards and deviation coverage cannot compensate for an invalid transported candidate. -/
theorem stricter_not_isEquilibriumWith :
    ¬ stricterTarget.IsEquilibriumWith (fun _ x y ↦ x ≤ y) 1 := by
  intro h
  have hv : 2 ≤ 1 := h.valid.2
  omega

/-- Deviation restriction alone also cannot carry full equilibrium into stricter validity. -/
example :
    (∀ i s t, stricterTarget.deviation i s t → descendingTarget.deviation i s t) ∧
    stricterTarget.value = descendingTarget.value ∧
    descendingTarget.IsEquilibriumWith (fun _ x y ↦ x ≤ y) 1 ∧
    ¬ stricterTarget.IsEquilibriumWith (fun _ x y ↦ x ≤ y) 1 :=
  ⟨fun _ _ _ h ↦ h, rfl, transport_equilibriumWith, stricter_not_isEquilibriumWith⟩

/-- The explicit pullback route uses the doubling map's nontrivial validity-reflection proof. -/
theorem pullback_equilibriumWith :
    descendingTarget.IsEquilibriumWith (fun _ x y ↦ x ≤ y) 1 :=
  doublingComorphism.pullbackWith (fun _ x y ↦ x ≤ y) (fun _ x y ↦ x ≤ y)
    (fun _ _ _ _ h ↦ h) source_isEquilibriumWith

/-- The separate pullback route transports deviation optimality. -/
example : descendingTarget.IsDeviationOptimalWith (fun _ x y ↦ x ≤ y) 1 :=
  doublingComorphism.pullback_isDeviationOptimalWith
    (fun _ x y ↦ x ≤ y) (fun _ x y ↦ x ≤ y)
    (fun _ _ _ _ h ↦ h) source_isEquilibriumWith.deviation_le

/-- Removing only candidate validity retains the same rewards and deviation relation. -/
def unrestricted : EquilibriumProblem Bool Unit Nat :=
  .ofDeviation noDeviations.deviation noDeviations.value

/-- An unrestricted candidate can be an equilibrium although its identical source is invalid. -/
example : unrestricted.IsEquilibriumWith (fun _ x y ↦ x ≤ y) false ∧
    ¬ noDeviations.IsEquilibriumWith (fun _ x y ↦ x ≤ y) false :=
  ⟨⟨trivial, invalid_isDeviationOptimalWith _⟩, invalid_not_isEquilibriumWith _⟩

/-- Identity preserves deviations and values, but cannot reflect the removed candidate guard. -/
example :
    (∀ i s t, noDeviations.deviation i s t → unrestricted.deviation i s t) ∧
    (∀ i s, unrestricted.value i s = noDeviations.value i s) ∧
    ¬ (∀ s, unrestricted.valid s → noDeviations.valid s) :=
  ⟨fun _ _ _ h ↦ h, fun _ _ ↦ rfl, fun h ↦ Bool.false_ne_true (h false trivial)⟩

end MathEconLibTest.GameTheory.ExplicitComparisonValidity

end
