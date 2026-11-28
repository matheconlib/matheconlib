/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
import MathEconLib

/-! Pins of the Pigou statements through the umbrella import, and a checked example. -/

open Set MathEconLib.Competition.Pigou

namespace MathEconLibTest.Competition.Pigou

/-! ## Pinned statements -/

example {I : Type*} [Fintype I] {P : ExternalityProblem I} {τ : ℝ} {e : I → ℝ}
    (h : P.IsTaxResponse τ e) (hs : P.SupportsDamageAt τ (∑ i, e i)) :
    e ∈ P.welfareMaximizers :=
  ExternalityProblem.mem_welfareMaximizers_of_isTaxResponse h hs

example {I : Type*} {P : ExternalityProblem I} {τ S : ℝ} (hD : ConvexOn ℝ (Ici 0) P.damage)
    (hS : 0 ≤ S) (hd : HasDerivWithinAt P.damage τ (Ici 0) S) : P.SupportsDamageAt τ S :=
  ExternalityProblem.supportsDamageAt_of_hasDerivWithinAt hD hS hd

example {I : Type*} [Fintype I] {P : ExternalityProblem I} {e : I → ℝ}
    (hD : ConvexOn ℝ (Ici 0) P.damage)
    (hd : DifferentiableWithinAt ℝ P.damage (Ici 0) (∑ i, e i))
    (h : P.IsTaxResponse (derivWithin P.damage (Ici 0) (∑ i, e i)) e) :
    e ∈ P.welfareMaximizers :=
  ExternalityProblem.mem_welfareMaximizers_of_pigou hD hd h

/-! ## A firm at zero emissions

Two firms, linear damage `D T = T`, so the marginal damage is `1` everywhere. Firm `0` has benefit
`2x - x² / 2` and emits `1`; firm `1` has benefit `x / 2`, below the charge, and emits `0`.
-/

/-- The example problem. -/
noncomputable def example₂ : ExternalityProblem (Fin 2) where
  benefit i x := if i = 0 then 2 * x - x ^ 2 / 2 else x / 2
  damage T := T

theorem derivWithin_damage {S : ℝ} (hS : 0 ≤ S) : derivWithin example₂.damage (Ici 0) S = 1 :=
  (hasDerivWithinAt_id S (Ici 0)).derivWithin (uniqueDiffOn_Ici 0 S hS)

theorem isTaxResponse_example₂ : example₂.IsTaxResponse 1 ![1, 0] := by
  intro i
  rw [MathEconLib.Choice.mem_maximizers_ofUtility]
  fin_cases i
  · refine ⟨by norm_num, fun x _ => ?_⟩
    simp only [example₂]
    norm_num
    nlinarith [sq_nonneg (x - 1)]
  · refine ⟨by norm_num, fun x (hx : (0 : ℝ) ≤ x) => ?_⟩
    simp only [example₂]
    norm_num
    linarith

/-- Pigou's rule applies, with firm `1` at the boundary of its feasible set. -/
example : ![(1 : ℝ), 0] ∈ example₂.welfareMaximizers := by
  refine ExternalityProblem.mem_welfareMaximizers_of_pigou ?_ ?_ ?_
  · exact convexOn_id (convex_Ici 0)
  · exact differentiableWithinAt_id
  · rw [derivWithin_damage (by simp [Fin.sum_univ_two])]
    exact isTaxResponse_example₂

#print axioms ExternalityProblem.mem_welfareMaximizers_of_pigou

end MathEconLibTest.Competition.Pigou
