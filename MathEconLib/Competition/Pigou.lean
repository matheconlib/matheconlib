/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import MathEconLib.Choice.Maximizers
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Pigouvian taxation of a production externality

Firms `i : I` choose nonnegative emission levels `e i`, with private benefit `benefit i`, and
the damage `damage` depends on total emissions. Under a fixed per-unit charge `τ`, each firm's
emission is a feasible maximizer (`Choice.maximizers`) of `benefit i x - τ * x` over `x ≥ 0`; the
charge is the same for every deviation. Welfare optimality is likewise membership in the
maximizers of welfare on the feasible profiles, so it asserts feasibility of the candidate.

The reusable step, `mem_welfareMaximizers_of_isTaxResponse`, needs no concavity: if the charge
supports the damage at the candidate total (`SupportsDamageAt`: the damage lies above the line
of slope `τ` through that total, on nonnegative totals), then a profile of optimal responses is
welfare maximizers. Under convexity, the derivative of the
damage within `Set.Ici 0` at the candidate total is such a charge
(`supportsDamageAt_of_hasDerivWithinAt`), which gives Pigou's rule `mem_welfareMaximizers_of_pigou`.
The boundary case of zero total emissions is covered by taking the derivative within `Set.Ici 0`.

This module does not prove the converse (a welfare maximum is a response to the marginal
damage), nor anything about permits or uncertainty; see #356.

## References

A. C. Pigou (1932), *The Economics of Welfare*, 4th ed., Macmillan, Part II, ch. IX,
« Divergences between marginal social net product and marginal private net product »
(1st ed. 1920), <https://www.econlib.org/library/NPDBooks/Pigou/pgEW.html>. Pigou argues in
terms of marginal net products; the support formulation and the convexity hypothesis here are
this module's.
-/

@[expose] public noncomputable section

namespace MathEconLib.Competition.Pigou

open Finset Set MathEconLib.Choice MathEconLib.Preferences

/-- Firms with private benefits from emissions, and a damage depending on total emissions. -/
structure ExternalityProblem (I : Type*) where
  /-- Private benefit of firm `i` from emitting `x`. -/
  benefit : I → ℝ → ℝ
  /-- Social damage of total emissions. -/
  damage : ℝ → ℝ

/-- Feasible emission profiles: every firm emits a nonnegative amount. -/
def feasibleProfiles (I : Type*) : Set (I → ℝ) := {e | ∀ i, 0 ≤ e i}

variable {I : Type*} [Fintype I] (P : ExternalityProblem I)

namespace ExternalityProblem

/-- Welfare: total private benefit minus the damage of total emissions. -/
def welfare (e : I → ℝ) : ℝ :=
  ∑ i, P.benefit i (e i) - P.damage (∑ i, e i)

/-- Every firm's emission is a feasible maximizer of its benefit net of the charge `τ`. -/
def IsTaxResponse (τ : ℝ) (e : I → ℝ) : Prop :=
  ∀ i, e i ∈ maximizers (Preference.ofUtility fun x => P.benefit i x - τ * x) (Ici 0)

/-- Welfare-maximizing profiles: feasible profiles with the greatest welfare. -/
def welfareMaximizers : Set (I → ℝ) :=
  maximizers (Preference.ofUtility P.welfare) (feasibleProfiles I)

/-- The charge `τ` supports the damage at total `S`: on nonnegative totals, the damage lies above
the line of slope `τ` through `(S, damage S)`. -/
def SupportsDamageAt (τ S : ℝ) : Prop :=
  ∀ T, 0 ≤ T → P.damage S + τ * (T - S) ≤ P.damage T

variable {P}

omit [Fintype I] in
theorem IsTaxResponse.mem_feasible {τ : ℝ} {e : I → ℝ} (h : P.IsTaxResponse τ e) :
    e ∈ feasibleProfiles I :=
  fun i => ((mem_maximizers_ofUtility _).1 (h i)).1

omit [Fintype I] in
theorem IsTaxResponse.isMaxOn {τ : ℝ} {e : I → ℝ} (h : P.IsTaxResponse τ e) (i : I) :
    IsMaxOn (fun x => P.benefit i x - τ * x) (Ici 0) (e i) :=
  ((mem_maximizers_ofUtility _).1 (h i)).2

/-- Optimal responses to a charge that supports the damage at their total are feasible and
maximise welfare over feasible profiles. No concavity or differentiability is needed. -/
theorem mem_welfareMaximizers_of_isTaxResponse {τ : ℝ} {e : I → ℝ} (h : P.IsTaxResponse τ e)
    (hs : P.SupportsDamageAt τ (∑ i, e i)) :
    e ∈ P.welfareMaximizers := by
  refine (mem_maximizers_ofUtility _).2 ⟨IsTaxResponse.mem_feasible h, fun e' he' => ?_⟩
  have hB := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => IsTaxResponse.isMaxOn h i (he' i)
  simp only [sum_sub_distrib, ← mul_sum] at hB
  have := hs (∑ i, e' i) (sum_nonneg fun i _ => he' i)
  change P.welfare e' ≤ P.welfare e
  unfold welfare
  linarith

omit [Fintype I] in
/-- A convex damage, with derivative `τ` within `Set.Ici 0` at a nonnegative total `S`, is
supported at `S` by the charge `τ`. -/
theorem supportsDamageAt_of_hasDerivWithinAt {τ S : ℝ} (hD : ConvexOn ℝ (Ici 0) P.damage)
    (hS : 0 ≤ S) (hd : HasDerivWithinAt P.damage τ (Ici 0) S) : P.SupportsDamageAt τ S := by
  intro T hT
  rcases lt_trichotomy S T with hST | rfl | hTS
  · have := hD.le_slope_of_hasDerivWithinAt hS hT hST hd
    rw [slope_def_field, le_div_iff₀ (sub_pos.2 hST)] at this
    linarith
  · simp
  · have := hD.slope_le_of_hasDerivWithinAt hT hS hTS hd
    rw [slope_def_field, div_le_iff₀ (sub_pos.2 hTS)] at this
    linarith

/-- **Pigou's rule.** With a convex damage, differentiable within `Set.Ici 0` at the candidate
total, optimal responses to a charge equal to the marginal damage at that total are feasible and
maximise welfare. -/
theorem mem_welfareMaximizers_of_pigou {e : I → ℝ} (hD : ConvexOn ℝ (Ici 0) P.damage)
    (hd : DifferentiableWithinAt ℝ P.damage (Ici 0) (∑ i, e i))
    (h : P.IsTaxResponse (derivWithin P.damage (Ici 0) (∑ i, e i)) e) :
    e ∈ P.welfareMaximizers :=
  mem_welfareMaximizers_of_isTaxResponse h <|
    supportsDamageAt_of_hasDerivWithinAt hD
      (sum_nonneg fun i _ => IsTaxResponse.mem_feasible h i) hd.hasDerivWithinAt

end ExternalityProblem

end MathEconLib.Competition.Pigou
