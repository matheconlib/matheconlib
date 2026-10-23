/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Auction.Typeclasses
public import MathEconLib.Auction.Affiliation.Basic

/-!
# Supporting lemmas for the 23 October 2026 semantic audit

These twelve statements preserve the original supporting proof content at audit revision
1d9f8cc233cdaeee0364b51befb84feea657a4da. They certify the zero-density environment,
the global strict-positivity obstruction and real arithmetic. They do not certify every
complete probabilistic countermodel or the future repaired signal interfaces. See the audit
record under docs/audits/2026-10-23-semantic and issue #218.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open MathEconLib
open MathEconLib.Auction.Affiliation

namespace MathEconLibTest.SemanticAudit

noncomputable def zeroDensityEnv : SignalValueEnv 1 where
  x_lo := 0
  x_hi := 1
  x_lo_le_hi := by norm_num
  f := fun _ ↦ 0
  f_nonneg := fun _ ↦ le_rfl
  f_support := fun _ _ => rfl
  v := fun i X ↦ Real.exp (X i)
  v_nonneg := fun _ _ => (Real.exp_pos _).le
  v_continuous := fun i => Real.continuous_exp.comp (continuous_apply i)
  v_mono := fun i X Y h => Real.exp_le_exp.mpr (h i)
  v_strictMono_own := by
    intro i X s t h
    simpa using Real.exp_strictMono h

theorem zeroDensityEnv_private : IsPrivateValues zeroDensityEnv := by
  intro i X Y h
  simpa only [zeroDensityEnv] using congrArg Real.exp h

theorem zeroDensityEnv_independent : HasIndependentSignals zeroDensityEnv := by
  refine ⟨fun _ _ => 0, ?_⟩
  intro X
  simp [zeroDensityEnv]

theorem zeroDensityEnv_ipv : IsIPV zeroDensityEnv :=
  ⟨zeroDensityEnv_private, zeroDensityEnv_independent⟩

theorem zeroDensityEnv_affiliated : HasAffiliatedSignals zeroDensityEnv :=
  zeroDensityEnv_independent.hasAffiliatedSignals

theorem zeroDensityEnv_mass :
    (∫ X : Fin 1 → ℝ, zeroDensityEnv.f X) = 0 := by
  simp [zeroDensityEnv]

-- The global fields force strictly positive values everywhere, including lower endpoints.
theorem all_values_strictly_positive {n : ℕ} (E : SignalValueEnv n)
    (i : Fin n) (X : Fin n → ℝ) : 0 < E.v i X := by
  have h := E.v_strictMono_own i X (sub_lt_self (X i) zero_lt_one)
  have hn := E.v_nonneg i (Function.update X i (X i - 1))
  have hu : Function.update X i (X i) = X := by ext j; by_cases hj : j = i <;> simp [hj]
  change E.v i (Function.update X i (X i - 1)) < E.v i (Function.update X i (X i)) at h
  rw [hu] at h
  exact lt_of_le_of_lt hn h

theorem cannot_represent_uniform_value_at_zero (E : SignalValueEnv 1) :
    E.v 0 (fun _ ↦ 0) ≠ 0 :=
  ne_of_gt (all_values_strictly_positive E 0 (fun _ ↦ 0))

-- Exact real identities establish the continuum-report part, without a bid grid.
theorem correlated_fp_marginal_payment (b : ℝ) :
    ((2 * (0 : ℝ) - 1) * b + (2 * (1 : ℝ) - 1) * b) / 2 = 0 := by ring

theorem correlated_fn_marginal_payment (b : ℝ) :
    ((b - (0 : ℝ)) ^ 2 + (b - (1 : ℝ)) ^ 2) / 2 = b ^ 2 - b + 1 / 2 := by ring

theorem correlated_fn_truth_optimal (s b : ℝ) :
    -(b - s) ^ 2 ≤ -(s - s) ^ 2 := by nlinarith [sq_nonneg (b - s)]

theorem correlated_fn_formal_deviation :
    -((0 : ℝ)^2 - 0 + 1 / 2) < -((1 / 2 : ℝ)^2 - 1 / 2 + 1 / 2) := by norm_num

theorem correlated_revenue_mismatch :
    (((0 : ℝ) * 0 + 1 * 1) / 2) = 1 / 2 ∧
    (((0 : ℝ) / 2 + 1 / 2) / 2) = 1 / 4 ∧ (1 / 4 : ℝ) ≠ 1 / 2 := by norm_num

end MathEconLibTest.SemanticAudit
