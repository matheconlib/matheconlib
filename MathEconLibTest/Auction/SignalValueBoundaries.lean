/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Auction.Affiliation.Basic

/-!
# Signal-value environment boundary cases

A `SignalValueEnv` can have identically zero signal weights, whose integral is zero.
The companion `SignalWeights` tests cover algebraic factorization and affiliation.
See docs/SemanticAudit.md for the findings and the full historical evidence archive.
-/

@[expose] public noncomputable section

open MeasureTheory
open MathEconLib
open MathEconLib.Auction.Affiliation

namespace MathEconLibTest.SignalValueBoundaries

noncomputable def zeroDensityEnv : SignalValueEnv 1 where
  x_lo := 0
  x_hi := 1
  x_lo_le_hi := by norm_num
  f := fun _ ↦ 0
  f_nonneg := fun _ ↦ le_rfl
  f_support := fun _ _ ↦ rfl
  v := fun i X ↦ Real.exp (X i)
  v_nonneg := fun _ _ ↦ (Real.exp_pos _).le
  v_continuous := fun i ↦ Real.continuous_exp.comp (continuous_apply i)
  v_mono := fun i X Y h ↦ Real.exp_le_exp.mpr (h i)
  v_strictMono_own := by
    intro i X a _ b _ hab
    simpa only [Function.update_self] using Real.exp_strictMono hab

theorem zeroDensityEnv_mass :
    (∫ X : Fin 1 → ℝ, zeroDensityEnv.f X) = 0 := by
  simp [zeroDensityEnv]

end MathEconLibTest.SignalValueBoundaries
