/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Auction.Affiliation.WinnersCurse

/-!
# Bounded private values in a signal/value environment

Independent uniform signals on `[0, 1]` have values equal to their own signals on
the declared box. Clamping the values outside the interval preserves global
nonnegativity, continuity and monotonicity, but not global strict monotonicity.
-/

@[expose] public noncomputable section

open MathEconLib Auction.Affiliation Set

namespace MathEconLibTest.SignalValueEnv

/-- Independent unit-interval signals with bounded private values. -/
def environment (n : ℕ) : SignalValueEnv n where
  x_lo := 0
  x_hi := 1
  x_lo_le_hi := by norm_num
  f := fun X ↦ ∏ i, if X i ∈ Icc (0 : ℝ) 1 then 1 else 0
  f_nonneg := by
    intro X
    exact Finset.prod_nonneg (fun i _ ↦ by split <;> norm_num)
  f_support := by
    intro X h
    obtain ⟨i, hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
  v := fun i X ↦ max 0 (min 1 (X i))
  v_nonneg := fun _ _ ↦ le_max_left _ _
  v_continuous := fun i ↦ continuous_const.max (continuous_const.min (continuous_apply i))
  v_mono := by
    intro i X Y h
    exact max_le_max_left _ (min_le_min_left _ (h i))
  v_strictMono_own := by
    intro i X a ha b hb hab
    simpa only [Function.update_self, min_eq_right ha.2, max_eq_right ha.1,
      min_eq_right hb.2, max_eq_right hb.1] using hab

theorem value_eq_own {n : ℕ} (i : Fin n) (X : Fin n → ℝ) (h : X i ∈ Icc (0 : ℝ) 1) :
    (environment n).v i X = X i := by
  simp only [environment, min_eq_right h.2, max_eq_right h.1]

theorem private_values (n : ℕ) : IsPrivateValues (environment n) := by
  intro i X Y h
  change max 0 (min 1 (X i)) = max 0 (min 1 (Y i))
  rw [h]

theorem independent_signals (n : ℕ) : HasIndependentSignals (environment n) :=
  ⟨fun _ t ↦ if t ∈ Icc (0 : ℝ) 1 then 1 else 0, fun _ ↦ rfl⟩

example (n : ℕ) : IsIPV (environment n) := ⟨private_values n, independent_signals n⟩

example (n : ℕ) : HasAffiliatedSignals (environment n) :=
  (independent_signals n).hasAffiliatedSignals

-- The clamped extension would fail the old global strictness requirement.
example : ¬ StrictMono (fun t : ℝ ↦ (environment 1).v 0 (fun _ ↦ t)) := by
  intro h
  have hlt := h (by norm_num : (1 : ℝ) < 2)
  norm_num [environment] at hlt

end MathEconLibTest.SignalValueEnv
