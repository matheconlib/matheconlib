/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
module

public import MathEconLib.GameTheory.Strategic.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Linear Cournot competition

Firms face inverse demand `a - b * Q` and common marginal cost `k`. The economic game
has nonnegative quantities and untruncated linear inverse demand. An auxiliary game on
real quantities isolates the quadratic optimization from feasibility. Under `0 < b`, its
symmetric profile is Nash for every `a` and `k`; `k ≤ a` makes that profile nonnegative.
Restricting actions uses the existing Nash transport theorem.

The scalar payoff-gap identity also holds at `n = 0`; profile results quantify over `Fin n`.
The quantity-competition calculation here was extracted from the all-purchase development
in #121, following the shared-core design in #193. This module does not prove uniqueness, nor
the shutdown equilibrium of the nonnegative game when `a < k`. Welfare and auction accounting
remain in their own modules.
-/

@[expose] public noncomputable section

namespace MathEconLib.Competition.Cournot

open Finset
open MathEconLib.GameTheory

/-- Profit with inverse demand `a - b * Q` and common marginal cost `k`. -/
def profit {n : ℕ} (a b k : ℝ) (i : Fin n) (q : Fin n → ℝ) : ℝ :=
  q i * (a - b * ∑ j, q j - k)

/-- Auxiliary real-quantity game used to separate optimality from nonnegative feasibility. -/
def unconstrainedGame (n : ℕ) (a b k : ℝ) : StrategicGame (Fin n) (fun _ => ℝ) ℝ where
  payoff := profit a b k

/-- The economic Cournot game restricts each firm's quantity to be nonnegative. -/
def game (n : ℕ) (a b k : ℝ) :
    StrategicGame (Fin n) (fun _ => {q : ℝ // 0 ≤ q}) ℝ :=
  (unconstrainedGame n a b k).comapActions (fun _ q => q.val)

/-- Symmetric stationary quantity; feasibility and optimality are separate theorems. -/
def symmetricQuantity (n : ℕ) (a b k : ℝ) : ℝ :=
  (a - k) / (b * ((n : ℝ) + 1))

/-- Positive demand slope and cost at most the intercept make the stationary quantity feasible. -/
theorem symmetricQuantity_nonneg (n : ℕ) (a b k : ℝ) (hb : 0 < b) (hk : k ≤ a) :
    0 ≤ symmetricQuantity n a b k :=
  div_nonneg (sub_nonneg.mpr hk) (mul_nonneg hb.le (by positivity))

/-- Completing the square gives the loss from any real deviation, including at `n = 0`.
No feasibility restriction on the stationary quantity or the deviation is needed. -/
theorem symmetricQuantity_payoff_gap (n : ℕ) (a b k : ℝ) (hb : 0 < b) (x : ℝ) :
    symmetricQuantity n a b k * (a - b * (n * symmetricQuantity n a b k) - k) -
      x * (a - b * (x + ((n : ℝ) - 1) * symmetricQuantity n a b k) - k) =
        b * (x - symmetricQuantity n a b k) ^ 2 := by
  have hden : b * ((n : ℝ) + 1) ≠ 0 := ne_of_gt (mul_pos hb (by positivity))
  have hstationary : symmetricQuantity n a b k * (b * ((n : ℝ) + 1)) = a - k :=
    div_mul_cancel₀ _ hden
  linear_combination -(symmetricQuantity n a b k - x) * hstationary

/-- The deviation changes total quantity as well as the deviator's own quantity. -/
theorem symmetric_payoff_gap {n : ℕ} (a b k : ℝ) (hb : 0 < b) (i : Fin n) (x : ℝ) :
    profit a b k i (fun _ => symmetricQuantity n a b k) -
      profit a b k i (Function.update (fun _ => symmetricQuantity n a b k) i x) =
        b * (x - symmetricQuantity n a b k) ^ 2 := by
  have hn : 1 ≤ n := Nat.succ_le_of_lt (Nat.zero_lt_of_lt i.isLt)
  have htotal : (∑ j, Function.update (fun _ : Fin n => symmetricQuantity n a b k) i x j) =
      x + ((n : ℝ) - 1) * symmetricQuantity n a b k := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    have heq : (∑ j ∈ Finset.univ.erase i,
        Function.update (fun _ : Fin n => symmetricQuantity n a b k) i x j) =
        ∑ _j ∈ Finset.univ.erase i, symmetricQuantity n a b k := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [heq]
    simp only [Function.update_self, Finset.sum_const, Finset.card_erase_of_mem
      (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Nat.cast_sub hn, Nat.cast_one]
    ring
  simpa only [profit, Function.update_self, htotal, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] using symmetricQuantity_payoff_gap n a b k hb x

/-- The auxiliary symmetric profile is Nash under `0 < b`, without assuming `k ≤ a`. -/
theorem unconstrained_symmetricProfile_isNash (n : ℕ) (a b k : ℝ) (hb : 0 < b) :
    (unconstrainedGame n a b k).IsNash (fun _ => symmetricQuantity n a b k) := by
  rw [StrategicGame.isNash_iff]
  intro i x
  have h := symmetric_payoff_gap a b k hb i x
  have hnonneg := mul_nonneg hb.le (sq_nonneg (x - symmetricQuantity n a b k))
  change profit a b k i (Function.update (fun _ => symmetricQuantity n a b k) i x) ≤
    profit a b k i (fun _ => symmetricQuantity n a b k)
  linarith

/-- The symmetric profile in the economic game, under its feasibility hypotheses. -/
def symmetricProfile (n : ℕ) (a b k : ℝ) (hb : 0 < b) (hk : k ≤ a) :
    Fin n → {q : ℝ // 0 ≤ q} :=
  fun _ => ⟨symmetricQuantity n a b k, symmetricQuantity_nonneg n a b k hb hk⟩

/-- Restricting the auxiliary game to nonnegative quantities preserves this feasible equilibrium. -/
theorem symmetricProfile_isNash (n : ℕ) (a b k : ℝ) (hb : 0 < b) (hk : k ≤ a) :
    (game n a b k).IsNash (symmetricProfile n a b k hb hk) :=
  (unconstrained_symmetricProfile_isNash n a b k hb).comapActions
    (fun _ (q : {q : ℝ // 0 ≤ q}) => q.val)

end MathEconLib.Competition.Cournot
