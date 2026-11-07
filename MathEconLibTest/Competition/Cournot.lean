/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
module

import MathEconLib.Competition.Cournot.Linear
import Mathlib.Tactic

/-! Regression checks for the shared linear Cournot game and restricted actions. -/

open MathEconLib.Competition.Cournot MathEconLib.GameTheory

-- The bounded duopoly parameters of #176: equilibrium quantity 1/3 and profit 1/9.
example : symmetricQuantity 2 2 1 1 = 1 / 3 := by norm_num [symmetricQuantity]

example (i : Fin 2) : profit 2 1 1 i (fun _ => symmetricQuantity 2 2 1 1) = 1 / 9 := by
  norm_num [profit, symmetricQuantity, Fin.sum_univ_two]

-- Restrict to capacity one using Nash transport, without another optimization proof.
example : ((game 2 2 1 1).comapActions
    (fun _ (q : Set.Icc (0 : ℝ) 1) => (⟨q.val, q.property.1⟩ : {q : ℝ // 0 ≤ q}))).IsNash
      (fun _ => (⟨1 / 3, by norm_num, by norm_num⟩ : Set.Icc (0 : ℝ) 1)) := by
  apply StrategicGame.IsNash.comapActions
  convert symmetricProfile_isNash 2 2 1 1 (by norm_num) (by norm_num) using 1
  funext i
  apply Subtype.ext
  norm_num [symmetricProfile, symmetricQuantity]

-- Equality of cost and intercept gives the zero profile.
example (n : ℕ) (a b : ℝ) : symmetricQuantity n a b a = 0 := by simp [symmetricQuantity]

-- Auxiliary optimality remains available above the intercept, where quantities are negative.
example : (unconstrainedGame 2 1 1 2).IsNash (fun _ => symmetricQuantity 2 1 1 2) :=
  unconstrained_symmetricProfile_isNash 2 1 1 2 (by norm_num)

-- The scalar identity is retained even for zero firms.
example (a b k x : ℝ) (hb : 0 < b) :
    symmetricQuantity 0 a b k * (a - b * (0 * symmetricQuantity 0 a b k) - k) -
      x * (a - b * (x + (0 - 1) * symmetricQuantity 0 a b k) - k) =
        b * (x - symmetricQuantity 0 a b k) ^ 2 :=
  by simpa only [Nat.cast_zero] using symmetricQuantity_payoff_gap 0 a b k hb x

-- Increasing own output changes price: the deviator earns zero, not 2/9.
example : profit 2 1 1 (0 : Fin 2) (Function.update (fun _ => (1 / 3 : ℝ)) 0 (2 / 3)) = 0 := by
  norm_num [profit, Fin.sum_univ_two]

#print axioms symmetric_payoff_gap
#print axioms unconstrained_symmetricProfile_isNash
#print axioms symmetricProfile_isNash
