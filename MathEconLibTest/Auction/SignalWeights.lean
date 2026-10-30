/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Auction.Affiliation.WinnersCurse

/-!
# Algebraic signal weights and finite conditional averages

Positive rescaling preserves all three finite conditional-average formulas.
Zero weights satisfy factorization and affiliation but do not give positive
conditioning mass. The normalized comparison theorems' positivity, inclusion and
nonemptiness hypotheses exclude every zero-mass conditioning set.
-/

@[expose] public noncomputable section

open MathEconLib Auction.Affiliation Finset

namespace MathEconLibTest.SignalWeights

/-- Rescaling cancels algebraically, including at the totalized zero denominator. -/
theorem rescale_condExpOn {α : Type*} (f g : α → ℝ) (A : Finset α)
    (c : ℝ) (hc : 0 < c) :
    condExpOn (fun x ↦ c * f x) g A = condExpOn f g A := by
  unfold condExpOn
  simp_rw [show ∀ x, g x * (c * f x) = c * (g x * f x) from fun x ↦ by ring]
  rw [← mul_sum, ← mul_sum]
  exact mul_div_mul_left _ _ hc.ne'

example {n : ℕ} (f g : (Fin n → ℝ) → ℝ) (S : Finset (Fin n → ℝ))
    (i : Fin n) (t c : ℝ) (hc : 0 < c) :
    condExpSlice (fun x ↦ c * f x) g S i t = condExpSlice f g S i t :=
  rescale_condExpOn f g _ c hc

example {n : ℕ} (f g : (Fin n → ℝ) → ℝ) (S : Finset (Fin n → ℝ))
    (i : Fin n) (t c : ℝ) (hc : 0 < c) :
    condExpWinningSlice (fun x ↦ c * f x) g S i t = condExpWinningSlice f g S i t :=
  rescale_condExpOn f g _ c hc

-- Unnormalized masses 2 and 6 give the genuine weighted average 3, not the raw sum 24.
example : condExpOn (fun b : Bool ↦ if b then 6 else 2)
    (fun b ↦ if b then 4 else 0) univ = 3 := by
  norm_num [condExpOn, Fintype.sum_bool]

-- Algebraic factorization and affiliation allow zero total mass.
example : Factors (fun _ : Fin 1 → ℝ ↦ 0) (fun _ _ ↦ 0) := by
  intro X
  simp

example {n : ℕ} : Affiliated (fun _ : Fin n → ℝ ↦ 0) := by
  intro X Y
  simp

example {α : Type*} (g : α → ℝ) (A : Finset α) : condExpOn (fun _ ↦ 0) g A = 0 := by
  simp [condExpOn]

/-- These are exactly the mass hypotheses used by the normalized comparison theorems. -/
theorem zero_mass_excludes_comparison {α : Type*} {f : α → ℝ} {S A : Finset α}
    (hmass : (∑ x ∈ A, f x) = 0) :
    ¬ ((∀ x ∈ S, 0 < f x) ∧ A ⊆ S ∧ A.Nonempty) := by
  rintro ⟨hpos, hAS, hA⟩
  have hpositive := sum_pos_on_of_pos hpos hAS hA
  rw [hmass] at hpositive
  exact lt_irrefl _ hpositive

end MathEconLibTest.SignalWeights
