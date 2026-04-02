module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! # Mechanism — Allocation and Payment Rules (Section 3b)

Examples: first-price, second-price, all-pay auctions are different `Mechanism` values.
-/

@[expose] public section

open Set

/-- A mechanism for `n` bidders: allocation rule and payment rule, both
functions of the full bid vector `b = (b₁,...,bₙ)`.

In the standard setting, `xᵢ(b)` is the probability that bidder `i` wins
given bid profile `b`, and `tᵢ(b)` is the payment of bidder `i`. -/
structure Mechanism (n : ℕ) where
  /-- Allocation rule: `x i b` is the probability bidder `i` wins given bids `b` -/
  x : Fin n → (Fin n → ℝ) → ℝ
  /-- Measurability of allocation -/
  x_measurable : ∀ i, Measurable (x i)
  /-- Payment rule: `t i b` is the payment of bidder `i` given bids `b` -/
  t : Fin n → (Fin n → ℝ) → ℝ

namespace Mechanism

variable {n : ℕ} (M : Mechanism n)

/-- Allocation takes values in `[0, 1]`. -/
def HasValidAllocation : Prop := ∀ i b, M.x i b ∈ Icc 0 1

/-- Feasibility: total allocation ≤ 1 (single indivisible good). -/
def IsFeasible : Prop := ∀ b, ∑ i, M.x i b ≤ 1

/-- Efficient allocation: the highest-type bidder wins. -/
def IsEfficient : Prop :=
  ∀ i, M.x i = {f | ∀ j ≠ i, f j < f i}.indicator 1

end Mechanism

end
