module

public import Mathlib

/-!
# Mechanism — Allocation and Payment Rules

A `Mechanism` in the standard auction-theoretic sense: a tuple of allocation
rule `x` and payment rule `t`, both functions of the full bid/message vector.

Different auction formats are different `Mechanism` values:
- First-price: highest bidder wins, pays own bid
- Second-price: highest bidder wins, pays second-highest bid
- All-pay: highest bidder wins, all pay their bids

## Reference

Section 2(c) and 3(b) of the mathematical reference: "A mechanism consists of
message spaces (M₁,...,Mₙ) and an outcome function g : M → O."
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

/-! ### Standard auction formats -/

/-- First-price auction: highest bidder wins, pays own bid. -/
noncomputable def Mechanism.firstPrice (n : ℕ) : Mechanism n where
  x i b := if ∀ j ≠ i, b j < b i then 1 else 0
  t i b := b i * (if ∀ j ≠ i, b j < b i then 1 else 0)

/-- All-pay auction: highest bidder wins, everyone pays their bid. -/
noncomputable def Mechanism.allPay (n : ℕ) : Mechanism n where
  x i b := if ∀ j ≠ i, b j < b i then 1 else 0
  t i b := b i

end
