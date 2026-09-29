module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! # Mechanism — Allocation and Payment Rules (Section 3b)

Examples: first-price, second-price, all-pay auctions are different `Mechanism` values.
-/

namespace MathEconLib

@[expose] public section

open Set

/-- A mechanism for `n` agents: allocation rule and payment rule, both
functions of the full report vector `r = (r₁,...,rₙ)`.

For a report profile `r`, `xᵢ(r)` is the allocation probability for agent `i`,
and `tᵢ(r)` is the payment of agent `i`. -/
structure Mechanism (n : ℕ) where
  /-- Allocation rule: `x i r` is the allocation probability for agent `i`
  given reports `r`. -/
  x : Fin n → (Fin n → ℝ) → ℝ
  /-- Measurability of allocation -/
  x_measurable : ∀ i, Measurable (x i)
  /-- Payment rule: `t i r` is the payment of agent `i` given reports `r`. -/
  t : Fin n → (Fin n → ℝ) → ℝ

namespace Mechanism

variable {n : ℕ} (M : Mechanism n)

/-- Allocation takes values in `[0, 1]`. -/
class HasValidAllocation : Prop where
  x_range : ∀ i b, M.x i b ∈ Icc 0 1

/-- Efficient allocation: the agent with the highest reported type receives
the allocation. -/
class IsEfficient : Prop where
  x_efficient : ∀ i, M.x i = {f | ∀ j ≠ i, f j < f i}.indicator 1

/-- Efficient allocation is valid: the indicator takes values in `{0, 1} ⊆ [0, 1]`. -/
instance IsEfficient.instHasValidAllocation [IsEfficient M] : HasValidAllocation M where
  x_range i b := by
    simp only [IsEfficient.x_efficient, indicator_apply, mem_Icc]; split_ifs <;> norm_num

end Mechanism

end

end MathEconLib
