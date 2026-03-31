module

public import Auctionlib.Mechanism.Basic

/-!
# All-Purchase Mechanism (Chapter 6)

A mechanism is an **all-purchase mechanism** when:
- The highest bidder wins (efficient allocation)
- Payments equal the net edition cost: each bidder pays posted price `p` per
  edition purchased, and each edition has resale value `φ(B)` depending on
  aggregate quantity `B = Σ bⱼ`.

The payment for bidder `i` given bids `b` is `(p − φ(Σ bⱼ)) · bᵢ`.

## Reference

Chapter 6 of the mathematical reference.
-/

@[expose] public section

open Set

namespace Mechanism

variable {n : ℕ}

/-- An all-purchase mechanism: efficient allocation (highest bidder wins) with
payments determined by posted price `p` and scarcity function `φ`.

The payment for bidder `i` given bids `b` is `(p - φ(Σ bⱼ)) · bᵢ`:
they pay `p` per edition purchased, and each edition has resale value `φ(B)`
depending on aggregate quantity `B = Σ bⱼ`. -/
class IsAllPurchase (M : Mechanism n) where
  /-- posted unit price -/
  p_price : ℝ
  /-- posted price is positive -/
  p_price_pos : 0 < p_price
  /-- scarcity function: per-unit edition value as function of aggregate quantity -/
  φ : ℝ → ℝ
  /-- scarcity function is continuous -/
  φ_continuous : Continuous φ
  /-- scarcity function is strictly decreasing -/
  φ_strictAnti : StrictAnti φ
  /-- allocation is efficient: highest bidder wins -/
  x_eq : ∀ i, M.x i = {f | ∀ j ≠ i, f j < f i}.indicator 1
  /-- payment is net edition cost: `tᵢ(b) = (p − φ(Σ bⱼ)) · bᵢ` -/
  t_eq : ∀ i b, M.t i b = (p_price - φ (∑ j, b j)) * b i

variable {n : ℕ} {M : Mechanism n} [IsAllPurchase M]

/-- The all-purchase allocation is valid: the indicator takes values in `{0, 1} ⊆ [0, 1]`. -/
theorem IsAllPurchase.hasValidAllocation : M.HasValidAllocation := by
  intro i b
  simp only [IsAllPurchase.x_eq, indicator_apply, mem_Icc]
  split_ifs <;> norm_num

end Mechanism

end
