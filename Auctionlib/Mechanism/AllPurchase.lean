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
class IsAllPurchase (M : Mechanism n) extends IsEfficient M where
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
  /-- payment is net edition cost: `tᵢ(b) = (p − φ(Σ bⱼ)) · bᵢ` -/
  t_eq : ∀ i b, M.t i b = (p_price - φ (∑ j, b j)) * b i

variable {n : ℕ} (M : Mechanism n) [IsAllPurchase M]

/-- The scarcity function `φ` from the all-purchase mechanism. -/
abbrev allPurchaseφ : ℝ → ℝ := IsAllPurchase.φ (M := M)

/-- The posted price `p` from the all-purchase mechanism. -/
abbrev allPurchase_p_price : ℝ := IsAllPurchase.p_price (M := M)

end Mechanism

end
