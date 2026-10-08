module

public import MathEconLib.Auction.AllPurchase.LinearScarcity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Algebraic optimal-pricing formulas for all-purchase auctions

The formulas here are motivated by Propositions 6.8 and 6.12 (§6.7.2) in Scott's notes.
For supplied real parameters `φbar`, `α`, `c`, and `M`, and a natural number `n`,
`interiorMeanQuantity` defines
`Q(p) = n(φbar − p)/(α(n+1)) + 2nM/((n+1)√α)`, and `sellerProfitInterior` defines
`Π(p) = (p − c) · Q(p)`. The candidate price is `p* = (φbar + c + 2√α·M)/2`.

When `α > 0` and `n ≥ 1`, the defined quadratic `Π` has the unique maximizer `p*` over
all real prices. The bridge identifying `Q` with an auction's mean equilibrium quantity
and `Π` with its actual seller profit remains to be formalized. In particular, this file
does not identify `M` with the expected square root of the all-pay benchmark bid.

The final theorem rewrites the interior-regime inequality at the candidate price for arbitrary
parameters. Auction feasibility and global optimality in the economic model require separate
results.

## Main definitions

* `AllPurchase.interiorMeanQuantity`: the supplied quantity formula `Q`.
* `AllPurchase.sellerProfitInterior`: the defined profit formula `Π`.
* `AllPurchase.optimalPriceInterior`: the candidate price `p*`.

## Main statements

* `AllPurchase.sellerProfitInterior_le_at_optimal`: `Π(p) ≤ Π(p*)` for every real price
  when `α > 0` and `n ≥ 1`.
* `AllPurchase.sellerProfitInterior_eq_at_optimal_iff`: under the same hypotheses, equality
  holds exactly when `p = p*`.
* `AllPurchase.optimalPriceInterior_in_interior_regime`: the algebraic equivalence
  `φbar − p* > (n−1)√α·M ↔ φbar − c > 2n√α·M`.

## Proof strategy

For `α > 0` and `n ≥ 1`, set `b = n/(α(n+1)) > 0` and `Φ = φbar + 2√α·M`.
Then `Π(p) = b · (p − c) · (Φ − p)` and
`Π(p*) − Π(p) = b · (p − p*)²`, proving maximality and uniqueness for the defined formula.
-/

namespace MathEconLib

@[expose] public section

namespace AllPurchase

open Real

/-- The quantity formula `Q(p) = n(φbar − p)/(α(n+1)) + 2nM/((n+1)√α)`, defined for
supplied parameters and motivated by Proposition 6.8 in Scott's notes. Its identification with
mean aggregate equilibrium quantity remains to be formalized. -/
noncomputable def interiorMeanQuantity (φbar α M : ℝ) (n : ℕ) (p : ℝ) : ℝ :=
  (n : ℝ) * (φbar - p) / (α * ((n : ℝ) + 1)) +
    2 * (n : ℝ) * M / (((n : ℝ) + 1) * sqrt α)

/-- The defined profit formula `Π(p) = (p − c) · interiorMeanQuantity φbar α M n p`.
Its identification with actual auction seller profit remains to be formalized. -/
noncomputable def sellerProfitInterior (φbar α c M : ℝ) (n : ℕ) (p : ℝ) : ℝ :=
  (p - c) * interiorMeanQuantity φbar α M n p

/-- The candidate price `p* = (φbar + c + 2√α·M)/2`, motivated by Proposition 6.12 in
Scott's notes. For `α > 0` and `n ≥ 1`, the theorems below show that it uniquely maximizes
the defined `sellerProfitInterior` formula over `ℝ`. -/
noncomputable def optimalPriceInterior (φbar c α M : ℝ) : ℝ :=
  (φbar + c + 2 * sqrt α * M) / 2

/-! ### Factored form of the profit -/

/-- The defined profit formula factors as `Π(p) = b · (p − c) · (Φ − p)`, where
`b = n/(α(n+1))` and `Φ = φbar + 2√α·M`, under `α > 0` and `n ≥ 1`.
This factorization supports the algebraic calculation motivated by Proposition 6.12. -/
theorem sellerProfitInterior_eq_factored
    {φbar α c M : ℝ} {n : ℕ} (hα : 0 < α) (hn : 1 ≤ n) (p : ℝ) :
    sellerProfitInterior φbar α c M n p =
      ((n : ℝ) / (α * ((n : ℝ) + 1))) *
        ((p - c) * ((φbar + 2 * sqrt α * M) - p)) := by
  have hα_ne : α ≠ 0 := ne_of_gt hα
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by
    have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact ne_of_gt this
  have hsqrt_sq : sqrt α * sqrt α = α := mul_self_sqrt hα.le
  have hsqrt_ne : sqrt α ≠ 0 := by
    have : 0 < sqrt α := sqrt_pos.mpr hα
    exact ne_of_gt this
  unfold sellerProfitInterior interiorMeanQuantity
  field_simp
  linear_combination (-2 * M * (p - c)) * hsqrt_sq

/-! ### Main inequality: `Π(p) ≤ Π(p*)` -/

/-- For `α > 0` and `n ≥ 1`, the gap in the defined profit formula is
`Π(p*) − Π(p) = (n / (α(n+1))) · (p − p*)²`, hence nonnegative. -/
theorem sellerProfitInterior_optimal_sub
    {φbar α c M : ℝ} {n : ℕ} (hα : 0 < α) (hn : 1 ≤ n) (p : ℝ) :
    sellerProfitInterior φbar α c M n (optimalPriceInterior φbar c α M) -
        sellerProfitInterior φbar α c M n p =
      ((n : ℝ) / (α * ((n : ℝ) + 1))) *
        (p - optimalPriceInterior φbar c α M) ^ 2 := by
  rw [sellerProfitInterior_eq_factored hα hn,
      sellerProfitInterior_eq_factored hα hn]
  unfold optimalPriceInterior
  ring

/-- **The coefficient `b = n/(α(n+1))` is positive** under `0 < α` and `1 ≤ n`. -/
theorem coeff_pos {α : ℝ} {n : ℕ} (hα : 0 < α) (hn : 1 ≤ n) :
    0 < (n : ℝ) / (α * ((n : ℝ) + 1)) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h_denom : (0 : ℝ) < α * ((n : ℝ) + 1) := by positivity
  exact div_pos hn_pos h_denom

/-- For `α > 0` and `n ≥ 1`, the candidate `p* = (φbar + c + 2√α·M)/2` maximizes the
defined `sellerProfitInterior` formula over all real prices. This is the algebraic maximization
component motivated by Proposition 6.12. The auction-level profit identification remains
unproved. -/
theorem sellerProfitInterior_le_at_optimal
    {φbar α c M : ℝ} {n : ℕ} (hα : 0 < α) (hn : 1 ≤ n) (p : ℝ) :
    sellerProfitInterior φbar α c M n p ≤
      sellerProfitInterior φbar α c M n (optimalPriceInterior φbar c α M) := by
  have h := sellerProfitInterior_optimal_sub (φbar := φbar) (c := c) (M := M) hα hn p
  have hb := coeff_pos (α := α) (n := n) hα hn
  have hsq : 0 ≤ (p - optimalPriceInterior φbar c α M) ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg hb.le hsq]

/-- For `α > 0` and `n ≥ 1`, equality with the maximum of the defined profit formula
holds exactly at the candidate price: `Π(p) = Π(p*) ↔ p = p*`. -/
theorem sellerProfitInterior_eq_at_optimal_iff
    {φbar α c M : ℝ} {n : ℕ} (hα : 0 < α) (hn : 1 ≤ n) (p : ℝ) :
    sellerProfitInterior φbar α c M n p =
        sellerProfitInterior φbar α c M n (optimalPriceInterior φbar c α M) ↔
      p = optimalPriceInterior φbar c α M := by
  have h := sellerProfitInterior_optimal_sub (φbar := φbar) (c := c) (M := M) hα hn p
  have hb := coeff_pos (α := α) (n := n) hα hn
  have hb_ne : ((n : ℝ) / (α * ((n : ℝ) + 1))) ≠ 0 := ne_of_gt hb
  refine ⟨fun heq => ?_, fun heq => by rw [heq]⟩
  have hprod : ((n : ℝ) / (α * ((n : ℝ) + 1))) *
      (p - optimalPriceInterior φbar c α M) ^ 2 = 0 := by linarith
  have hsq_zero : (p - optimalPriceInterior φbar c α M) ^ 2 = 0 :=
    (mul_eq_zero.mp hprod).resolve_left hb_ne
  have hdiff_zero : p - optimalPriceInterior φbar c α M = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp hsq_zero
  linarith

/-! ### Algebraic interior-regime inequality -/

/-- For arbitrary supplied parameters, the candidate price satisfies
`φbar − p* > (n−1)√α·M` exactly when `φbar − c > 2n√α·M`.
This algebraic equivalence is motivated by Proposition 6.8 and the second statement of
Proposition 6.12 in Scott's notes. Auction feasibility and global optimality in the economic
model require separate results. -/
theorem optimalPriceInterior_in_interior_regime
    (φbar α c M : ℝ) (n : ℕ) :
    ((n : ℝ) - 1) * sqrt α * M < φbar - optimalPriceInterior φbar c α M ↔
      2 * (n : ℝ) * sqrt α * M < φbar - c := by
  unfold optimalPriceInterior
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

end AllPurchase

end

end MathEconLib
