module

public import MathEconLib.Auction.AllPurchase.LinearScarcity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Optimal Pricing (Proposition 6.12, §6.7.2)

In the interior regime of a linear-scarcity all-purchase auction
(`ϕ(B) = ϕ̄ − αB`), Proposition 6.8 gives the closed form for the
mean equilibrium quantity as a function of the posted price `p`:
`𝔼[B](p) = n(ϕ̄ − p)/(α(n+1)) + 2nM/((n+1)√α)`,
where `M = 𝔼[√(b^{AP}(V))]` depends only on `F` and `n` (not on `p`).

The seller's profit `Π(p) = (p − c)·𝔼[B](p)` is therefore a concave
quadratic in `p`, and the FOC yields the unique unconstrained maximizer
`p* = (ϕ̄ + c + 2√α·M)/2`.  This is **Proposition 6.12** in Scott's notes.

This file states the proposition at the pure-algebra layer, mirroring how
the paper itself proves it (the connection to the auction-level
equilibrium is supplied by Proposition 6.8 / `interior_regime_strategy`).

## Main results

- `AllPurchase.interiorMeanQuantity` — closed form for `𝔼[B](p)` in the interior regime.
- `AllPurchase.sellerProfitInterior` — `Π(p) = (p − c)·𝔼[B](p)`.
- `AllPurchase.optimalPriceInterior` — the unique unconstrained maximizer `p*`.
- `AllPurchase.sellerProfitInterior_le_at_optimal` — main inequality: `Π(p) ≤ Π(p*)`.
- `AllPurchase.sellerProfitInterior_eq_at_optimal_iff` — strict concavity: equality iff `p = p*`.
- `AllPurchase.optimalPriceInterior_in_interior_regime` — feasibility condition
  `ϕ̄ − c > 2n√α·M` ⇔ `p*` satisfies the interior-regime inequality `ϕ̄ − p* > (n−1)√α·M`.

## Proof strategy

The key algebraic identity, after factoring `b := n/(α(n+1)) > 0` and
`Φ := ϕ̄ + 2√α·M`, is
`Π(p) = b · (p − c) · (Φ − p)`,
so `Π(p*) − Π(p) = b · (p − p*)² ≥ 0`.
-/

namespace MathEconLib

@[expose] public section

namespace AllPurchase

open Real

/-- **Mean aggregate equilibrium quantity in the interior regime**, as a
function of the posted price `p`.  By Proposition 6.8, in the interior
regime of a linear-scarcity all-purchase auction,
`𝔼[B](p) = n(ϕ̄ − p)/(α(n+1)) + 2nM/((n+1)√α)`. -/
noncomputable def interiorMeanQuantity (φbar α M : ℝ) (n : ℕ) (p : ℝ) : ℝ :=
  (n : ℝ) * (φbar - p) / (α * ((n : ℝ) + 1)) +
    2 * (n : ℝ) * M / (((n : ℝ) + 1) * sqrt α)

/-- **Seller profit in the interior regime**: `Π(p) = (p − c)·𝔼[B](p)`. -/
noncomputable def sellerProfitInterior (φbar α c M : ℝ) (n : ℕ) (p : ℝ) : ℝ :=
  (p - c) * interiorMeanQuantity φbar α M n p

/-- **The unconstrained profit-maximizing price** (Prop 6.12):
`p* = (ϕ̄ + c + 2√α·M)/2`. -/
noncomputable def optimalPriceInterior (φbar c α M : ℝ) : ℝ :=
  (φbar + c + 2 * sqrt α * M) / 2

/-! ### Factored form of the profit -/

/-- **Factored form.** Setting `b := n/(α(n+1))` and `Φ := ϕ̄ + 2√α·M`,
the profit factors as `Π(p) = b · (p − c) · (Φ − p)`.

This is the key algebraic identity behind Proposition 6.12. -/
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

/-- **The profit gap is a square.**

`Π(p*) − Π(p) = (n / (α(n+1))) · (p − p*)² ≥ 0`.

Pure algebra after substituting the factored form. -/
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

/-- **Proposition 6.12 (main inequality).**

For every `p`, the seller's profit in the interior regime satisfies
`Π(p) ≤ Π(p*)`, where `p* = (ϕ̄ + c + 2√α·M)/2`.

That is, `p*` is a global maximizer of `Π` over `ℝ`. -/
theorem sellerProfitInterior_le_at_optimal
    {φbar α c M : ℝ} {n : ℕ} (hα : 0 < α) (hn : 1 ≤ n) (p : ℝ) :
    sellerProfitInterior φbar α c M n p ≤
      sellerProfitInterior φbar α c M n (optimalPriceInterior φbar c α M) := by
  have h := sellerProfitInterior_optimal_sub (φbar := φbar) (c := c) (M := M) hα hn p
  have hb := coeff_pos (α := α) (n := n) hα hn
  have hsq : 0 ≤ (p - optimalPriceInterior φbar c α M) ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg hb.le hsq]

/-- **Strict concavity (uniqueness of the maximizer).**

`Π(p) = Π(p*)` if and only if `p = p*`. -/
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

/-! ### Feasibility: `p*` is in the interior regime -/

/-- **Feasibility (Prop 6.12, second statement).**

The optimal price `p*` lies in the interior regime — i.e. satisfies the
interior-regime inequality `ϕ̄ − p* > (n−1)√α·M` from Prop 6.8 — if and
only if `ϕ̄ − c > 2n√α·M`.

In particular, when `ϕ̄ − c > 2n√α·M`, the unconstrained maximizer of
`Π(p)` is a valid candidate for the seller's global optimum. -/
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
