module

public import Auctionlib.Auction.AllPurchase.Welfare

/-!
# Revenue Analysis for All-Purchase Auctions (Section 6.3)

## Main results

- **Proposition 6.8** (`revenue_decomposition`): Revenue identity
  `E[pB] = n · E[b^{AP}(V)] − n · U(0) + E[B · φ(B)]`
- **Corollary 6.9** (`revenue_boundary_regime`): In the boundary regime,
  `E[pB] = n · E[b^{AP}(V)] + E[B · φ(B)]`
- **Proposition 6.9** (`optimal_price_interior`): The optimal price in the
  interior regime is `p* = (φ̄ + c + 2√α · M) / 2`

All revenue results here are stated as algebraic identities relating
revenue components, following the paper's decomposition.
-/

@[expose] public section

open Real

namespace AllPurchase

/-! ### Revenue decomposition (Proposition 6.8)

The seller's revenue `E[pB]` decomposes into three terms:
1. `n · E[b^{AP}(V)]`: contest-driven revenue (all-pay equivalent)
2. `−n · U(0)`: baseline demand rent retained by bidders
3. `E[B · φ(B)]`: aggregate gross value of editions produced

We state the algebraic identity that links these quantities. -/

/-- **Proposition 6.8 (Revenue decomposition).**
If `netPayment` is the total expected net expenditure (= `n · E[C(β(V))]`),
`allPayRevenue` is `n · E[b^{AP}(V)]`, and `U₀` is the baseline utility,
then `netPayment = allPayRevenue − n · U₀`.

Combined with `E[pB] = netPayment + E[Bφ(B)]`, this gives the full decomposition:
`E[pB] = allPayRevenue − n · U₀ + E[Bφ(B)]`.

This is a restatement of the net-payment identity `C(β(v)) = b^{AP}(v) − U(0)`
aggregated over `n` symmetric bidders. -/
theorem revenue_decomposition (allPayRevenue netPayment editionValue U₀ revenue : ℝ) (n : ℕ)
    (h_net : netPayment = allPayRevenue - ↑n * U₀)
    (h_rev : revenue = netPayment + editionValue) :
    revenue = allPayRevenue - ↑n * U₀ + editionValue := by
  linarith

/-- In the boundary regime (`U₀ = 0`), revenue simplifies. -/
theorem revenue_boundary_regime (allPayRevenue editionValue revenue : ℝ) (n : ℕ)
    (h_net : revenue = allPayRevenue - ↑n * (0 : ℝ) + editionValue) :
    revenue = allPayRevenue + editionValue := by
  linarith

/-! ### Optimal pricing (Proposition 6.9)

In the interior regime with linear scarcity, the expected total quantity is
`E[B] = n · μ` where `μ = (φ̄ − p) / (α(n+1)) + 2M / ((n+1)√α)`.
Seller profit `Π(p) = (p − c) · E[B]` is a concave quadratic in `p`.
The unconstrained maximizer is `p* = (φ̄ + c + 2√α · M) / 2`. -/

/-- Expected total quantity in the interior regime:
`E[B] = n(φ̄ − p) / (α(n+1)) + 2nM / ((n+1)√α)`. -/
noncomputable def expectedTotalQuantity (φ_bar p α M : ℝ) (n : ℕ) : ℝ :=
  ↑n * (φ_bar - p) / (α * (↑n + 1)) + 2 * ↑n * M / ((↑n + 1) * sqrt α)

/-- Seller profit: `Π(p) = (p − c) · E[B]`. -/
noncomputable def sellerProfit (φ_bar c p α M : ℝ) (n : ℕ) : ℝ :=
  (p - c) * expectedTotalQuantity φ_bar p α M n

/-- **Proposition 6.9.** The derivative of profit with respect to price,
treating the contest moment `M` as independent of `p`:
`dΠ/dp = n/(α(n+1)) · [φ̄ + c − 2p + 2√α · M]`.

Setting `dΠ/dp = 0` gives `p* = (φ̄ + c + 2√α · M) / 2`. -/
noncomputable def optimalPrice (φ_bar c α M : ℝ) : ℝ :=
  (φ_bar + c + 2 * sqrt α * M) / 2

/-- At the optimal price, the profit first-order condition is satisfied:
`φ̄ + c − 2p* + 2√α · M = 0`. -/
theorem optimal_price_foc (φ_bar c α M : ℝ) :
    φ_bar + c - 2 * optimalPrice φ_bar c α M + 2 * sqrt α * M = 0 := by
  unfold optimalPrice; ring

/-- The optimal price is feasible for the interior regime iff
`φ̄ − c > 2n · √α · M`. -/
theorem optimal_price_interior_condition (φ_bar c α M : ℝ) :
    optimalPrice φ_bar c α M < φ_bar ↔ φ_bar - c > 2 * sqrt α * M := by
  unfold optimalPrice
  constructor
  · intro h; linarith
  · intro h; linarith

/-! ### Revenue comparison

The three seller options:
- Option A: all-pay auction only → revenue `Π_A = n · E[V_{(n-1:n)}]`
- Option B: editions only → revenue `Π_B = (p − c) · B^{ed}`
- Option C: bundled all-purchase → revenue `Π_C = (p − c) · E[B]`
-/

/-- Editions-only profit. -/
noncomputable def editionsOnlyProfit (φ_bar c p α : ℝ) (n : ℕ) : ℝ :=
  (p - c) * cournotQuantity φ_bar p α n

/-- Bundled all-purchase profit. -/
noncomputable def bundledProfit (φ_bar c p α M : ℝ) (n : ℕ) : ℝ :=
  (p - c) * expectedTotalQuantity φ_bar p α M n

/-- The bundled profit exceeds editions-only profit when `M > 0`:
the contest component `2nM/((n+1)√α)` adds to total quantity. -/
theorem bundled_exceeds_editionsOnly (φ_bar c p α M : ℝ) (n : ℕ)
    (hp : c < p) (hα : 0 < α) (hM : 0 < M) (hn : (0 : ℝ) < ↑n) :
    editionsOnlyProfit φ_bar c p α n < bundledProfit φ_bar c p α M n := by
  unfold editionsOnlyProfit bundledProfit expectedTotalQuantity cournotQuantity
  have hp' : 0 < p - c := by linarith
  have hextra : 0 < 2 * ↑n * M / ((↑n + 1) * sqrt α) := by
    apply div_pos (by nlinarith) (mul_pos (by linarith) (sqrt_pos_of_pos hα))
  have : (p - c) * (↑n * (φ_bar - p) / (α * (↑n + 1))) <
      (p - c) * (↑n * (φ_bar - p) / (α * (↑n + 1)) +
        2 * ↑n * M / ((↑n + 1) * sqrt α)) := by
    apply mul_lt_mul_of_pos_left _ hp'
    linarith
  linarith

end AllPurchase

end
