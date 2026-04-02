module

public import Auctionlib.Auction.AllPurchase.LinearScarcity
public import Auctionlib.ReducedForm.TypeDeviationIC
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Explicit Equilibrium Solutions (Section 6.2)

Closed-form equilibrium strategies for the all-purchase auction under
specific scarcity functions, stated at the `ReducedForm` and `Auction` levels.

The bridge is the **net-payment identity** (Proposition 6.4):
`R.cost(R.strategy(v)) = R.allPayBid(v) − R.U(R.lowestType)`.

## Main results

- **Proposition 6.5** (`ReducedForm.constant_scarcity_strategy`):
  `R.strategy(v) = R.allPayBid(v) / p_net`
- **Proposition 6.6** (`ReducedForm.boundary_regime_strategy`,
  `Auction.boundary_regime_strategy_auction`):
  `β(v) = (−K + √(K² + 4α · allPayBid(v))) / (2α)`
- **Proposition 6.7** (`ReducedForm.interior_regime_strategy`,
  `Auction.interior_regime_strategy_auction`):
  `β(v) = −K/(2α) + √(allPayBid(v)/α)`
-/

@[expose] public section

open Real

/-! ## Part 1: Algebraic strategy formulas -/

namespace AllPurchase

/-- Net cost under linear scarcity (private helper): `C(b) = α · b² + K · b`. -/
private noncomputable def netCostLinear (α K b : ℝ) : ℝ := α * b ^ 2 + K * b

/-- Completed-square form (private helper):
`C(b) = α · (b + K/(2α))² - K²/(4α)`. -/
private theorem netCostLinear_completed_square (α K b : ℝ) (hα : α ≠ 0) :
    netCostLinear α K b = α * (b + K / (2 * α)) ^ 2 - K ^ 2 / (4 * α) := by
  unfold netCostLinear; field_simp; ring

/-- Equilibrium strategy under linear scarcity, boundary regime (`K ≥ 0`):
`β(v) = (−K + √(K² + 4α · bAP)) / (2α)`. -/
noncomputable def strategyBoundary (α K bAP : ℝ) : ℝ :=
  (-K + sqrt (K ^ 2 + 4 * α * bAP)) / (2 * α)

/-- Equilibrium strategy under linear scarcity, interior regime (`A = −K > 0`):
`β(v) = A/(2α) + √(bAP/α)`. -/
noncomputable def strategyInterior (α A bAP : ℝ) : ℝ :=
  A / (2 * α) + sqrt (bAP / α)

/-- The boundary strategy satisfies `αy² + Ky = c`. -/
theorem boundary_regime_quadratic_raw (α K c : ℝ) (hα : 0 < α) (hc : 0 ≤ c) :
    α * strategyBoundary α K c ^ 2 + K * strategyBoundary α K c = c := by
  suffices h : netCostLinear α K (strategyBoundary α K c) = c by
    simp only [netCostLinear] at h; linarith
  rw [netCostLinear_completed_square α K _ (ne_of_gt hα)]
  unfold strategyBoundary
  have hD : 0 ≤ K ^ 2 + 4 * α * c := by nlinarith [sq_nonneg K]
  have h1 : (-K + sqrt (K ^ 2 + 4 * α * c)) / (2 * α) + K / (2 * α) =
      sqrt (K ^ 2 + 4 * α * c) / (2 * α) := by ring
  rw [h1]
  have hsq : sqrt (K ^ 2 + 4 * α * c) ^ 2 = K ^ 2 + 4 * α * c := sq_sqrt hD
  rw [div_pow, hsq]
  field_simp
  ring

/-- The boundary strategy is nonneg. -/
theorem strategyBoundary_nonneg (α K bAP : ℝ)
    (hα : 0 < α) (hK : 0 ≤ K) (hbAP : 0 ≤ bAP) :
    0 ≤ strategyBoundary α K bAP := by
  unfold strategyBoundary
  apply div_nonneg _ (by linarith)
  have : K ≤ sqrt (K ^ 2 + 4 * α * bAP) := by
    calc K = sqrt (K ^ 2) := (sqrt_sq hK).symm
      _ ≤ sqrt (K ^ 2 + 4 * α * bAP) := sqrt_le_sqrt (by nlinarith)
  linarith

end AllPurchase

/-! ## Part 2: ReducedForm-level propositions -/

namespace ReducedForm

open AllPurchase

variable (R : ReducedForm)

/-! #### Proposition 6.5: Constant scarcity equilibrium -/

/-- **Proposition 6.5.** Under linear cost `[HasLinearCost R]` and boundary
regime `[IsBoundaryRegime R]`, the equilibrium strategy is
`strategy(v) = allPayBid(v) / p_net`. -/
theorem constant_scarcity_strategy [HasTypeDeviationIC R]
    [HasLinearCost R] [IsBoundaryRegime R]
    (v : ℝ) (hv : v ∈ R.typeInterval) :
    R.strategy v = R.allPayBid v / R.linearCost_pNet := by
  have hid := R.netPaymentIdentity v hv
  rw [HasLinearCost.cost_eq, IsBoundaryRegime.U_lowestType_zero, sub_zero] at hid
  rw [← hid, mul_div_cancel_left₀ _ (ne_of_gt HasLinearCost.p_net_pos)]

/-! #### Proposition 6.6: Boundary regime equilibrium -/

/-- In the boundary regime with quadratic cost, the strategy satisfies
`α · β(v)² + K · β(v) = allPayBid(v)`. -/
theorem boundary_regime_quadratic [HasTypeDeviationIC R]
    [HasQuadraticCost R] [IsBoundaryRegime R]
    (v : ℝ) (hv : v ∈ R.typeInterval) :
    R.quadraticCost_α * (R.strategy v) ^ 2 + R.quadraticCost_K * R.strategy v =
      R.allPayBid v := by
  have hid := R.netPaymentIdentity v hv
  rw [HasQuadraticCost.cost_eq, IsBoundaryRegime.U_lowestType_zero, sub_zero] at hid
  linarith

/-- **Proposition 6.6.** Under quadratic cost and boundary regime, if the
strategy is nonneg and `K ≥ 0`, then
`strategy(v) = (−K + √(K² + 4α · allPayBid(v))) / (2α)`. -/
theorem boundary_regime_strategy [HasTypeDeviationIC R]
    [HasQuadraticCost R] [IsBoundaryRegime R]
    (hK : 0 ≤ R.quadraticCost_K)
    (v : ℝ) (hv : v ∈ R.typeInterval)
    (h_bAP_nn : 0 ≤ R.allPayBid v)
    (h_strat_nn : 0 ≤ R.strategy v) :
    R.strategy v = strategyBoundary R.quadraticCost_α R.quadraticCost_K (R.allPayBid v) := by
  have hα_pos := HasQuadraticCost.α_pos (R := R)
  have hquad := R.boundary_regime_quadratic v hv
  set α := R.quadraticCost_α; set K := R.quadraticCost_K
  set β := R.strategy v; set c := R.allPayBid v
  set y := strategyBoundary α K c
  have hy_eq : α * y ^ 2 + K * y = c :=
    boundary_regime_quadratic_raw α K c hα_pos h_bAP_nn
  have hfactor : (β - y) * (α * (β + y) + K) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfactor with h | h
  · linarith
  · have hy_nn : 0 ≤ y := strategyBoundary_nonneg α K c hα_pos hK h_bAP_nn
    have hα_ne : α ≠ 0 := ne_of_gt hα_pos
    have hsum : β + y = -K / α := by field_simp at h ⊢; linarith
    have hK0 : K = 0 := by nlinarith
    have : β + y = 0 := by rw [hsum, hK0]; simp
    linarith

/-! #### Proposition 6.7: Interior regime equilibrium -/

/-- In the interior regime, the strategy satisfies the shifted quadratic
`α · β(v)² + K · β(v) = allPayBid(v) − K²/(4α)`. -/
theorem interior_regime_quadratic [HasTypeDeviationIC R]
    [IsInteriorRegime R]
    (v : ℝ) (hv : v ∈ R.typeInterval) :
    R.quadraticCost_α * (R.strategy v) ^ 2 + R.quadraticCost_K * R.strategy v =
      R.allPayBid v - R.quadraticCost_K ^ 2 / (4 * R.quadraticCost_α) := by
  have hid := R.netPaymentIdentity v hv
  rw [HasQuadraticCost.cost_eq, IsInteriorRegime.U_lowestType_eq] at hid
  linarith

/-- **Proposition 6.7.** Under quadratic cost and interior regime, if the
strategy satisfies `strategy(v) ≥ −K/(2α)`, then
`strategy(v) = −K/(2α) + √(allPayBid(v)/α)`. -/
theorem interior_regime_strategy [HasTypeDeviationIC R]
    [IsInteriorRegime R]
    (v : ℝ) (hv : v ∈ R.typeInterval)
    (h_bAP_nn : 0 ≤ R.allPayBid v)
    (h_strat_ge : -R.quadraticCost_K / (2 * R.quadraticCost_α) ≤ R.strategy v) :
    R.strategy v =
      strategyInterior R.quadraticCost_α (-R.quadraticCost_K) (R.allPayBid v) := by
  have hα_pos := HasQuadraticCost.α_pos (R := R)
  have hα_ne : R.quadraticCost_α ≠ 0 := ne_of_gt hα_pos
  have hK_neg := IsInteriorRegime.K_neg (R := R)
  set α := R.quadraticCost_α; set K := R.quadraticCost_K
  have hquad := R.interior_regime_quadratic v hv
  unfold strategyInterior
  have hba : 0 ≤ R.allPayBid v / α := div_nonneg h_bAP_nn (le_of_lt hα_pos)
  have h1 : α * (R.strategy v + K / (2 * α)) ^ 2 =
      α * (R.strategy v) ^ 2 + K * R.strategy v + K ^ 2 / (4 * α) := by
    field_simp; ring
  have h2 : α * (R.strategy v + K / (2 * α)) ^ 2 = R.allPayBid v := by linarith
  have hsq_eq : (R.strategy v + K / (2 * α)) ^ 2 = R.allPayBid v / α := by
    rwa [eq_div_iff hα_ne, mul_comm]
  have h_diff_nn : 0 ≤ R.strategy v + K / (2 * α) := by
    linarith [show -K / (2 * α) + K / (2 * α) = (0 : ℝ) from by ring]
  have h_sqrt : R.strategy v + K / (2 * α) = sqrt (R.allPayBid v / α) := by
    rw [← sqrt_sq h_diff_nn, hsq_eq]
  linarith [show K / (2 * α) + (-K / (2 * α)) = (0 : ℝ) from by ring]

end ReducedForm

/-! ## Part 3: Auction-level corollaries

These compose the full chain:
`HasLinearScarcity A` → `HasQuadraticCost R` → explicit strategy formula. -/

open MeasureTheory ProbabilityTheory AllPurchase

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} [NeZero n] [n.AtLeastTwo]

namespace Auction

variable (A : Auction Ω n)

/-- **Proposition 6.6 (Auction level).** In a symmetric all-purchase auction
with linear scarcity and boundary regime (`K ≥ 0`, `U(0) = 0`), the
equilibrium strategy satisfies
`β(v) = (−K + √(K² + 4α · allPayBid(v))) / (2α)`. -/
theorem boundary_regime_strategy_auction
    [Mechanism.IsAllPurchase A.rules] [HasLinearScarcity A] [HasIdenticalTypes A]
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (hβ_int : ∀ j, Integrable (fun ω => β (A.θ j ω)) ℙ)
    (i : Fin n)
    (hIC : A.toAllPurchaseReducedForm β hβ_meas i |>.HasTypeDeviationIC)
    (hBR : A.toAllPurchaseReducedForm β hβ_meas i |>.IsBoundaryRegime)
    (hK : 0 ≤ A.K_linear β)
    (v : ℝ) (hv : v ∈ (A.toAllPurchaseReducedForm β hβ_meas i |>.typeInterval))
    (h_bAP_nn : 0 ≤ (A.toAllPurchaseReducedForm β hβ_meas i |>.allPayBid v))
    (h_strat_nn : 0 ≤ β v) :
    β v = strategyBoundary A.linearScarcity_α (A.K_linear β)
      (A.toAllPurchaseReducedForm β hβ_meas i |>.allPayBid v) := by
  let R := A.toAllPurchaseReducedForm β hβ_meas i
  letI : R.HasQuadraticCost := A.allPurchaseHasQuadraticCost β hβ_meas hβ_int i
  change R.strategy v = _
  exact R.boundary_regime_strategy hK v hv h_bAP_nn h_strat_nn

omit [n.AtLeastTwo] in
/-- **Proposition 6.7 (Auction level).** In a symmetric all-purchase auction
with interior regime (`K < 0`), the equilibrium strategy satisfies
`β(v) = −K/(2α) + √(allPayBid(v)/α)`. The `α` and `K` come from the
`IsInteriorRegime` instance (which extends `HasQuadraticCost`). -/
theorem interior_regime_strategy_auction
    [Mechanism.IsAllPurchase A.rules] [HasLinearScarcity A] [HasIdenticalTypes A]
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (i : Fin n)
    (hIC : A.toAllPurchaseReducedForm β hβ_meas i |>.HasTypeDeviationIC)
    (hIR : A.toAllPurchaseReducedForm β hβ_meas i |>.IsInteriorRegime)
    (v : ℝ) (hv : v ∈ (A.toAllPurchaseReducedForm β hβ_meas i |>.typeInterval))
    (h_bAP_nn : 0 ≤ (A.toAllPurchaseReducedForm β hβ_meas i |>.allPayBid v))
    (h_strat_ge : -hIR.K_param / (2 * hIR.α_coeff) ≤ β v) :
    β v = strategyInterior hIR.α_coeff (-hIR.K_param)
      (A.toAllPurchaseReducedForm β hβ_meas i |>.allPayBid v) := by
  let R := A.toAllPurchaseReducedForm β hβ_meas i
  letI : R.IsInteriorRegime := hIR
  change R.strategy v = _
  exact R.interior_regime_strategy v hv h_bAP_nn h_strat_ge

end Auction

end
