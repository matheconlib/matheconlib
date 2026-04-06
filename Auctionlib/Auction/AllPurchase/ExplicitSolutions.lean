module

public import Auctionlib.Auction.AllPurchase.LinearScarcity
public import Auctionlib.BidderProblem.TypeDeviationIC
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Explicit Equilibrium Solutions (Section 6.2)

Closed-form equilibrium strategies for the all-purchase auction under
specific scarcity functions, stated at the `BidderProblem` and `Auction` levels.

The bridge is the **net-payment identity** (Proposition 6.4):
`cost(strategy(v)) = allPayBid(v) − U(lowestType)`.

## Main results

- **Proposition 6.5** (`LinearCostProblem.constant_scarcity_strategy`):
  `P.strategy(v) = P.allPayBid(v) / p_net`
- **Proposition 6.6** (`QuadraticCostProblem.boundary_regime_strategy`,
  `LinearScarcityAuction.boundary_regime_strategy_auction`):
  `β(v) = (−K + √(K² + 4α · allPayBid(v))) / (2α)`
- **Proposition 6.7** (`InteriorRegimeProblem.interior_regime_strategy`,
  `LinearScarcityAuction.interior_regime_strategy_auction`):
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

/-! ## Part 2: BidderProblem-level propositions -/

open AllPurchase

/-! #### Proposition 6.5: Constant scarcity equilibrium -/

/-- **Proposition 6.5.** Under linear cost and boundary regime, the equilibrium
strategy is `strategy(v) = allPayBid(v) / p_net`. -/
theorem LinearCostProblem.constant_scarcity_strategy (P : LinearCostProblem)
    [BidderProblem.HasTypeDeviationIC P.toBidderProblem]
    [BidderProblem.IsBoundaryRegime P.toBidderProblem]
    (v : ℝ) (hv : v ∈ P.typeInterval) :
    P.strategy v = P.allPayBid v / P.p_net := by
  have hid := P.toBidderProblem.netPaymentIdentity v hv
  rw [P.cost_eq, BidderProblem.IsBoundaryRegime.U_lowestType_zero, sub_zero] at hid
  rw [← hid, mul_div_cancel_left₀ _ (ne_of_gt P.p_net_pos)]

/-! #### Proposition 6.6: Boundary regime equilibrium -/

/-- In the boundary regime with quadratic cost, the strategy satisfies
`α · β(v)² + K · β(v) = allPayBid(v)`. -/
theorem QuadraticCostProblem.boundary_regime_quadratic (P : QuadraticCostProblem)
    [BidderProblem.HasTypeDeviationIC P.toBidderProblem]
    [BidderProblem.IsBoundaryRegime P.toBidderProblem]
    (v : ℝ) (hv : v ∈ P.typeInterval) :
    P.α_coeff * (P.strategy v) ^ 2 + P.K_param * P.strategy v =
      P.allPayBid v := by
  have hid := P.toBidderProblem.netPaymentIdentity v hv
  rw [P.cost_eq, BidderProblem.IsBoundaryRegime.U_lowestType_zero, sub_zero] at hid
  linarith

/-- **Proposition 6.6.** Under quadratic cost and boundary regime, if the
strategy is nonneg and `K ≥ 0`, then
`strategy(v) = (−K + √(K² + 4α · allPayBid(v))) / (2α)`. -/
theorem QuadraticCostProblem.boundary_regime_strategy (P : QuadraticCostProblem)
    [BidderProblem.HasTypeDeviationIC P.toBidderProblem]
    [BidderProblem.IsBoundaryRegime P.toBidderProblem]
    (hK : 0 ≤ P.K_param)
    (v : ℝ) (hv : v ∈ P.typeInterval)
    (h_bAP_nn : 0 ≤ P.allPayBid v)
    (h_strat_nn : 0 ≤ P.strategy v) :
    P.strategy v = strategyBoundary P.α_coeff P.K_param (P.allPayBid v) := by
  have hα_pos := P.α_pos
  have hquad := P.boundary_regime_quadratic v hv
  set α := P.α_coeff; set K := P.K_param
  set β := P.strategy v; set c := P.allPayBid v
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
theorem InteriorRegimeProblem.interior_regime_quadratic (P : InteriorRegimeProblem)
    [BidderProblem.HasTypeDeviationIC P.toBidderProblem]
    (v : ℝ) (hv : v ∈ P.typeInterval) :
    P.α_coeff * (P.strategy v) ^ 2 + P.K_param * P.strategy v =
      P.allPayBid v - P.K_param ^ 2 / (4 * P.α_coeff) := by
  have hid := P.toBidderProblem.netPaymentIdentity v hv
  rw [P.cost_eq, P.U_lowestType_eq] at hid
  linarith

/-- **Proposition 6.7.** Under quadratic cost and interior regime, if the
strategy satisfies `strategy(v) ≥ −K/(2α)`, then
`strategy(v) = −K/(2α) + √(allPayBid(v)/α)`. -/
theorem InteriorRegimeProblem.interior_regime_strategy (P : InteriorRegimeProblem)
    [BidderProblem.HasTypeDeviationIC P.toBidderProblem]
    (v : ℝ) (hv : v ∈ P.typeInterval)
    (h_bAP_nn : 0 ≤ P.allPayBid v)
    (h_strat_ge : -P.K_param / (2 * P.α_coeff) ≤ P.strategy v) :
    P.strategy v =
      strategyInterior P.α_coeff (-P.K_param) (P.allPayBid v) := by
  have hα_pos := P.α_pos
  have hα_ne : P.α_coeff ≠ 0 := ne_of_gt hα_pos
  have hK_neg := P.K_neg
  set α := P.α_coeff; set K := P.K_param
  have hquad := P.interior_regime_quadratic v hv
  unfold strategyInterior
  have hba : 0 ≤ P.allPayBid v / α := div_nonneg h_bAP_nn (le_of_lt hα_pos)
  have h1 : α * (P.strategy v + K / (2 * α)) ^ 2 =
      α * (P.strategy v) ^ 2 + K * P.strategy v + K ^ 2 / (4 * α) := by
    field_simp; ring
  have h2 : α * (P.strategy v + K / (2 * α)) ^ 2 = P.allPayBid v := by linarith
  have hsq_eq : (P.strategy v + K / (2 * α)) ^ 2 = P.allPayBid v / α := by
    rwa [eq_div_iff hα_ne, mul_comm]
  have h_diff_nn : 0 ≤ P.strategy v + K / (2 * α) := by
    linarith [show -K / (2 * α) + K / (2 * α) = (0 : ℝ) from by ring]
  have h_sqrt : P.strategy v + K / (2 * α) = sqrt (P.allPayBid v / α) := by
    rw [← sqrt_sq h_diff_nn, hsq_eq]
  linarith [show K / (2 * α) + (-K / (2 * α)) = (0 : ℝ) from by ring]

/-! ## Part 3: Auction-level corollaries

These compose the full chain:
`LinearScarcityAuction` → `QuadraticCostProblem` → explicit strategy formula. -/

open MeasureTheory ProbabilityTheory AllPurchase

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} [NeZero n] [n.AtLeastTwo]

namespace LinearScarcityAuction

variable (A : LinearScarcityAuction Ω n)

/-- **Proposition 6.6 (Auction level).** In a symmetric all-purchase auction
with linear scarcity and boundary regime (`K ≥ 0`, `U(0) = 0`), the
equilibrium strategy satisfies
`β(v) = (−K + √(K² + 4α · allPayBid(v))) / (2α)`. -/
theorem boundary_regime_strategy_auction
    [Auction.HasIdenticalTypes A.toAuction]
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (hβ_int : ∀ j, Integrable (fun ω => β (A.θ j ω)) ℙ)
    (i : Fin n)
    (hIC : (A.bidderProblem β hβ_meas i).HasTypeDeviationIC)
    (hBR : (A.bidderProblem β hβ_meas i).IsBoundaryRegime)
    (hK : 0 ≤ A.K_linear β)
    (v : ℝ) (hv : v ∈ (A.bidderProblem β hβ_meas i).typeInterval)
    (h_bAP_nn : 0 ≤ (A.bidderProblem β hβ_meas i).allPayBid v)
    (h_strat_nn : 0 ≤ β v) :
    β v = strategyBoundary A.α_coeff (A.K_linear β)
      ((A.bidderProblem β hβ_meas i).allPayBid v) := by
  let P := A.toQuadraticCostProblem β hβ_meas hβ_int i
  letI : BidderProblem.HasTypeDeviationIC P.toBidderProblem := hIC
  letI : BidderProblem.IsBoundaryRegime P.toBidderProblem := hBR
  change P.strategy v = _
  exact P.boundary_regime_strategy hK v hv h_bAP_nn h_strat_nn

/-- **Proposition 6.7 (Auction level).** In a symmetric all-purchase auction
with interior regime (`K < 0`), the equilibrium strategy satisfies
`β(v) = −K/(2α) + √(allPayBid(v)/α)`. -/
theorem interior_regime_strategy_auction
    [Auction.HasIdenticalTypes A.toAuction]
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (hβ_int : ∀ j, Integrable (fun ω => β (A.θ j ω)) ℙ)
    (i : Fin n)
    (hIC : (A.bidderProblem β hβ_meas i).HasTypeDeviationIC)
    (hK_neg : A.K_linear β < 0)
    (hU_eq : (A.bidderProblem β hβ_meas i).U A.toAuction.lowestType =
        (A.K_linear β) ^ 2 / (4 * A.α_coeff))
    (v : ℝ) (hv : v ∈ (A.bidderProblem β hβ_meas i).typeInterval)
    (h_bAP_nn : 0 ≤ (A.bidderProblem β hβ_meas i).allPayBid v)
    (h_strat_ge : -(A.K_linear β) / (2 * A.α_coeff) ≤ β v) :
    β v = strategyInterior A.α_coeff (-(A.K_linear β))
      ((A.bidderProblem β hβ_meas i).allPayBid v) := by
  let P : InteriorRegimeProblem := {
    A.toQuadraticCostProblem β hβ_meas hβ_int i with
    K_neg := hK_neg
    U_lowestType_eq := hU_eq
  }
  letI : BidderProblem.HasTypeDeviationIC P.toBidderProblem := hIC
  change P.strategy v = _
  exact P.interior_regime_strategy v hv h_bAP_nn h_strat_ge

end LinearScarcityAuction

end
