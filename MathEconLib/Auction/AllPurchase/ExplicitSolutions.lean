module

public import MathEconLib.Auction.AllPurchase.LinearScarcity
public import MathEconLib.BidderProblem.TypeDeviationIC
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Explicit strategy formulas for all-purchase auctions

Strategies for bidder problems with linear or quadratic net cost satisfy
`cost(strategy(v)) = allPayBid(v) − U(lowestType)` under type-deviation incentive compatibility.
The resulting formulas express purchases in terms of the all-pay bid and the lowest type's utility.

For quadratic cost `αb² + Kb` with `α > 0`, the boundary regime has `U(lowestType) = 0`, while the
interior regime has `K < 0` and `U(lowestType) = K²/(4α)`. Sign and lower-bound assumptions select
the corresponding quadratic root. These formulas also apply to induced bidder problems in
all-purchase auctions with linear scarcity and identical type distributions.

## Main definitions

* `AllPurchase.strategyBoundary`: the boundary-regime purchase formula.
* `AllPurchase.strategyInterior`: the interior-regime purchase formula.

## Main statements

* `LinearCostProblem.constant_scarcity_strategy`: purchases equal the all-pay bid divided by
  positive net cost per unit in the boundary regime.
* `QuadraticCostProblem.boundary_regime_strategy`: the boundary formula for nonnegative purchases
  and all-pay bids when `K ≥ 0`.
* `InteriorRegimeProblem.interior_regime_strategy`: the interior formula for purchases at least
  `−K/(2α)` and nonnegative all-pay bids.
* `LinearScarcityAuction.boundary_regime_strategy_auction` and
  `LinearScarcityAuction.interior_regime_strategy_auction`: the corresponding auction formulas.

## Tags

all-purchase auctions, scarcity, incentive compatibility, strategy formulas
-/

namespace MathEconLib

@[expose] public section

open Real

/-! ## Algebraic strategy formulas -/

namespace AllPurchase

/-- Quadratic net cost under linear scarcity: `C(b) = α · b² + K · b`. -/
private noncomputable def netCostLinear (α K b : ℝ) : ℝ := α * b ^ 2 + K * b

/-- For nonzero `α`, quadratic net cost equals `α · (b + K/(2α))² - K²/(4α)`. -/
private theorem netCostLinear_completed_square (α K b : ℝ) (hα : α ≠ 0) :
    netCostLinear α K b = α * (b + K / (2 * α)) ^ 2 - K ^ 2 / (4 * α) := by
  unfold netCostLinear; field_simp; ring

/-- Boundary-regime purchase formula in terms of the all-pay bid `bAP`:
`(−K + √(K² + 4α · bAP)) / (2α)`. -/
noncomputable def strategyBoundary (α K bAP : ℝ) : ℝ :=
  (-K + sqrt (K ^ 2 + 4 * α * bAP)) / (2 * α)

/-- Interior-regime purchase formula in terms of the all-pay bid `bAP`, with `A = −K`:
`A/(2α) + √(bAP/α)`. -/
noncomputable def strategyInterior (α A bAP : ℝ) : ℝ :=
  A / (2 * α) + sqrt (bAP / α)

/-- For `α > 0` and `c ≥ 0`, the boundary formula gives a root of `αy² + Ky = c`. -/
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

/-- The boundary formula is nonnegative when `α > 0`, `K ≥ 0`, and `bAP ≥ 0`. -/
theorem strategyBoundary_nonneg (α K bAP : ℝ)
    (hα : 0 < α) (hK : 0 ≤ K) (hbAP : 0 ≤ bAP) :
    0 ≤ strategyBoundary α K bAP := by
  unfold strategyBoundary
  apply div_nonneg _ (by linarith)
  have : K ≤ sqrt (K ^ 2 + 4 * α * bAP) := by
    calc
      K = sqrt (K ^ 2) := (sqrt_sq hK).symm
      _ ≤ sqrt (K ^ 2 + 4 * α * bAP) := sqrt_le_sqrt (by nlinarith)
  linarith

end AllPurchase

/-! ## Strategies for bidder problems -/

open AllPurchase

/-! ### Constant scarcity -/

/-- Under type-deviation incentive compatibility, linear net cost with `p_net > 0`, and
`U(lowestType) = 0`, purchases satisfy `strategy(v) = allPayBid(v) / p_net` on the type interval. -/
theorem LinearCostProblem.constant_scarcity_strategy (P : LinearCostProblem)
    [BidderProblem.HasTypeDeviationIC P.toBidderProblem]
    [BidderProblem.IsBoundaryRegime P.toBidderProblem]
    (v : ℝ) (hv : v ∈ P.typeInterval) :
    P.strategy v = P.allPayBid v / P.p_net := by
  have hid := P.toBidderProblem.netPaymentIdentity v hv
  rw [P.cost_eq, BidderProblem.IsBoundaryRegime.U_lowestType_zero, sub_zero] at hid
  rw [← hid, mul_div_cancel_left₀ _ (ne_of_gt P.p_net_pos)]

/-! ### Boundary regime -/

/-- Under type-deviation incentive compatibility and `U(lowestType) = 0`, a quadratic-cost strategy
satisfies `α · β(v)² + K · β(v) = allPayBid(v)` on the type interval. -/
theorem QuadraticCostProblem.boundary_regime_quadratic (P : QuadraticCostProblem)
    [BidderProblem.HasTypeDeviationIC P.toBidderProblem]
    [BidderProblem.IsBoundaryRegime P.toBidderProblem]
    (v : ℝ) (hv : v ∈ P.typeInterval) :
    P.α_coeff * (P.strategy v) ^ 2 + P.K_param * P.strategy v =
      P.allPayBid v := by
  have hid := P.toBidderProblem.netPaymentIdentity v hv
  rw [P.cost_eq, BidderProblem.IsBoundaryRegime.U_lowestType_zero, sub_zero] at hid
  linarith

/-- Under type-deviation incentive compatibility, quadratic net cost, and `U(lowestType) = 0`, the
strategy equals `(−K + √(K² + 4α · allPayBid(v))) / (2α)` at types in the interval where the
strategy and all-pay bid are nonnegative, provided `K ≥ 0`. -/
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

/-! ### Interior regime -/

/-- Under type-deviation incentive compatibility in the interior regime, the strategy satisfies
`α · β(v)² + K · β(v) = allPayBid(v) − K²/(4α)` on the type interval. -/
theorem InteriorRegimeProblem.interior_regime_quadratic (P : InteriorRegimeProblem)
    [BidderProblem.HasTypeDeviationIC P.toBidderProblem]
    (v : ℝ) (hv : v ∈ P.typeInterval) :
    P.α_coeff * (P.strategy v) ^ 2 + P.K_param * P.strategy v =
      P.allPayBid v - P.K_param ^ 2 / (4 * P.α_coeff) := by
  have hid := P.toBidderProblem.netPaymentIdentity v hv
  rw [P.cost_eq, P.U_lowestType_eq] at hid
  linarith

/-- Under type-deviation incentive compatibility in the interior regime, the strategy equals
`−K/(2α) + √(allPayBid(v)/α)` at types in the interval where `allPayBid(v) ≥ 0` and
`strategy(v) ≥ −K/(2α)`. -/
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

/-! ## Strategies in all-purchase auctions with linear scarcity -/

open MeasureTheory ProbabilityTheory AllPurchase

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} [NeZero n] [n.AtLeastTwo]

namespace LinearScarcityAuction

variable (A : LinearScarcityAuction Ω n)

/-- In an all-purchase auction with linear scarcity and identical type distributions, a measurable
common strategy `β` with integrable purchases satisfies
`β(v) = (−K + √(K² + 4α · allPayBid(v))) / (2α)` when bidder `i`'s induced problem is
type-deviation incentive compatible, `U(lowestType) = 0`, and `K ≥ 0`. Here `v` lies in the
bidder's type interval, and both `β(v)` and the induced all-pay bid are nonnegative. -/
theorem boundary_regime_strategy_auction
    [A.HasIdenticalTypes]
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (hβ_int : ∀ j, Integrable (fun ω => β (A.θ j ω)) ℙ)
    (i : Fin n)
    (hIC : (A.toBidderProblem A.spec.isUnitIntervalAllocation β i).HasTypeDeviationIC)
    (hBR : (A.toBidderProblem A.spec.isUnitIntervalAllocation β i).IsBoundaryRegime)
    (hK : 0 ≤ A.K_linear β)
    (v : ℝ) (hv : v ∈ (A.toBidderProblem A.spec.isUnitIntervalAllocation β i).typeInterval)
    (h_bAP_nn : 0 ≤ (A.toBidderProblem A.spec.isUnitIntervalAllocation β i).allPayBid v)
    (h_strat_nn : 0 ≤ β v) :
    β v = strategyBoundary A.α_coeff (A.K_linear β)
      ((A.toBidderProblem A.spec.isUnitIntervalAllocation β i).allPayBid v) := by
  let P := A.toQuadraticCostProblem β hβ_meas hβ_int i
  letI : BidderProblem.HasTypeDeviationIC P.toBidderProblem := hIC
  letI : BidderProblem.IsBoundaryRegime P.toBidderProblem := hBR
  change P.strategy v = _
  exact P.boundary_regime_strategy hK v hv h_bAP_nn h_strat_nn

/-- In an all-purchase auction with linear scarcity and identical type distributions, a measurable
common strategy `β` with integrable purchases satisfies `β(v) = −K/(2α) + √(allPayBid(v)/α)` when
bidder `i`'s induced problem is type-deviation incentive compatible, `K < 0`, and
`U(lowestType) = K²/(4α)`. Here `v` lies in the bidder's type interval, the induced all-pay bid is
nonnegative, and `β(v) ≥ −K/(2α)`. -/
theorem interior_regime_strategy_auction
    [A.HasIdenticalTypes]
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (hβ_int : ∀ j, Integrable (fun ω => β (A.θ j ω)) ℙ)
    (i : Fin n)
    (hIC : (A.toBidderProblem A.spec.isUnitIntervalAllocation β i).HasTypeDeviationIC)
    (hK_neg : A.K_linear β < 0)
    (hU_eq : (A.toBidderProblem A.spec.isUnitIntervalAllocation β i).U
        (A.toBidderProblem A.spec.isUnitIntervalAllocation β i).lowestType =
        (A.K_linear β) ^ 2 / (4 * A.α_coeff))
    (v : ℝ) (hv : v ∈ (A.toBidderProblem A.spec.isUnitIntervalAllocation β i).typeInterval)
    (h_bAP_nn : 0 ≤ (A.toBidderProblem A.spec.isUnitIntervalAllocation β i).allPayBid v)
    (h_strat_ge : -(A.K_linear β) / (2 * A.α_coeff) ≤ β v) :
    β v = strategyInterior A.α_coeff (-(A.K_linear β))
      ((A.toBidderProblem A.spec.isUnitIntervalAllocation β i).allPayBid v) := by
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

end MathEconLib
