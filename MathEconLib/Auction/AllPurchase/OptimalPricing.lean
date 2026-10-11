module

public import MathEconLib.Auction.AllPurchase.LinearScarcity
public import MathEconLib.Auction.AllPurchase.ExplicitSolutions
public import MathEconLib.Auction.AllPurchase.RevenueDecomposition
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Interior quantity and pricing in all-purchase auctions

Motivated by Propositions 6.8 and 6.12 (§6.7.2) in Scott's notes. For real parameters
`φbar`, `α`, `c`, and `M`, and `n : ℕ`, define
`Q(p) = n(φbar − p)/(α(n+1)) + 2nM/((n+1)√α)`,
`Π(p) = (p − c) · Q(p)`, and `p* = (φbar + c + 2√α·M)/2`.

For `α > 0` and `n ≥ 1`, `p*` uniquely maximizes the defined `Π` over all real prices.
For a linear-scarcity auction with independent identical bounded atomless types, the
interior-regime assumptions identify `M` with the distribution-based moment
`𝔼[√(b^{AP}(V))]`, `Q` with expected aggregate purchases, and `Π` with actual bundled
profit at the posted price. The common strategy is measurable and strictly increasing,
purchases are integrable, and the representative bidder satisfies type-deviation IC
and the interior lowest-type utility condition. The quadratic root and the quantity
formula are derived from these assumptions.

The optimal value is an upper bound for the profit of each such auction, with equality
exactly when its posted price is `p*`. This does not construct an auction equilibrium at
another price or compare interior and boundary regimes.

## Main results

* `AllPurchase.sellerProfitInterior_le_at_optimal`: `Π(p) ≤ Π(p*)`.
* `AllPurchase.sellerProfitInterior_eq_at_optimal_iff`: `Π(p) = Π(p*) ↔ p = p*`.
* `AllPurchase.optimalPriceInterior_in_interior_regime`: for arbitrary parameters,
  `φbar − p* > (n−1)√α·M ↔ φbar − c > 2n√α·M`.
* `LinearScarcityAuction.expectedAggregateBid_eq_interiorMeanQuantity`: the quantity
  formula from interior incentives and the self-consistency equation.
* `LinearScarcityAuction.bundledProfit_eq_sellerProfitInterior`: actual bundled profit
  equals the defined profit formula at the auction's posted price.
* `LinearScarcityAuction.bundledProfit_le_interior_optimum`: the corresponding upper bound,
  with equality characterized by `bundledProfit_eq_interior_optimum_iff`.

For `b = n/(α(n+1)) > 0` and `Φ = φbar + 2√α·M`,
`Π(p) = b · (p − c) · (Φ − p)` and `Π(p*) − Π(p) = b · (p − p*)²`.
-/

namespace MathEconLib

@[expose] public section

namespace AllPurchase

open Real

/-- The quantity formula `Q(p) = n(φbar − p)/(α(n+1)) + 2nM/((n+1)√α)`.
`LinearScarcityAuction.expectedAggregateBid_eq_interiorMeanQuantity` identifies it with
expected aggregate purchases under the stated interior-regime assumptions. -/
noncomputable def interiorMeanQuantity (φbar α M : ℝ) (n : ℕ) (p : ℝ) : ℝ :=
  (n : ℝ) * (φbar - p) / (α * ((n : ℝ) + 1)) +
    2 * (n : ℝ) * M / (((n : ℝ) + 1) * sqrt α)

/-- The profit formula `Π(p) = (p − c) · interiorMeanQuantity φbar α M n p`. -/
noncomputable def sellerProfitInterior (φbar α c M : ℝ) (n : ℕ) (p : ℝ) : ℝ :=
  (p - c) * interiorMeanQuantity φbar α M n p

/-- Candidate price `p* = (φbar + c + 2√α·M)/2`. It uniquely maximizes
`sellerProfitInterior` over `ℝ` when `α > 0` and `n ≥ 1`. -/
noncomputable def optimalPriceInterior (φbar c α M : ℝ) : ℝ :=
  (φbar + c + 2 * sqrt α * M) / 2

/-! ### Factored form of the profit -/

/-- For `α > 0` and `n ≥ 1`,
`Π(p) = (n/(α(n+1))) · (p − c) · (φbar + 2√α·M − p)`. -/
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

/-- For `α > 0` and `n ≥ 1`, the candidate price maximizes the defined profit formula over `ℝ`. -/
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

/-- Algebraic interior-regime condition:
`φbar − p* > (n−1)√α·M ↔ φbar − c > 2n√α·M`, for arbitrary parameters. -/
theorem optimalPriceInterior_in_interior_regime
    (φbar α c M : ℝ) (n : ℕ) :
    ((n : ℝ) - 1) * sqrt α * M < φbar - optimalPriceInterior φbar c α M ↔
      2 * (n : ℝ) * sqrt α * M < φbar - c := by
  unfold optimalPriceInterior
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

end AllPurchase

/-! ### Distribution-based moment and aggregate purchases -/

open Real MeasureTheory ProbabilityTheory Set Finset

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} [NeZero n]

namespace Auction

variable (A : Auction Ω n) [A.HasIdenticalTypes]

/-- The square-root all-pay moment `M = 𝔼[√(b^{AP}(V₀))]`. It uses only the common
type distribution, its lower endpoint, and the number of bidders; no purchase strategy
or posted-price specification enters the definition. As with other Bochner integrals,
the definition is totalized; the interior-auction results below establish integrability. -/
noncomputable def expectedSqrtAllPayBid : ℝ :=
  𝔼[fun ω => sqrt (A.allPayBid (A.θ 0 ω))]

/-- The square-root all-pay moment is nonnegative. -/
theorem expectedSqrtAllPayBid_nonneg : 0 ≤ A.expectedSqrtAllPayBid := by
  exact integral_nonneg fun _ => sqrt_nonneg _

/-- Identical type distributions and an integrable measurable common strategy identify
expected aggregate purchases with `n` times the representative bidder's mean purchase. -/
theorem expectedAggregateBid_eq_mul_mean
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (hβ_int : ∀ j, Integrable (fun ω => β (A.θ j ω)) ℙ) :
    A.expectedAggregateBid β = (n : ℝ) * 𝔼[fun ω => β (A.θ 0 ω)] := by
  unfold expectedAggregateBid aggregateBid
  rw [integral_finset_sum _ (fun j _ => hβ_int j)]
  have hsym : ∀ j, 𝔼[fun ω => β (A.θ j ω)] = 𝔼[fun ω => β (A.θ 0 ω)] := by
    intro j
    rw [← integral_map (A.θ_measurable j).aemeasurable
          hβ_meas.aestronglyMeasurable,
        (HasIdenticalTypes.θ_identical j 0).map_eq,
        integral_map (A.θ_measurable 0).aemeasurable
          hβ_meas.aestronglyMeasurable]
  simp_rw [hsym]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Auction

namespace LinearScarcityAuction

variable [n.AtLeastTwo]
variable (A : LinearScarcityAuction Ω n)
variable [A.HasIdenticalTypes] [A.HasIndependentTypes]
variable [A.HasBoundedTypes] [A.HasAtomlessTypes]

/-- Interior purchases in terms of the distribution-based all-pay bid. The lowest-type
utility condition forces `β(lowestType) = −K/(2α)`, and strict monotonicity selects the
upper quadratic root. Thus no separate root-selection or all-pay-nonnegativity premise
is needed. The incentive condition concerns deviations to other types' prescribed bids. -/
theorem interior_regime_strategy_eq_allPayBid
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (hβ_mono : StrictMonoOn β (Icc A.lowestType A.highestType))
    (hβ_int : ∀ j, Integrable (fun ω => β (A.θ j ω)) ℙ)
    (i : Fin n)
    (hIC : (A.toBidderProblem A.spec.isUnitIntervalAllocation β i).HasTypeDeviationIC)
    (hK_neg : A.K_linear β < 0)
    (hU_eq : (A.toBidderProblem A.spec.isUnitIntervalAllocation β i).U
        (A.toBidderProblem A.spec.isUnitIntervalAllocation β i).lowestType =
        (A.K_linear β) ^ 2 / (4 * A.α_coeff))
    (v : ℝ) (hv : v ∈ Icc A.lowestType A.highestType) :
    β v = -(A.K_linear β) / (2 * A.α_coeff) +
      sqrt (A.toAuction.allPayBid v) / sqrt A.α_coeff := by
  let P : InteriorRegimeProblem := {
    A.toQuadraticCostProblem β hβ_meas hβ_int i with
    K_neg := hK_neg
    U_lowestType_eq := hU_eq
  }
  letI : BidderProblem.HasTypeDeviationIC P.toBidderProblem := hIC
  letI := hIC
  have hmem (w : ℝ) (hw : w ∈ Icc A.lowestType A.highestType) :
      w ∈ P.typeInterval := by
    change w ∈ Icc (A.θmin i) (A.θmax i)
    simpa only [Auction.θmin_eq_lowestType, Auction.θmax_eq_highestType] using hw
  have hAP (w : ℝ) (hw : w ∈ Icc A.lowestType A.highestType) :
      P.allPayBid w = A.toAuction.allPayBid w := by
    exact A.toAuction.toBidderProblem_allPayBid_eq
      A.spec.usesStrictHighestBidAllocation hβ_mono hβ_meas i hw
  have hα_ne : A.α_coeff ≠ 0 := ne_of_gt A.α_pos
  have hsquare (w : ℝ) (hw : w ∈ Icc A.lowestType A.highestType) :
      A.α_coeff * (β w + A.K_linear β / (2 * A.α_coeff)) ^ 2 =
        A.toAuction.allPayBid w := by
    have hquad := P.interior_regime_quadratic w (hmem w hw)
    rw [hAP w hw] at hquad
    change A.α_coeff * (β w) ^ 2 + A.K_linear β * β w =
      A.toAuction.allPayBid w - (A.K_linear β) ^ 2 / (4 * A.α_coeff) at hquad
    have hcomplete :
        A.α_coeff * (β w + A.K_linear β / (2 * A.α_coeff)) ^ 2 =
          A.α_coeff * (β w) ^ 2 + A.K_linear β * β w +
            (A.K_linear β) ^ 2 / (4 * A.α_coeff) := by
      field_simp
      ring
    linarith
  have hlo_mem : A.lowestType ∈ Icc A.lowestType A.highestType :=
    ⟨le_rfl, hv.1.trans hv.2⟩
  have hlo_sq := hsquare A.lowestType hlo_mem
  rw [A.toAuction.allPayBid_lowestType] at hlo_sq
  have hlo_zero : β A.lowestType + A.K_linear β / (2 * A.α_coeff) = 0 := by
    have hsq : (β A.lowestType + A.K_linear β / (2 * A.α_coeff)) ^ 2 = 0 :=
      (mul_eq_zero.mp hlo_sq).resolve_left hα_ne
    exact pow_eq_zero_iff two_ne_zero |>.mp hsq
  have hroot : -(A.K_linear β) / (2 * A.α_coeff) ≤ β v := by
    have := hβ_mono.monotoneOn hlo_mem hv hv.1
    rw [neg_div]
    linarith
  have hAP_nn : 0 ≤ P.allPayBid v := by
    rw [hAP v hv, ← hsquare v hv]
    exact mul_nonneg A.α_pos.le (sq_nonneg _)
  have hstrategy := P.interior_regime_strategy v (hmem v hv) hAP_nn hroot
  rw [hAP v hv] at hstrategy
  change β v = AllPurchase.strategyInterior A.α_coeff (-(A.K_linear β))
    (A.toAuction.allPayBid v) at hstrategy
  simpa only [AllPurchase.strategyInterior, sqrt_div' _ A.α_pos.le] using hstrategy

variable (β : ℝ → ℝ) (hβ_meas : Measurable β)
variable (hβ_mono : StrictMonoOn β (Icc A.lowestType A.highestType))
variable (hβ_int : ∀ j, Integrable (fun ω => β (A.θ j ω)) ℙ)
variable (hIC : (A.toBidderProblem A.spec.isUnitIntervalAllocation β 0).HasTypeDeviationIC)
variable (hK_neg : A.K_linear β < 0)
variable (hU_eq : (A.toBidderProblem A.spec.isUnitIntervalAllocation β 0).U
    (A.toBidderProblem A.spec.isUnitIntervalAllocation β 0).lowestType =
    (A.K_linear β) ^ 2 / (4 * A.α_coeff))

include hβ_meas hβ_mono hβ_int hIC hK_neg hU_eq

/-- The distribution-based square-root all-pay bid is integrable under the interior
assumptions: the strategy formula expresses it as a constant multiple of an integrable
purchase plus a constant. -/
theorem integrable_sqrt_allPayBid_of_interior (j : Fin n) :
    Integrable (fun ω => sqrt (A.toAuction.allPayBid (A.θ j ω))) ℙ := by
  have hs_ne : sqrt A.α_coeff ≠ 0 := ne_of_gt (sqrt_pos.mpr A.α_pos)
  have hfun : (fun ω => sqrt (A.toAuction.allPayBid (A.θ j ω))) =
      (fun ω => sqrt A.α_coeff *
        (β (A.θ j ω) + A.K_linear β / (2 * A.α_coeff))) := by
    funext ω
    have hmem : A.θ j ω ∈ Icc A.lowestType A.highestType := by
      simpa only [Auction.θmin_eq_lowestType, Auction.θmax_eq_highestType] using
        (Auction.HasBoundedTypes.θ_in (A := A.toAuction) j ω)
    have h := A.interior_regime_strategy_eq_allPayBid β hβ_meas hβ_mono hβ_int
      0 hIC hK_neg hU_eq (A.θ j ω) hmem
    have hdiv : β (A.θ j ω) + A.K_linear β / (2 * A.α_coeff) =
        sqrt (A.toAuction.allPayBid (A.θ j ω)) / sqrt A.α_coeff := by
      rw [neg_div] at h
      linarith
    simpa only [mul_comm] using ((eq_div_iff hs_ne).mp hdiv).symm
  rw [hfun]
  exact ((hβ_int j).add (integrable_const _)).const_mul _

/-- Taking expectations of the interior strategy and solving
`K = p − φbar + α(n−1)μ` determines the representative bidder's mean purchase. -/
theorem meanPurchase_eq_interior :
    A.meanPurchase β =
      (A.φ_bar - A.spec.price) / (A.α_coeff * ((n : ℝ) + 1)) +
        2 * A.toAuction.expectedSqrtAllPayBid / (((n : ℝ) + 1) * sqrt A.α_coeff) := by
  have hs_int := A.integrable_sqrt_allPayBid_of_interior β hβ_meas hβ_mono hβ_int
    hIC hK_neg hU_eq 0
  have hfun : (fun ω => β (A.θ 0 ω)) =
      (fun ω => -(A.K_linear β) / (2 * A.α_coeff) +
        sqrt (A.toAuction.allPayBid (A.θ 0 ω)) / sqrt A.α_coeff) := by
    funext ω
    apply A.interior_regime_strategy_eq_allPayBid β hβ_meas hβ_mono hβ_int
      0 hIC hK_neg hU_eq
    simpa only [Auction.θmin_eq_lowestType, Auction.θmax_eq_highestType] using
      (Auction.HasBoundedTypes.θ_in (A := A.toAuction) 0 ω)
  have hmean : A.meanPurchase β = -(A.K_linear β) / (2 * A.α_coeff) +
      A.toAuction.expectedSqrtAllPayBid / sqrt A.α_coeff := by
    unfold meanPurchase
    rw [hfun, integral_add (integrable_const _) (hs_int.div_const _),
      integral_const, probReal_univ, one_smul, integral_div]
    rfl
  have hα_ne : A.α_coeff ≠ 0 := ne_of_gt A.α_pos
  have hs_ne : sqrt A.α_coeff ≠ 0 := ne_of_gt (sqrt_pos.mpr A.α_pos)
  have hn1_ne : (n : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < n + 1)
  unfold K_linear at hmean
  field_simp [hα_ne, hs_ne, hn1_ne] at hmean ⊢
  nlinarith

/-- Under the interior incentive and baseline-utility assumptions, expected aggregate
purchases equal the quantity formula at the actual posted price, with the moment taken
from the type distribution's all-pay bid. Only the representative bidder's IC and
baseline utility are needed because all bidders use the common strategy. -/
theorem expectedAggregateBid_eq_interiorMeanQuantity :
    A.toAuction.expectedAggregateBid β =
      AllPurchase.interiorMeanQuantity A.φ_bar A.α_coeff
        A.toAuction.expectedSqrtAllPayBid n A.spec.price := by
  rw [A.toAuction.expectedAggregateBid_eq_mul_mean β hβ_meas hβ_int]
  change (n : ℝ) * A.meanPurchase β = _
  rw [A.meanPurchase_eq_interior β hβ_meas hβ_mono hβ_int hIC hK_neg hU_eq]
  unfold AllPurchase.interiorMeanQuantity
  ring

/-- Actual bundled profit at the auction's posted price is the interior profit formula
with the distribution-based square-root all-pay moment. This is an identification for
the supplied auction and strategy, not an existence statement at other prices. -/
theorem bundledProfit_eq_sellerProfitInterior (c : ℝ) :
    A.toAuction.bundledProfit A.spec β c =
      AllPurchase.sellerProfitInterior A.φ_bar A.α_coeff c
        A.toAuction.expectedSqrtAllPayBid n A.spec.price := by
  unfold Auction.bundledProfit AllPurchase.sellerProfitInterior
  rw [A.expectedAggregateBid_eq_interiorMeanQuantity β hβ_meas hβ_mono hβ_int
    hIC hK_neg hU_eq]

/-- The algebraic interior optimum bounds the actual profit of a supplied interior
auction. This does not assert the existence of an equilibrium at the optimizing price. -/
theorem bundledProfit_le_interior_optimum (c : ℝ) :
    A.toAuction.bundledProfit A.spec β c ≤
      AllPurchase.sellerProfitInterior A.φ_bar A.α_coeff c
        A.toAuction.expectedSqrtAllPayBid n
        (AllPurchase.optimalPriceInterior A.φ_bar c A.α_coeff
          A.toAuction.expectedSqrtAllPayBid) := by
  rw [A.bundledProfit_eq_sellerProfitInterior β hβ_meas hβ_mono hβ_int
    hIC hK_neg hU_eq c]
  exact AllPurchase.sellerProfitInterior_le_at_optimal A.α_pos
    (by have := Nat.AtLeastTwo.prop (n := n); omega) A.spec.price

/-- An interior auction attains the algebraic optimum exactly when its actual posted
price equals the candidate price. No cross-price auction family is assumed. -/
theorem bundledProfit_eq_interior_optimum_iff (c : ℝ) :
    A.toAuction.bundledProfit A.spec β c =
        AllPurchase.sellerProfitInterior A.φ_bar A.α_coeff c
          A.toAuction.expectedSqrtAllPayBid n
          (AllPurchase.optimalPriceInterior A.φ_bar c A.α_coeff
            A.toAuction.expectedSqrtAllPayBid) ↔
      A.spec.price = AllPurchase.optimalPriceInterior A.φ_bar c A.α_coeff
        A.toAuction.expectedSqrtAllPayBid := by
  rw [A.bundledProfit_eq_sellerProfitInterior β hβ_meas hβ_mono hβ_int
    hIC hK_neg hU_eq c]
  exact AllPurchase.sellerProfitInterior_eq_at_optimal_iff A.α_pos
    (by have := Nat.AtLeastTwo.prop (n := n); omega) A.spec.price

end LinearScarcityAuction

end

end MathEconLib
