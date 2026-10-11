module

public import MathEconLib.Auction.AllPurchase
public import MathEconLib.BidderProblem
public import MathEconLibExamples.AllPurchase.Basic
public import MathEconLibExamples.AllPurchase.UniformProbability

/-!
# An interior equilibrium with 2 uniform bidders

2 bidders have independent uniform values on `[0, 2]`. The posted edition price is `2`,
scarcity value at total purchases `B` is `3 - B`, and the unique highest purchaser receives the
prize. The strategy `β(v) = 1/6 + v/2` is optimal against every real-valued unilateral bid, not
only bids in the strategy's range. A bid `b` gives interim utility
`v · q(b) - b² + b/3`, accounting for both the prize and edition value.
Each bidder's expected purchase is `2/3`, marginal net cost at purchases `0` is `-1/3`, and
lowest-type utility is `1/36`.

The final results apply the auction-level interior quantity and seller-profit theorems to this
fully specified model. Expected total purchases are `4/3`, and profit at production cost `0` is
`8/3`; the posted price realizes the algebraic interior optimum. This application does not assert
an optimum over other equilibrium regimes.

The welfare results evaluate this privately optimal, prize-aware strategy. Expected edition
welfare is `37/18`, the gap from the edition first best is `7/36`, and the variance penalty is
`1/6`. Compared with editions-only Cournot purchases, the prize raises expected total purchases
and edition welfare, so the contest gap is `-1/2`. The welfare comparison concerns editions;
it does not include the prize's value.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace MathEconLib.Examples.AllPurchase.UniformTwoBidder

open UniformProbability

/-- The shared all-purchase rules with independent uniform values on `[0, 2]`. -/
def model : LinearScarcityAuction Ω 2 :=
  auction value measurable_value

instance : Auction.HasIndependentTypes model.toAuction where
  θ_indep := independent_values

instance : Auction.HasIdenticalTypes model.toAuction where
  θ_identical := identical_values
  θmin_eq _ := rfl
  θmax_eq _ := rfl

instance : Auction.HasBoundedTypes model.toAuction where
  θ_in := value_mem

instance : Auction.HasAtomlessTypes model.toAuction where
  θ_noAtoms := noAtoms_value 0

instance : Auction.HasDensity model.toAuction where
  θ_hasPDF := hasPDF_value

/-- Each bidder buys a positive baseline quantity plus `1/2` of their value. -/
def strategy (v : ℝ) : ℝ := 1 / 6 + v / 2

theorem strategy_measurable : Measurable strategy := by
  unfold strategy
  fun_prop

theorem strategy_strictMono : StrictMono strategy := by
  intro v w hvw
  dsimp [strategy]
  linarith

theorem strategy_strictMonoOn :
    StrictMonoOn strategy (Icc model.lowestType model.highestType) := by
  intro v _ w _ hvw
  exact strategy_strictMono hvw

theorem strategy_integrable (i : Fin 2) :
    Integrable (fun ω => strategy (model.θ i ω)) ℙ := by
  exact (integrable_const (1 / 6 : ℝ)).add ((integrable_value i).div_const 2)

theorem mean_strategy (i : Fin 2) :
    𝔼[fun ω => strategy (model.θ i ω)] = (2 : ℝ) / 3 := by
  change (∫ ω, (1 / 6 : ℝ) + value i ω / 2 ∂ℙ) = 2 / 3
  rw [integral_add (integrable_const _) ((integrable_value i).div_const 2),
    integral_div 2 (value i), integral_value]
  norm_num

theorem meanPurchase_eq : model.meanPurchase strategy = (2 : ℝ) / 3 :=
  mean_strategy 0

theorem K_eq : model.K_linear strategy = -(1 : ℝ) / 3 := by
  rw [LinearScarcityAuction.K_linear, meanPurchase_eq]
  change (2 : ℝ) - 3 + 1 * (2 - 1) * (2 / 3) = -(1 : ℝ) / 3
  norm_num

theorem commonCDF_eq (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 2) :
    model.commonCDF v = v / 2 :=
  cdf_value 0 v hv

/-- The prescribed bid of type `v` wins with probability `v/2`. -/
theorem winning_probability (i : Fin 2) (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 2) :
    model.q_strat strategy i (strategy v) = v / 2 := by
  rw [model.toAuction.q_strat_at_strictMono_eq
    model.spec.usesStrictHighestBidAllocation strategy_strictMonoOn strategy_measurable i hv]
  norm_num [commonCDF_eq v hv]

/-- Expected net payment after edition resale value is `b² - b/3`; gross expenditure is `2b`. -/
theorem interim_payment (i : Fin 2) (b : ℝ) :
    model.p_strat strategy i b = b ^ 2 - b / 3 := by
  rw [model.p_strat_eq_quadratic strategy strategy_measurable strategy_integrable i b, K_eq]
  change 1 * b ^ 2 + (-(1 : ℝ) / 3) * b = b ^ 2 - b / 3
  ring

/-- The actual interim decision problem induced by the auction and opponents' strategy. -/
abbrev problem (i : Fin 2) : BidderProblem :=
  model.toBidderProblem model.spec.isUnitIntervalAllocation strategy i

theorem payoff_on_strategy (i : Fin 2) (v w : ℝ) (hw : w ∈ Icc (0 : ℝ) 2) :
    (problem i).payoff v (strategy w) = v * w / 2 - w ^ 2 / 4 + 1 / 36 := by
  change v * model.q_strat strategy i (strategy w) -
    model.p_strat strategy i (strategy w) = _
  rw [winning_probability i w hw, interim_payment]
  dsimp [strategy]
  ring

theorem utility_eq (i : Fin 2) (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 2) :
    (problem i).U v = v ^ 2 / 4 + 1 / 36 := by
  change (problem i).payoff v (strategy v) = _
  rw [payoff_on_strategy i v v hv]
  ring

/-- Mimicking another supported value cannot increase interim utility. -/
instance typeDeviationIC (i : Fin 2) : (problem i).HasTypeDeviationIC where
  typeDeviationIC v hv w hw := by
    change (problem i).payoff v (strategy w) ≤ (problem i).payoff v (strategy v)
    rw [payoff_on_strategy i v w hw, payoff_on_strategy i v v hv]
    nlinarith [sq_nonneg (v - w)]

private theorem winning_probability_below (i : Fin 2) (b : ℝ) (hb : b ≤ 1 / 6) :
    model.q_strat strategy i b = 0 := by
  have hset : {v ∈ Icc (0 : ℝ) 2 | strategy v < b} = ∅ := by
    ext v
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
    rintro ⟨hv, hlt⟩
    dsimp [strategy] at hlt
    linarith [hv.1]
  have hthreshold : bidThreshold strategy 0 2 b = 0 := by
    rw [bidThreshold, hset]
    simp
  rw [model.toAuction.q_strat_eq_cdf_pow model.spec.usesStrictHighestBidAllocation
    strategy_strictMonoOn.monotoneOn strategy_measurable i b]
  change model.commonCDF (bidThreshold strategy 0 2 b) ^ (2 - 1) = 0
  rw [hthreshold, commonCDF_eq 0 (by norm_num)]
  norm_num

/-- Every real-valued unilateral bid is weakly worse than the prescribed bid.
This also verifies off-range deviations, including negative purchases. -/
instance universalIC (i : Fin 2) : (problem i).HasUniversalIC Set.univ where
  strategyInS _ _ := Set.mem_univ _
  universalIC v hv b _ := by
    change (problem i).payoff v b ≤ (problem i).U v
    rw [utility_eq i v hv]
    change v * model.q_strat strategy i b - model.p_strat strategy i b ≤ _
    rw [interim_payment]
    by_cases hb : b ≤ 1 / 6
    · rw [winning_probability_below i b hb]
      nlinarith [sq_nonneg (b - 1 / 6), sq_nonneg v]
    · by_cases hb' : b ≤ 7 / 6
      · have hw : 2 * b - 1 / 3 ∈ Icc (0 : ℝ) 2 := by constructor <;> linarith
        have hrepr : strategy (2 * b - 1 / 3) = b := by dsimp [strategy]; ring
        have hq := winning_probability i (2 * b - 1 / 3) hw
        rw [hrepr] at hq
        rw [hq]
        nlinarith [sq_nonneg (b - 1 / 6 - v / 2)]
      · have hq := (model.q_strat_range model.spec.isUnitIntervalAllocation strategy i b).2
        have hv0 : 0 ≤ v := hv.1
        have hmul := mul_le_mul_of_nonneg_left hq hv0
        nlinarith [sq_nonneg (b - 7 / 6), sq_nonneg (v / 2 - 1)]

theorem lowest_utility (i : Fin 2) : (problem i).U (problem i).lowestType = 1 / 36 := by
  change (problem i).U 0 = 1 / 36
  simpa using utility_eq i 0 (by norm_num)

theorem K_neg : model.K_linear strategy < 0 := by rw [K_eq]; norm_num

theorem interior_utility :
    (problem 0).U (problem 0).lowestType =
      model.K_linear strategy ^ 2 / (4 * model.α_coeff) := by
  rw [lowest_utility, K_eq]
  change (1 : ℝ) / 36 = (-(1 : ℝ) / 3) ^ 2 / (4 * 1)
  norm_num

/-- The common all-pay benchmark bid is `v²/4`. -/
theorem allPayBid_eq (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 2) :
    model.allPayBid v = v ^ 2 / 4 := by
  have h := model.toAuction.allPayBid_uniform 2 (by norm_num) rfl commonCDF_eq v hv
  norm_num at h
  convert h using 1
  ring

theorem sqrt_allPayBid_eq (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 2) :
    Real.sqrt (model.allPayBid v) = v / 2 := by
  rw [allPayBid_eq v hv]
  have hsq : v ^ 2 / 4 = (v / 2) ^ 2 := by ring
  rw [hsq, Real.sqrt_sq (by linarith [hv.1])]

theorem expectedSqrtAllPayBid_eq : model.toAuction.expectedSqrtAllPayBid = 1 / 2 := by
  change (∫ ω, Real.sqrt (model.allPayBid (value 0 ω)) ∂ℙ) = 1 / 2
  calc
    (∫ ω, Real.sqrt (model.allPayBid (value 0 ω)) ∂ℙ) =
        ∫ ω, value 0 ω / 2 ∂ℙ := by
      apply integral_congr_ae
      exact ae_of_all _ fun ω => sqrt_allPayBid_eq (value 0 ω) (value_mem 0 ω)
    _ = 1 / 2 := by rw [integral_div, integral_value]

/-- Applying the interior quantity theorem gives expected aggregate purchases `4/3`. -/
theorem expectedAggregateBid_eq : model.expectedAggregateBid strategy = 4 / 3 := by
  have h := model.expectedAggregateBid_eq_interiorMeanQuantity strategy strategy_measurable
    strategy_strictMonoOn strategy_integrable (typeDeviationIC 0) K_neg interior_utility
  rw [expectedSqrtAllPayBid_eq] at h
  change model.expectedAggregateBid strategy =
    MathEconLib.AllPurchase.interiorMeanQuantity 3 1 (1 / 2) 2 2 at h
  norm_num [MathEconLib.AllPurchase.interiorMeanQuantity] at h
  exact h

/-- Applying the auction-to-profit bridge gives profit `8/3` at production cost `0`. -/
theorem bundledProfit_eq : model.bundledProfit model.spec strategy 0 = 8 / 3 := by
  have h := model.bundledProfit_eq_sellerProfitInterior strategy strategy_measurable
    strategy_strictMonoOn strategy_integrable (typeDeviationIC 0) K_neg interior_utility 0
  rw [expectedSqrtAllPayBid_eq] at h
  change model.bundledProfit model.spec strategy 0 =
    MathEconLib.AllPurchase.sellerProfitInterior 3 1 0 (1 / 2) 2 2 at h
  norm_num [MathEconLib.AllPurchase.sellerProfitInterior,
    MathEconLib.AllPurchase.interiorMeanQuantity] at h
  exact h

/-- The actual posted price is the candidate price of the interior pricing theorem. -/
theorem postedPrice_eq_optimal :
    model.spec.price = MathEconLib.AllPurchase.optimalPriceInterior
      model.φ_bar 0 model.α_coeff model.toAuction.expectedSqrtAllPayBid := by
  rw [expectedSqrtAllPayBid_eq]
  change (2 : ℝ) = MathEconLib.AllPurchase.optimalPriceInterior 3 0 1 (1 / 2)
  norm_num [MathEconLib.AllPurchase.optimalPriceInterior]

/-- The concrete equilibrium realizes the interior profit bound. -/
theorem bundledProfit_eq_interior_optimum :
    model.bundledProfit model.spec strategy 0 =
      MathEconLib.AllPurchase.sellerProfitInterior model.φ_bar model.α_coeff 0
        model.toAuction.expectedSqrtAllPayBid 2
        (MathEconLib.AllPurchase.optimalPriceInterior
          model.φ_bar 0 model.α_coeff model.toAuction.expectedSqrtAllPayBid) := by
  exact (model.bundledProfit_eq_interior_optimum_iff strategy strategy_measurable
    strategy_strictMonoOn strategy_integrable (typeDeviationIC 0) K_neg interior_utility 0).2
      postedPrice_eq_optimal

/-! ## Edition welfare at privately optimal purchases -/

/-- The prescribed quantity maximizes the bidder's prize-aware interim utility over all real
purchases, with the net payment written explicitly. -/
theorem prize_aware_best_response (i : Fin 2) (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 2)
    (b : ℝ) :
    v * model.q_strat strategy i b - (b ^ 2 - b / 3) ≤ v ^ 2 / 4 + 1 / 36 := by
  have h := (universalIC i).universalIC v hv b (Set.mem_univ b)
  change (problem i).payoff v b ≤ (problem i).U v at h
  rw [utility_eq i v hv] at h
  change v * model.q_strat strategy i b - model.p_strat strategy i b ≤ _ at h
  rwa [interim_payment] at h

/-- Total equilibrium purchases are an affine function of the 2 independent values. -/
theorem aggregate_formula :
    model.aggregateBid strategy =
      fun ω => (1 / 3 : ℝ) + (1 / 2 : ℝ) * (value 0 ω + value 1 ω) := by
  funext ω
  simp only [Auction.aggregateBid, Fin.sum_univ_two]
  change strategy (value 0 ω) + strategy (value 1 ω) = _
  dsimp [strategy]
  ring

private theorem value_memLp (i : Fin 2) : MemLp (value i) 2 ℙ :=
  memLp_of_bounded (ae_of_all _ (value_mem i)) (measurable_value i).aestronglyMeasurable 2

/-- Equilibrium aggregate purchases are square-integrable. -/
theorem aggregate_memLp : MemLp (model.aggregateBid strategy) 2 ℙ := by
  rw [aggregate_formula]
  exact (memLp_const (1 / 3 : ℝ)).add
    (((value_memLp 0).add (value_memLp 1)).const_mul (1 / 2 : ℝ))

private theorem variance_value (i : Fin 2) : variance (value i) ℙ = 1 / 3 := by
  rw [variance_eq_sub (value_memLp i)]
  change (∫ ω, value i ω ^ 2 ∂ℙ) - (∫ ω, value i ω ∂ℙ) ^ 2 = 1 / 3
  rw [integral_value_sq, integral_value]
  norm_num

/-- Independence gives aggregate purchase variance `1/6`. -/
theorem aggregate_variance : variance (model.aggregateBid strategy) ℙ = 1 / 6 := by
  have hsum : variance (fun ω => value 0 ω + value 1 ω) ℙ = 2 / 3 := by
    rw [IndepFun.variance_fun_add (value_memLp 0) (value_memLp 1)
      (independent_values.indepFun (by decide : (0 : Fin 2) ≠ 1)),
      variance_value, variance_value]
    norm_num
  rw [aggregate_formula,
    variance_const_add
      (measurable_const.mul ((measurable_value 0).add (measurable_value 1))).aestronglyMeasurable,
    variance_const_mul, hsum]
  norm_num

/-- The second moment of actual aggregate purchases is `35/18`. -/
theorem expectedAggregateBidSq_eq : model.expectedAggregateBidSq strategy = 35 / 18 := by
  have h := variance_eq_sub aggregate_memLp
  change variance (model.aggregateBid strategy) ℙ =
    model.expectedAggregateBidSq strategy - model.expectedAggregateBid strategy ^ 2 at h
  rw [aggregate_variance, expectedAggregateBid_eq] at h
  linarith

/-- The prize-aware equilibrium delivers expected edition welfare `37/18` at production cost `0`. -/
theorem bundledEditionWelfare_eq : model.bundledEditionWelfare strategy 0 = 37 / 18 := by
  unfold LinearScarcityAuction.bundledEditionWelfare
  rw [expectedAggregateBid_eq, expectedAggregateBidSq_eq]
  change (3 - 0 : ℝ) * (4 / 3) - 1 * (35 / 18) = 37 / 18
  norm_num

/-- The welfare number is the expectation of realized edition value, rather than only a formula
in supplied moments. The strategy also maximizes prize-aware utility, as proved above. -/
theorem expected_edition_welfare :
    𝔼[fun ω => model.aggregateBid strategy ω *
      model.spec.φ (model.aggregateBid strategy ω)] = 37 / 18 := by
  have h := model.bundledEditionWelfare_eq_integral strategy 0 aggregate_memLp
  rw [bundledEditionWelfare_eq] at h
  simpa only [zero_mul, sub_zero] using h.symm

/-- The editions-only Cournot benchmark buys `2/3` units in total. -/
theorem cournotQuantity_eq : model.cournotQuantityLinear = 2 / 3 := by
  change (2 : ℝ) * (3 - 2) / (1 * (2 + 1)) = 2 / 3
  norm_num

/-- A type's prize-aware purchase is at least the editions-only quantity `1/3` exactly when
its value is at least `1/3`; the prize does not raise every type's purchase. -/
theorem strategy_ge_cournot_iff (v : ℝ) :
    model.cournotPurchaseLinear ≤ strategy v ↔ (1 : ℝ) / 3 ≤ v := by
  change (3 - 2 : ℝ) / (1 * (2 + 1)) ≤ 1 / 6 + v / 2 ↔ (1 : ℝ) / 3 ≤ v
  constructor <;> intro h <;> linarith

/-- The gap between first-best edition welfare and the Cournot benchmark is `25/36`. -/
theorem cournot_gap :
    MathEconLib.AllPurchase.cournotLoss model.φ_bar 0 model.α_coeff
      model.cournotQuantityLinear = 25 / 36 := by
  rw [cournotQuantity_eq]
  change MathEconLib.AllPurchase.cournotLoss 3 0 1 (2 / 3) = 25 / 36
  norm_num [MathEconLib.AllPurchase.cournotLoss, MathEconLib.AllPurchase.firstBestEditionSurplus,
    MathEconLib.AllPurchase.editionWelfare]

/-- The negative contest gap records a gain of `1/2` in expected edition welfare. -/
theorem contest_gap :
    MathEconLib.AllPurchase.contestLoss model.φ_bar 0 model.α_coeff
      model.cournotQuantityLinear (model.bundledEditionWelfare strategy 0) = -(1 : ℝ) / 2 := by
  rw [cournotQuantity_eq, bundledEditionWelfare_eq]
  change MathEconLib.AllPurchase.contestLoss 3 0 1 (2 / 3) (37 / 18) = -(1 : ℝ) / 2
  norm_num [MathEconLib.AllPurchase.contestLoss, MathEconLib.AllPurchase.editionWelfare]

/-- Applying the auction-level welfare decomposition gives the total gap `7/36`, which splits
into Cournot gap `25/36` and contest gap `-1/2`. -/
theorem welfare_gap :
    MathEconLib.AllPurchase.firstBestEditionSurplus model.φ_bar 0 model.α_coeff -
      𝔼[fun ω => model.aggregateBid strategy ω *
        model.spec.φ (model.aggregateBid strategy ω)] = 7 / 36 := by
  have h := model.welfare_decomposition strategy 0 aggregate_memLp
  rw [cournot_gap, contest_gap] at h
  norm_num only [zero_mul, sub_zero] at h
  exact h

/-- Applying the auction-level variance theorem gives a welfare correction of `1/6` when
replacing random purchases by their mean. -/
theorem variance_penalty :
    MathEconLib.AllPurchase.editionWelfare model.φ_bar 0 model.α_coeff
        (model.expectedAggregateBid strategy) - model.bundledEditionWelfare strategy 0 = 1 / 6 := by
  have h := model.editionWelfare_mean_sub_bundled_eq_variance strategy 0 aggregate_memLp
  rw [aggregate_variance] at h
  change MathEconLib.AllPurchase.editionWelfare model.φ_bar 0 model.α_coeff
    (model.expectedAggregateBid strategy) - model.bundledEditionWelfare strategy 0 =
      1 * (1 / 6) at h
  simpa only [one_mul] using h

end MathEconLib.Examples.AllPurchase.UniformTwoBidder

end

end
