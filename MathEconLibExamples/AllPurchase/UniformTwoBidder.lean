module

public import MathEconLib.Auction.AllPurchase
public import MathEconLib.BidderProblem
public import MathEconLibExamples.AllPurchase.Basic
public import MathEconLibExamples.AllPurchase.UniformProbability

/-!
# An interior equilibrium with two uniform bidders

Two bidders have independent uniform values on `[0, 2]`. The posted edition price is two,
scarcity value at total purchases `B` is `3 - B`, and the unique highest purchaser receives the
prize. The strategy `β(v) = 1/6 + v/2` is optimal against every real-valued unilateral bid, not
only bids in the strategy's range. Its expected purchase is `2/3`, marginal net cost at zero is
`-1/3`, and lowest-type utility is `1/36`.

The final results apply the auction-level interior quantity and seller-profit theorems to this
fully specified model. Expected total purchases are `4/3`, and profit at zero production cost is
`8/3`; the posted price realizes the algebraic interior optimum. This application does not assert
an optimum over other equilibrium regimes.
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

/-- Each bidder buys a positive baseline quantity plus half their value. -/
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

/-- The expected payment from any real bid is `b² - b/3`. -/
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

/-- Applying the auction-to-profit bridge gives profit `8/3` at zero production cost. -/
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

end MathEconLib.Examples.AllPurchase.UniformTwoBidder

end

end
