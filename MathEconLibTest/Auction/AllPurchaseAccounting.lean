/-
Copyright (c) 2026 yoshiki-pramaana, Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: yoshiki-pramaana, Bo Cowgill
-/
module

public import MathEconLib.Auction.AllPurchase.RevenueDecomposition
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# All-purchase accounting regressions

These examples adapt the counterexamples submitted by @yoshiki-pramaana in issue #239.
The scalar bidder model retains the net-cost formula used by the bidding proofs. Its induced
monetary mechanism records purchases, charges the seller's posted price, and values resale in the
outcome environment. The examples distinguish actual receipts from bidder net cost, check price
identification, and retain the action-domain and arbitrage qualifications.
-/

@[expose] public section

open MathEconLib MathEconLib.Mechanism MathEconLib.Mechanism.Auctions
open MeasureTheory ProbabilityTheory

namespace MathEconLib.Tests.AllPurchaseAccounting

noncomputable section

/-- One bidder's auxiliary net-cost model, with price one and resale value `3 - B`. -/
def bidderRules : MathEconLib.Mechanism (Fin 1) (fun _ ↦ ℝ) (Fin 1 → ℝ) where
  outcome _ _ := 1
  transfer i b := -((1 - (3 - ∑ j, b j)) * b i)

/-- Simultaneously shifted prices and scarcity values have the same auxiliary net costs. -/
def model (k : ℝ) (hk : 0 ≤ k) : AllPurchaseBidderSpec bidderRules where
  price := 1 + k
  price_pos := by linarith
  φ B := 3 + k - B
  φ_continuous := by fun_prop
  φ_strictAnti := fun _ _ h ↦ by dsimp; linarith
  usesStrictHighestBidAllocation i := by
    funext b
    fin_cases i
    simp [bidderRules, Set.indicator]
  transfer_eq _ _ := by dsimp [bidderRules]; ring

/-- At one purchase the bidder gains two and the seller receives one; net cost is minus one. -/
theorem finite_accounting :
    (model 0 (by norm_num)).toMechanism.revenue (fun _ ↦ 1) = 1 ∧
      (model 0 (by norm_num)).toSpec.environment.utility
        (model 0 (by norm_num)).toMechanism 0 (fun _ ↦ 1) (fun _ ↦ 1) = 2 ∧
      (model 0 (by norm_num)).toSpec.netCost 0 (fun _ ↦ 1) = -1 := by
  norm_num [AllPurchaseSpec.environment, AllPurchaseSpec.resaleValue,
    AllPurchaseSpec.netCost, QuasilinearEnvironment.utility,
    QuasilinearEnvironment.ofPrivate, AllPurchaseBidderSpec.toSpec,
    AllPurchaseBidderSpec.toMechanism, bidderRules, model, Mechanism.revenue]

/-- The scalar model's negative revenue is net cost, not the artist's receipts. -/
theorem scalar_revenue_is_not_seller_revenue :
    bidderRules.revenue (fun _ ↦ 1) = -1 ∧
      (model 0 (by norm_num)).toMechanism.revenue (fun _ ↦ 1) = 1 := by
  norm_num [Mechanism.revenue, bidderRules, AllPurchaseBidderSpec.toMechanism, model]

/-- Purchases remain available to the valuation environment at the chosen outcome. -/
theorem purchases_recorded (b : Fin 1 → ℝ) :
    ((model 0 (by norm_num)).toMechanism.outcome b).purchases = b := rfl

/-- The two purported prices now produce different monetary mechanisms. -/
theorem shifted_prices_change_mechanism :
    (model 0 (by norm_num)).toMechanism ≠ (model 10 (by norm_num)).toMechanism := by
  intro h
  have ht := congrArg (fun M ↦ M.transfer 0 (fun _ ↦ 1)) h
  norm_num [AllPurchaseBidderSpec.toMechanism, model] at ht

/-- Any specification of the actual mechanism has the posted price one. -/
theorem posted_price_identified
    (spec : AllPurchaseSpec (model 0 (by norm_num)).toMechanism
      AllPurchaseBidderSpec.Outcome.prize AllPurchaseBidderSpec.Outcome.purchases) :
    spec.price = 1 := by
  have h := spec.price_unique (model 0 (by norm_num)).toSpec
  simpa [AllPurchaseBidderSpec.toSpec, model] using h

/-- Real actions allow negative purchases and hence negative receipts even after repair. -/
theorem negative_purchase_receipts :
    (model 0 (by norm_num)).toMechanism.revenue (fun _ ↦ -1) = -1 := by
  rw [(model 0 (by norm_num)).toSpec.revenue_eq]
  norm_num [AllPurchaseBidderSpec.toSpec, model]

/-- Global no-deficit must not be asserted for unrestricted real purchases. -/
theorem real_actions_not_noDeficit :
    ¬ (model 0 (by norm_num)).toMechanism.IsNoDeficit :=
  (model 0 (by norm_num)).toSpec.not_isNoDeficit

/-- On nonnegative actions the actual monetary mechanism has no deficit. -/
theorem nonnegative_actions_noDeficit :
    ((model 0 (by norm_num)).toMechanism.comap
      (fun _ (b : Set.Ici (0 : ℝ)) ↦ b.val)).IsNoDeficit :=
  (model 0 (by norm_num)).toSpec.isNoDeficit_nonnegative

local instance : MeasureSpace Unit := ⟨Measure.dirac ()⟩
local instance : IsProbabilityMeasure (volume : Measure Unit) := by
  change IsProbabilityMeasure (Measure.dirac ())
  infer_instance

/-- Deterministic type one permits a direct same-strategy expected-receipts regression. -/
def bidderAuction : Auction Unit 1 where
  rules := bidderRules
  outcome_measurable _ := measurable_const
  θmin _ := 1
  θmax _ := 1
  θ _ _ := 1
  θ_measurable _ := measurable_const

/-- Doubling purchases doubles actual expected receipts; truthful play would give only one. -/
theorem expected_receipts_same_strategy :
    bidderAuction.sellerGrossRevenue (model 0 (by norm_num)) (fun v ↦ 2 * v) = 2 ∧
      (𝔼[fun ω ↦ ((model 0 (by norm_num)).toMechanism.comap
        (fun _ (v : ℝ) ↦ 2 * v)).revenue (bidderAuction.θ · ω)]) = 2 := by
  have h : bidderAuction.sellerGrossRevenue (model 0 (by norm_num)) (fun v ↦ 2 * v) = 2 := by
    norm_num [Auction.sellerGrossRevenue, Auction.expectedAggregateBid, Auction.aggregateBid,
      bidderAuction, model]
  exact ⟨h, (bidderAuction.sellerGrossRevenue_eq_integral_revenue_comap
    (model 0 (by norm_num)) (fun v ↦ 2 * v)).symm.trans h⟩

/-- The exponential scarcity example's auxiliary net-cost model. -/
def arbitrageRules : MathEconLib.Mechanism (Fin 1) (fun _ ↦ ℝ) (Fin 1 → ℝ) where
  outcome _ _ := 1
  transfer i b := -((1 - (2 + Real.exp (-∑ j, b j))) * b i)

/-- Accounting repair does not prohibit per-edition resale value above the price. -/
def arbitrageModel : AllPurchaseBidderSpec arbitrageRules where
  price := 1
  price_pos := by norm_num
  φ B := 2 + Real.exp (-B)
  φ_continuous := by fun_prop
  φ_strictAnti := fun _ _ h ↦ by dsimp; gcongr
  usesStrictHighestBidAllocation i := by
    funext b
    fin_cases i
    simp [arbitrageRules, Set.indicator]
  transfer_eq _ _ := rfl

/-- Every nonnegative purchase gives utility at least prize value plus quantity purchased. -/
theorem arbitrage_utility_lower_bound (θ : Fin 1 → ℝ) (x : ℝ) (hx : 0 ≤ x) :
    θ 0 + x ≤ arbitrageModel.toSpec.environment.utility arbitrageModel.toMechanism
      0 θ (fun _ ↦ x) := by
  change θ 0 + x ≤ θ 0 * 1 + (2 + Real.exp (-(∑ _j : Fin 1, x))) * x + -(1 * x)
  simp only [Finset.univ_unique, Finset.sum_singleton, mul_one, one_mul]
  nlinarith [Real.exp_pos (-x)]

/-- No purchase level is a best response on the unchanged real action domain. -/
theorem arbitrage_no_best_bid (θ r : Fin 1 → ℝ) :
    ∃ r', arbitrageModel.toSpec.environment.utility arbitrageModel.toMechanism 0 θ r <
      arbitrageModel.toSpec.environment.utility arbitrageModel.toMechanism 0 θ r' := by
  let u := arbitrageModel.toSpec.environment.utility arbitrageModel.toMechanism 0 θ r
  let x := max 0 (u - θ 0 + 1)
  refine ⟨fun _ ↦ x, ?_⟩
  have h := arbitrage_utility_lower_bound θ x (le_max_left _ _)
  have hx : u - θ 0 + 1 ≤ x := le_max_right _ _
  linarith

/-- The same arbitrage survives restriction to nonnegative purchases. -/
theorem arbitrage_no_best_nonnegative (θ : Fin 1 → ℝ)
    (r : Fin 1 → Set.Ici (0 : ℝ)) :
    ∃ r' : Fin 1 → Set.Ici (0 : ℝ),
      arbitrageModel.toSpec.environment.utility
          (arbitrageModel.toMechanism.comap (fun _ (b : Set.Ici (0 : ℝ)) ↦ b.val)) 0 θ r <
        arbitrageModel.toSpec.environment.utility
          (arbitrageModel.toMechanism.comap (fun _ (b : Set.Ici (0 : ℝ)) ↦ b.val)) 0 θ r' := by
  let u := arbitrageModel.toSpec.environment.utility arbitrageModel.toMechanism
    0 θ (fun i ↦ (r i).val)
  let x := max 0 (u - θ 0 + 1)
  refine ⟨fun _ ↦ ⟨x, le_max_left _ _⟩, ?_⟩
  change u < arbitrageModel.toSpec.environment.utility arbitrageModel.toMechanism 0 θ (fun _ ↦ x)
  have h := arbitrage_utility_lower_bound θ x (le_max_left _ _)
  have hx : u - θ 0 + 1 ≤ x := le_max_right _ _
  linarith

/-- The public bidder adapter packages the raw scalar auction without coercing to it. -/
def revenueModel : AllPurchaseBidderModel Unit 1 where
  toNetCostAuction := bidderAuction
  spec := model 0 (by norm_num)

/-- The same adapter boundary applies to the linear-scarcity specialization. -/
def linearRevenueModel : LinearScarcityAuction Unit 1 where
  toAllPurchaseBidderModel := revenueModel
  φ_bar := 3
  α_coeff := 1
  α_pos := by norm_num
  φ_bar_pos := by norm_num
  scarcity_is_linear := by
    funext B
    simp [revenueModel, model]

/-- Actual receipts and bidder net costs have separate names and different values. -/
theorem revenue_api_distinguishes_net_cost :
    revenueModel.expectedSellerRevenue id = 1 ∧ revenueModel.expectedNetCost id = -1 := by
  norm_num [AllPurchaseBidderModel.expectedSellerRevenue, AllPurchaseBidderModel.sellerRevenue,
    AllPurchaseBidderModel.toMechanism, AllPurchaseBidderModel.expectedNetCost,
    AllPurchaseSpec.netCost, AllPurchaseBidderSpec.toSpec, AllPurchaseBidderSpec.toMechanism,
    revenueModel, bidderAuction, bidderRules, model, Mechanism.revenue]
  dsimp only [revenueModel, model]
  norm_num

/-- Both APIs evaluate the explicitly supplied strategy rather than silently using truthful play. -/
theorem revenue_api_uses_supplied_strategy :
    revenueModel.expectedSellerRevenue (fun v ↦ 2 * v) = 2 ∧
      revenueModel.expectedNetCost (fun v ↦ 2 * v) = 0 := by
  norm_num [AllPurchaseBidderModel.expectedSellerRevenue, AllPurchaseBidderModel.sellerRevenue,
    AllPurchaseBidderModel.toMechanism, AllPurchaseBidderModel.expectedNetCost,
    AllPurchaseSpec.netCost, AllPurchaseBidderSpec.toSpec, AllPurchaseBidderSpec.toMechanism,
    revenueModel, bidderAuction, bidderRules, model, Mechanism.revenue]
  dsimp only [revenueModel, model]
  norm_num

/-- The linear model exposes the same safe seller and net-cost methods through its parent. -/
theorem linear_revenue_api_distinguishes_net_cost :
    linearRevenueModel.expectedSellerRevenue id = 1 ∧
      linearRevenueModel.expectedNetCost id = -1 := revenue_api_distinguishes_net_cost

/-- The old scalar revenue is available by deliberate projection and is explicitly net cost. -/
theorem raw_revenue_is_net_cost :
    revenueModel.toNetCostAuction.expectedRevenue = revenueModel.expectedNetCost id :=
  revenueModel.expectedNetCost_id_eq_auxiliary_expectedRevenue.symm

-- Positive controls keep generic Auction.expectedRevenue available. The failing calls check
-- the adapter's type boundary, rather than relying on a warning or a shadowed method name.
example : True := by
  have _ : ℝ := revenueModel.expectedSellerRevenue id
  have _ : ℝ := revenueModel.expectedNetCost id
  have _ : ℝ := revenueModel.toNetCostAuction.expectedRevenue
  fail_if_success have _ : ℝ := revenueModel.expectedSellerRevenue
  fail_if_success have _ := revenueModel.expectedRevenue
  fail_if_success have _ : ℝ := Auction.expectedRevenue revenueModel
  fail_if_success have _ : Auction Unit 1 := revenueModel
  trivial

example : True := by
  have _ : ℝ := linearRevenueModel.expectedSellerRevenue id
  have _ : ℝ := linearRevenueModel.expectedNetCost id
  have _ : ℝ := linearRevenueModel.toNetCostAuction.expectedRevenue
  fail_if_success have _ : ℝ := linearRevenueModel.expectedSellerRevenue
  fail_if_success have _ := linearRevenueModel.expectedRevenue
  fail_if_success have _ : ℝ := Auction.expectedRevenue linearRevenueModel
  fail_if_success have _ := linearRevenueModel.toAuction
  fail_if_success have _ : Auction Unit 1 := linearRevenueModel
  trivial

end

end MathEconLib.Tests.AllPurchaseAccounting
