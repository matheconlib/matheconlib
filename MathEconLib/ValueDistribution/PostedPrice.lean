module

public import MathEconLib.SingleParameter.PostedPrice
public import MathEconLib.ValueDistribution.Demand
public import MathEconLib.ValueDistribution.SingleParameter

/-!
# Distributional Posted Pricing

This file combines the deterministic `postedPriceProblem` with a separately
supplied `ValueDistribution`. It derives expected allocation, expected payment,
and seller profit from the probability that the buyer's value reaches the
posted price.

The buyer purchases when `price ≤ value`, so demand includes any probability
mass exactly at the price. The results require neither bounded support nor a
density. Differentiability, virtual values, and price optimization belong to
later layers.
-/

namespace MathEconLib

@[expose] public section

open MeasureTheory Set
open SingleParameterProblem

namespace ValueDistribution

/-- Expected allocation at a posted price is the probability that the buyer's
value is at least the price. -/
theorem expectedAllocation_postedPriceProblem
    (D : ValueDistribution) (lowestType highestType price : ℝ) :
    D.expectedAllocation
        (postedPriceProblem lowestType highestType price) =
      D.probAtLeast price := by
  rw [expectedAllocation]
  simp_rw [postedPriceProblem_q]
  have hintegrand :
      (fun value : ℝ => if price ≤ value then (1 : ℝ) else 0) =
        (Ici price).indicator (1 : ℝ → ℝ) := by
    funext value
    simp [Set.indicator]
  rw [hintegrand, integral_indicator_one measurableSet_Ici, probAtLeast,
    ← D.measureReal_eq_coe_coeFn]

/-- Expected payment at a posted price is the price multiplied by the
probability of purchase. -/
theorem expectedPayment_postedPriceProblem
    (D : ValueDistribution) (lowestType highestType price : ℝ) :
    D.expectedPayment
        (postedPriceProblem lowestType highestType price) =
      price * D.probAtLeast price := by
  rw [expectedPayment]
  have hintegrand :
      (fun value : ℝ =>
        (postedPriceProblem lowestType highestType price).payment
          ((postedPriceProblem lowestType highestType price).strategy value)) =
      (fun value : ℝ =>
        price * (postedPriceProblem lowestType highestType price).q value) := by
    funext value
    by_cases hprice : price ≤ value
    all_goals
      simp [postedPriceProblem, PurchaseDecision.allocation,
        PurchaseDecision.payment, q, hprice]
  rw [hintegrand, integral_const_mul]
  change price * D.expectedAllocation
      (postedPriceProblem lowestType highestType price) =
    price * D.probAtLeast price
  rw [D.expectedAllocation_postedPriceProblem]

/-- Seller profit at a posted price is the continuation value minus the
acquisition cost, plus the margin over continuation value multiplied by the
probability of purchase. -/
theorem sellerProfit_postedPriceProblem
    (D : ValueDistribution) (lowestType highestType price : ℝ)
    (continuationValue acquisitionCost : ℝ) :
    D.sellerProfit
        (postedPriceProblem lowestType highestType price)
        continuationValue acquisitionCost =
      continuationValue - acquisitionCost +
        (price - continuationValue) * D.probAtLeast price := by
  rw [sellerProfit, D.expectedPayment_postedPriceProblem,
    D.expectedAllocation_postedPriceProblem]
  ring

/-- With zero continuation value and zero acquisition cost, posted-price
seller profit is the familiar price-times-demand revenue formula. -/
theorem sellerProfit_postedPriceProblem_zero
    (D : ValueDistribution) (lowestType highestType price : ℝ) :
    D.sellerProfit
        (postedPriceProblem lowestType highestType price) 0 0 =
      price * D.probAtLeast price := by
  simpa using
    (D.sellerProfit_postedPriceProblem lowestType highestType price 0 0)

/-- The unconditional acquisition cost cancels when comparing two posted
prices. Thus the profit difference depends only on the two margins over the
continuation value and their associated demands. -/
theorem sellerProfit_postedPriceProblem_sub
    (D : ValueDistribution) (lowestType highestType price₁ price₂ : ℝ)
    (continuationValue acquisitionCost : ℝ) :
    D.sellerProfit
          (postedPriceProblem lowestType highestType price₁)
          continuationValue acquisitionCost -
        D.sellerProfit
          (postedPriceProblem lowestType highestType price₂)
          continuationValue acquisitionCost =
      (price₁ - continuationValue) * D.probAtLeast price₁ -
        (price₂ - continuationValue) * D.probAtLeast price₂ := by
  rw [D.sellerProfit_postedPriceProblem,
    D.sellerProfit_postedPriceProblem]
  ring

end ValueDistribution

end

end MathEconLib
