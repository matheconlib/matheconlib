module

import Auctionlib.ValueDistribution.PostedPrice
import Mathlib.MeasureTheory.Measure.DiracProba

/-!
# Compatibility Checks for Distributional Pricing

This file checks that value distributions, deterministic posted prices, and
the generic seller objective compose with the intended economic semantics.
The examples are test-only and do not extend the production API.
-/

noncomputable section

open MeasureTheory ProbabilityTheory SingleParameterProblem

namespace PricingCompatibility

variable (lowestType highestType price : ℝ)

/-! ## Certain sale -/

/-- If the buyer's value is certainly equal to the posted price, the weak
purchase inequality produces a sale with probability one. Seller profit is
therefore the price received minus the unconditional acquisition cost; the
continuation value cancels because the object is never retained. -/
example (continuationValue acquisitionCost : ℝ) :
    ValueDistribution.sellerProfit (diracProba price)
        (postedPriceProblem lowestType highestType price)
        continuationValue acquisitionCost =
      price - acquisitionCost := by
  rw [ValueDistribution.sellerProfit_postedPriceProblem]
  unfold ValueDistribution.probAtLeast
  simp [ProbabilityMeasure.coeFn_def]

/-! ## Certain non-sale -/

/-- If the buyer's value is certainly strictly below the posted price, no
sale occurs. The seller retains the continuation value and pays the
unconditional acquisition cost. -/
example (value continuationValue acquisitionCost : ℝ)
    (hvalue : value < price) :
    ValueDistribution.sellerProfit (diracProba value)
        (postedPriceProblem lowestType highestType price)
        continuationValue acquisitionCost =
      continuationValue - acquisitionCost := by
  rw [ValueDistribution.sellerProfit_postedPriceProblem]
  unfold ValueDistribution.probAtLeast
  simp [ProbabilityMeasure.coeFn_def, not_le_of_gt hvalue]

/-! ## Price comparisons -/

/-- A common unconditional acquisition cost does not affect the ordering of
two posted prices. -/
example (D : ValueDistribution)
    (price₂ continuationValue acquisitionCost : ℝ) :
    D.sellerProfit
          (postedPriceProblem lowestType highestType price)
          continuationValue acquisitionCost ≤
        D.sellerProfit
          (postedPriceProblem lowestType highestType price₂)
          continuationValue acquisitionCost ↔
      D.sellerProfit
          (postedPriceProblem lowestType highestType price)
          continuationValue 0 ≤
        D.sellerProfit
          (postedPriceProblem lowestType highestType price₂)
          continuationValue 0 := by
  simp [ValueDistribution.sellerProfit_postedPriceProblem]

/-! ## Reduced-form compatibility -/

/-- Reducing the deterministic posted-price problem preserves its
distributional seller-profit formula. -/
example (D : ValueDistribution)
    (continuationValue acquisitionCost : ℝ) :
    D.sellerProfit
        (postedPriceProblem lowestType highestType price).reduce
        continuationValue acquisitionCost =
      continuationValue - acquisitionCost +
        (price - continuationValue) * D.probAtLeast price := by
  rw [D.sellerProfit_reduce]
  exact D.sellerProfit_postedPriceProblem lowestType highestType price
    continuationValue acquisitionCost

end PricingCompatibility

end
