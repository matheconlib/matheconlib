module

public import Auctionlib.ValueDistribution.PostedPriceOptimality

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# First-Order Conditions for Posted Prices

This file differentiates posted-price seller profit and prepares the
first-order condition for an interior locally optimal price.

The CDF derivative is assumed only at the candidate price. The resulting
derivative is expressed using division-free net virtual surplus, so it remains
meaningful when the derivative vanishes. No global density representative,
bounded-support assumption, or absolute-continuity assumption is required.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open SingleParameterProblem

namespace ValueDistribution

/-- The derivative of posted-price seller profit is the negative of net
virtual surplus at the candidate price.

Here `density price` is the pointwise derivative of the CDF at `price`. The
function `density` need not be a global Radon--Nikodym density representative.
Atomlessness identifies the closed-tail posted-price demand with one minus the
CDF throughout a neighborhood of the candidate price.
The unconditional acquisition cost is constant in price and therefore does
not enter the derivative. -/
theorem hasDerivAt_sellerProfit_postedPriceProblem
    (D : ValueDistribution) [NoAtoms (D : Measure ℝ)]
    (lowestType highestType : ℝ) (density : ℝ → ℝ)
    (continuationValue acquisitionCost price : ℝ)
    (hcdf : HasDerivAt (cdf (D : Measure ℝ)) (density price) price) :
    HasDerivAt
      (fun candidatePrice ↦
        D.sellerProfit
          (postedPriceProblem lowestType highestType candidatePrice)
          continuationValue acquisitionCost)
      (-(D.virtualSurplusWeight density price -
          continuationValue * density price))
      price := by
  convert
    (((hasDerivAt_id price).sub_const continuationValue).mul
      ((hasDerivAt_const price 1).sub hcdf)).const_add
        (continuationValue - acquisitionCost) using 1
  · funext candidatePrice
    rw [D.sellerProfit_postedPriceProblem,
      D.probAtLeast_eq_one_sub_cdf]
    rfl
  · rw [virtualSurplusWeight, D.probAtLeast_eq_one_sub_cdf]
    simp only [Pi.sub_apply, id_eq]
    ring

/-- An interior locally optimal posted price has zero net virtual-surplus
weight.

This is a necessary condition. It does not assert that a price satisfying the
condition is globally or locally optimal. -/
theorem netVirtualSurplus_eq_zero_of_isLocalMaxOn_sellerProfit_postedPriceProblem
    (D : ValueDistribution) [NoAtoms (D : Measure ℝ)]
    (lowestType highestType : ℝ) (density : ℝ → ℝ)
    (continuationValue acquisitionCost price : ℝ)
    (hprice : price ∈ Ioo lowestType highestType)
    (hcdf : HasDerivAt (cdf (D : Measure ℝ)) (density price) price)
    (hmax :
      IsLocalMaxOn
        (fun candidatePrice ↦
          D.sellerProfit
            (postedPriceProblem lowestType highestType candidatePrice)
            continuationValue acquisitionCost)
        (Icc lowestType highestType) price) :
    D.virtualSurplusWeight density price -
      continuationValue * density price = 0 := by
  have hlocalMax :
      IsLocalMax
        (fun candidatePrice ↦
          D.sellerProfit
            (postedPriceProblem lowestType highestType candidatePrice)
            continuationValue acquisitionCost)
        price :=
    hmax.isLocalMax (Icc_mem_nhds hprice.1 hprice.2)
  have hderivativeZero :
      -(D.virtualSurplusWeight density price -
          continuationValue * density price) = 0 :=
    hlocalMax.hasDerivAt_eq_zero
      (D.hasDerivAt_sellerProfit_postedPriceProblem
        lowestType highestType density continuationValue acquisitionCost price
        hcdf)
  exact neg_eq_zero.mp hderivativeZero

/-- At an interior locally optimal posted price with nonzero density, virtual
value equals the seller's continuation value. -/
theorem virtualValue_eq_continuationValue_of_isLocalMaxOn_sellerProfit_postedPriceProblem
    (D : ValueDistribution) [NoAtoms (D : Measure ℝ)]
    (lowestType highestType : ℝ) (density : ℝ → ℝ)
    (continuationValue acquisitionCost price : ℝ)
    (hprice : price ∈ Ioo lowestType highestType)
    (hcdf : HasDerivAt (cdf (D : Measure ℝ)) (density price) price)
    (hmax :
      IsLocalMaxOn
        (fun candidatePrice ↦
          D.sellerProfit
            (postedPriceProblem lowestType highestType candidatePrice)
            continuationValue acquisitionCost)
        (Icc lowestType highestType) price)
    (hdensity : density price ≠ 0) :
    D.virtualValue density price = continuationValue := by
  have hnet :=
    D.netVirtualSurplus_eq_zero_of_isLocalMaxOn_sellerProfit_postedPriceProblem
      lowestType highestType density continuationValue acquisitionCost price
      hprice hcdf hmax
  apply mul_left_cancel₀ hdensity
  rw [← D.virtualSurplusWeight_eq_density_mul_virtualValue
    density price hdensity, sub_eq_zero.mp hnet]
  exact mul_comm continuationValue (density price)

/-- With zero continuation value, an interior locally optimal posted price
has virtual value zero whenever the density there is nonzero. -/
theorem virtualValue_eq_zero_of_isLocalMaxOn_sellerProfit_postedPriceProblem
    (D : ValueDistribution) [NoAtoms (D : Measure ℝ)]
    (lowestType highestType : ℝ) (density : ℝ → ℝ)
    (acquisitionCost price : ℝ)
    (hprice : price ∈ Ioo lowestType highestType)
    (hcdf : HasDerivAt (cdf (D : Measure ℝ)) (density price) price)
    (hmax :
      IsLocalMaxOn
        (fun candidatePrice ↦
          D.sellerProfit
            (postedPriceProblem lowestType highestType candidatePrice)
            0 acquisitionCost)
        (Icc lowestType highestType) price)
    (hdensity : density price ≠ 0) :
    D.virtualValue density price = 0 := by
  simpa using
    (D.virtualValue_eq_continuationValue_of_isLocalMaxOn_sellerProfit_postedPriceProblem
      lowestType highestType density 0 acquisitionCost price hprice hcdf hmax
      hdensity)

end ValueDistribution

end
