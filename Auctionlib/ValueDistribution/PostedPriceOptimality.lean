module

public import Auctionlib.ValueDistribution.PostedPrice
public import Auctionlib.ValueDistribution.SellerProfit

/-!
# Posted-Price Seller Profit as a Cutoff Integral

This file rewrites seller profit at a posted price as a cutoff integral of
net virtual surplus. The representation is the analytic bridge used by later
posted-price optimization results.

## Scope

For a buyer with value in `[lowestType, highestType]`, posting `price` induces
the cutoff allocation that sells exactly when `price ≤ value`. The general
seller-profit representation from `SellerProfit.lean` therefore collapses to
an integral over `[price, highestType]`.

The net virtual-surplus weight `w(v) - r * f(v)` is division-free, so it is
meaningful even where the density vanishes. It corresponds to Riley and
Zeckhauser's `k(v) = (j(v) - π(v))f(v)` when the continuation value `r` is
constant.

This file proves a representation, not an optimality theorem. It does not
compare prices, differentiate the profit function, or establish optimality
against arbitrary selling rules.

## Assumptions

The price lies in the type interval, the distribution is supported on that
interval and absolutely continuous with respect to Lebesgue measure, and the
chosen density agrees almost everywhere there with
`ValueDistribution.realDensity`. A chosen density is a representative, not a
canonical pointwise continuous density.

Integrability is derived from existing envelope-IC, support, and
absolute-continuity results rather than assumed, so no integrability side
conditions appear in the public statement.
-/

@[expose] public section

open MeasureTheory Set
open SingleParameterProblem

namespace ValueDistribution

/-! ## Collapsing the cutoff allocation

The induced allocation of a posted price is the cutoff indicator supplied by
`postedPriceProblem_q`. Weighting any function by it and integrating over the
type interval therefore only keeps the part of the interval at or above the
price.

At the tie `value = price` the buyer purchases, so the integrand on the lower
piece is not pointwise zero; it vanishes only away from that single point.
Since a singleton is Lebesgue-null, the lower piece still contributes nothing,
and the argument below is almost-everywhere rather than pointwise. -/

private theorem intervalIntegral_q_postedPriceProblem_mul
    (lowestType highestType price : ℝ) (h : ℝ → ℝ)
    (hprice : price ∈ Icc lowestType highestType)
    (hqh :
      IntervalIntegrable
        (fun value =>
          (postedPriceProblem lowestType highestType price).q value * h value)
        volume lowestType highestType) :
    (∫ value in lowestType..highestType,
        (postedPriceProblem lowestType highestType price).q value * h value) =
      ∫ value in price..highestType, h value := by
  have hpricemem : price ∈ uIcc lowestType highestType := by
    rw [uIcc_of_le (hprice.1.trans hprice.2)]
    exact hprice
  have hlowerint :
      IntervalIntegrable
        (fun value =>
          (postedPriceProblem lowestType highestType price).q value * h value)
        volume lowestType price :=
    hqh.mono_set (uIcc_subset_uIcc left_mem_uIcc hpricemem)
  have hupperint :
      IntervalIntegrable
        (fun value =>
          (postedPriceProblem lowestType highestType price).q value * h value)
        volume price highestType :=
    hqh.mono_set (uIcc_subset_uIcc hpricemem right_mem_uIcc)
  have hnull : ∀ᵐ value ∂(volume : Measure ℝ), value ≠ price := by
    rw [ae_iff]
    simp
  have hlower :
      (∫ value in lowestType..price,
        (postedPriceProblem lowestType highestType price).q value * h value) = 0 := by
    have hzero :
        (∫ value in lowestType..price,
            (postedPriceProblem lowestType highestType price).q value * h value) =
          ∫ _ in lowestType..price, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hnull] with value hne hmem
      rw [uIoc_of_le hprice.1] at hmem
      rw [postedPriceProblem_q, if_neg (not_le.mpr (lt_of_le_of_ne hmem.2 hne))]
      ring
    simpa using hzero
  have hupper :
      (∫ value in price..highestType,
          (postedPriceProblem lowestType highestType price).q value * h value) =
        ∫ value in price..highestType, h value := by
    apply intervalIntegral.integral_congr
    intro value hvalue
    rw [uIcc_of_le hprice.2] at hvalue
    dsimp only
    rw [postedPriceProblem_q, if_pos hvalue.1]
    ring
  rw [← intervalIntegral.integral_add_adjacent_intervals hlowerint hupperint,
    hlower, hupper, zero_add]

/-- Interval integrability of the allocation-weighted net virtual surplus.

This is derived from the public envelope-IC integrability results rather than
assumed, so the theorems below need no integrability side conditions. -/
private theorem intervalIntegrable_q_mul_netVirtualSurplus
    (D : ValueDistribution) (lowestType highestType price : ℝ)
    (density : ℝ → ℝ) (continuationValue : ℝ)
    (horder : lowestType ≤ highestType)
    (hsupport : D.IsSupportedOnInterval lowestType highestType)
    (hD : (D : Measure ℝ) ≪ volume)
    (hdensity :
      density =ᵐ[volume.restrict (Icc lowestType highestType)] D.realDensity) :
    IntervalIntegrable
      (fun value =>
        (postedPriceProblem lowestType highestType price).q value *
          (D.virtualSurplusWeight density value -
            continuationValue * density value))
      volume lowestType highestType := by
  have hweight :=
    D.intervalIntegrable_q_mul_virtualSurplusWeight_realDensity
      (postedPriceProblem lowestType highestType price) horder hsupport hD
  have hdens :=
    D.intervalIntegrable_q_mul_realDensity
      (postedPriceProblem lowestType highestType price) horder hD
  have hcombined :
      IntervalIntegrable
        (fun value =>
          (postedPriceProblem lowestType highestType price).q value *
              D.virtualSurplusWeight D.realDensity value -
            continuationValue *
              ((postedPriceProblem lowestType highestType price).q value *
                D.realDensity value))
        volume lowestType highestType :=
    hweight.sub (hdens.const_mul continuationValue)
  have hcanonical :
      IntervalIntegrable
        (fun value =>
          (postedPriceProblem lowestType highestType price).q value *
            (D.virtualSurplusWeight D.realDensity value -
              continuationValue * D.realDensity value))
        volume lowestType highestType := by
    apply IntervalIntegrable.congr _ hcombined
    intro value _
    dsimp only
    ring
  have hae :
      density =ᵐ[volume.restrict (uIoc lowestType highestType)] D.realDensity := by
    apply ae_restrict_of_ae_restrict_of_subset uIoc_subset_uIcc
    simpa only [uIcc_of_le horder] using hdensity
  apply hcanonical.congr_ae
  filter_upwards [hae] with value hvalue
  simp only [virtualSurplusWeight, hvalue]

/-! ## Cutoff-integral representation of seller profit -/

/-- **Posted-price seller profit as a cutoff integral of net virtual surplus.**

For a price in the type interval, expected seller profit is the continuation
value, less the unconditional acquisition cost, plus the integral of net
virtual surplus over the values at or above the price.

The integrand `virtualSurplusWeight density value - continuationValue *
density value` is division-free, so the identity remains meaningful wherever
the density vanishes.

This is a representation, not an optimality claim: it says what profit *is*
at a given price, and asserts nothing about which price is best. -/
theorem sellerProfit_postedPriceProblem_eq_intervalIntegral_netVirtualSurplus
    (D : ValueDistribution) (lowestType highestType price : ℝ)
    (density : ℝ → ℝ) (continuationValue acquisitionCost : ℝ)
    (hprice : price ∈ Icc lowestType highestType)
    (hsupport : D.IsSupportedOnInterval lowestType highestType)
    (hD : (D : Measure ℝ) ≪ volume)
    (hdensity :
      density =ᵐ[volume.restrict (Icc lowestType highestType)] D.realDensity) :
    D.sellerProfit (postedPriceProblem lowestType highestType price)
        continuationValue acquisitionCost =
      continuationValue - acquisitionCost +
        ∫ value in price..highestType,
          (D.virtualSurplusWeight density value -
            continuationValue * density value) := by
  have horder : lowestType ≤ highestType :=
    hprice.1.trans hprice.2
  have hlowestTypeUtility :
      (postedPriceProblem lowestType highestType price).U
        (postedPriceProblem lowestType highestType price).lowestType = 0 :=
    postedPriceProblem_hasZeroLowestTypeUtility lowestType highestType price
      hprice.1
  have hcollapse :
      (∫ value in lowestType..highestType,
          (postedPriceProblem lowestType highestType price).q value *
            (D.virtualSurplusWeight density value -
              continuationValue * density value)) =
        ∫ value in price..highestType,
          (D.virtualSurplusWeight density value -
            continuationValue * density value) :=
    intervalIntegral_q_postedPriceProblem_mul lowestType highestType price _
      hprice
      (intervalIntegrable_q_mul_netVirtualSurplus D lowestType highestType price
        density continuationValue horder hsupport hD hdensity)
  rw [D.sellerProfit_eq_virtualSurplus
      (postedPriceProblem lowestType highestType price) density
      continuationValue acquisitionCost horder hsupport hD hdensity,
    hlowestTypeUtility,
    show (postedPriceProblem lowestType highestType price).lowestType =
      lowestType from rfl,
    show (postedPriceProblem lowestType highestType price).highestType =
      highestType from rfl,
    hcollapse]
  ring

end ValueDistribution

end
