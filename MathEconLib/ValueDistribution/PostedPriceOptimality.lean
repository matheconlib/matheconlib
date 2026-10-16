/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.ValueDistribution.PostedPrice
public import MathEconLib.ValueDistribution.SellerProfit

/-!
# Optimal Posted Prices from Virtual-Surplus Sign Conditions

This file rewrites posted-price seller profit as a cutoff integral of net
virtual surplus and derives global optimality among posted prices from a
single-crossing sign condition.

## Main results

* `sellerProfit_postedPriceProblem_eq_intervalIntegral_netVirtualSurplus`
  collapses the general seller-profit representation to the tail above the
  posted price.
* `isMaxOn_sellerProfit_postedPriceProblem_of_netVirtualSurplus_sign` proves
  that a cutoff is globally optimal among feasible posted prices when net
  virtual surplus is nonpositive below it and nonnegative above it.
* The `_lowestType_` and `_highestType_` corollaries cover boundary optima.

The optimality statements use mathlib's `IsMaxOn`, which composes with the
wider extremum API while remaining the familiar comparison with every
feasible price.

## Scope and relationship to Riley--Zeckhauser

The net virtual-surplus weight `w(v) - r * f(v)` is division-free, so it is
meaningful even where the density vanishes. With constant continuation value
`r` and at values where `f(v) ≠ 0`, it corresponds to Riley and Zeckhauser's
`k(v) = (j(v) - π(v))f(v)`. Where `f(v) = 0`, no such correspondence is
asserted: the division-free weight remains meaningful, but the factorization
through virtual value need not hold.

The results here compare only posted prices and impose an explicit
single-crossing sign condition. They do not prove Riley and Zeckhauser's
Proposition 1, which optimizes over general monotone sale-probability rules,
permits the net weight to change sign multiple times, and thereby establishes
the fixed-price conclusion against haggling. They also do not prove the
remaining-buyers comparative static in Proposition 2.

Pointwise differentiation and the interior virtual-value first-order condition
are handled separately in `PostedPriceFirstOrder`. Type-dependent continuation
values, ironing, and stochastic-dominance comparative statics remain later
layers.

## Assumptions

The price lies in the type interval, the distribution is supported on that
interval and absolutely continuous with respect to Lebesgue measure, and the
chosen density agrees almost everywhere there with
`ValueDistribution.realDensity`. A chosen density is a representative, not a
canonical pointwise continuous density.

The global sign hypotheses are likewise stated almost everywhere on the
relevant subintervals. Below the candidate price the division-free net weight
`virtualSurplusWeight density value - continuationValue * density value` is
nonpositive; above the candidate it is nonnegative. This formulation is
unchanged if the chosen density is modified on a Lebesgue-null set and does
not require division by a possibly zero density.

Integrability is derived from existing envelope-IC, support, and
absolute-continuity results rather than assumed, so no integrability side
conditions appear in the public statements.
-/

namespace MathEconLib

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
    simpa [uIcc_of_le horder] using hdensity
  apply hcanonical.congr_ae
  filter_upwards [hae] with value hvalue
  simp [virtualSurplusWeight, hvalue]

/-- Interval integrability of net virtual surplus itself.

This is internal proof infrastructure for comparing cutoff integrals. It is
obtained from the allocation-weighted result by choosing the lowest type as
the posted price, so the cutoff allocation is one almost everywhere on the
type interval. -/
private theorem intervalIntegrable_netVirtualSurplus
    (D : ValueDistribution) (lowestType highestType : ℝ)
    (density : ℝ → ℝ) (continuationValue : ℝ)
    (horder : lowestType ≤ highestType)
    (hsupport : D.IsSupportedOnInterval lowestType highestType)
    (hD : (D : Measure ℝ) ≪ volume)
    (hdensity :
      density =ᵐ[volume.restrict (Icc lowestType highestType)] D.realDensity) :
    IntervalIntegrable
      (fun value =>
        D.virtualSurplusWeight density value -
          continuationValue * density value)
      volume lowestType highestType := by
  have hweighted :=
    intervalIntegrable_q_mul_netVirtualSurplus D lowestType highestType
      lowestType density continuationValue horder hsupport hD hdensity
  apply hweighted.congr_ae
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with value hvalue
  rw [uIoc_of_le horder] at hvalue
  rw [postedPriceProblem_q, if_pos hvalue.1.le]
  simp

/-! ## Comparing cutoff integrals -/

/-- If an integrable function is nonpositive almost everywhere below a cutoff
and nonnegative almost everywhere above it, then its tail integral from any
feasible point is at most its tail integral from the cutoff. -/
private theorem intervalIntegral_le_of_ae_nonpos_below_nonneg_above
    {lowestType highestType cutoff price : ℝ} {g : ℝ → ℝ}
    (hcutoff : cutoff ∈ Icc lowestType highestType)
    (hprice : price ∈ Icc lowestType highestType)
    (hint : IntervalIntegrable g volume lowestType highestType)
    (hbelow :
      ∀ᵐ value ∂volume.restrict (Icc lowestType cutoff), g value ≤ 0)
    (habove :
      ∀ᵐ value ∂volume.restrict (Icc cutoff highestType), 0 ≤ g value) :
    (∫ value in price..highestType, g value) ≤
      ∫ value in cutoff..highestType, g value := by
  have horder : lowestType ≤ highestType :=
    hcutoff.1.trans hcutoff.2
  have hcutoffU : cutoff ∈ uIcc lowestType highestType := by
    simpa [uIcc_of_le horder] using hcutoff
  have hpriceU : price ∈ uIcc lowestType highestType := by
    simpa [uIcc_of_le horder] using hprice
  have hcutoffPrice :=
    hint.mono_set (uIcc_subset_uIcc hcutoffU hpriceU)
  have hpriceTail :=
    hint.mono_set (uIcc_subset_uIcc hpriceU right_mem_uIcc)
  have hsplit :
      (∫ value in cutoff..price, g value) +
          ∫ value in price..highestType, g value =
        ∫ value in cutoff..highestType, g value :=
    intervalIntegral.integral_add_adjacent_intervals hcutoffPrice hpriceTail
  have hsegmentNonneg : 0 ≤ ∫ value in cutoff..price, g value := by
    rcases le_total price cutoff with hle | hge
    · have hsign :
          (fun value => g value) ≤ᵐ[volume.restrict (Icc price cutoff)]
            (fun _ : ℝ => (0 : ℝ)) :=
        ae_restrict_of_ae_restrict_of_subset
          (Icc_subset_Icc hprice.1 le_rfl) hbelow
      have hreverseNonpos : (∫ value in price..cutoff, g value) ≤ 0 := by
        have hmono :=
          intervalIntegral.integral_mono_ae_restrict hle
            hcutoffPrice.symm intervalIntegrable_const hsign
        simpa using hmono
      rw [intervalIntegral.integral_symm price cutoff]
      exact neg_nonneg.mpr hreverseNonpos
    · have hsign :
          (fun _ : ℝ => (0 : ℝ)) ≤ᵐ[volume.restrict (Icc cutoff price)]
            (fun value => g value) :=
        ae_restrict_of_ae_restrict_of_subset
          (Icc_subset_Icc le_rfl hprice.2) habove
      exact intervalIntegral.integral_nonneg_of_ae_restrict hge hsign
  rw [← hsplit]
  exact (le_add_iff_nonneg_left _).2 hsegmentNonneg

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

/-! ## Global optimality among posted prices -/

/-- **A single-crossing net virtual-surplus sign condition is sufficient for
global optimality among posted prices.**

Net virtual surplus is assumed nonpositive almost everywhere below the
candidate cutoff and nonnegative almost everywhere above it. Consequently,
lowering the cutoff only adds nonpositive surplus, while raising it removes
nonnegative surplus.

This theorem compares the candidate only with other posted prices in the type
interval. It does not establish optimality among arbitrary selling rules. -/
theorem isMaxOn_sellerProfit_postedPriceProblem_of_netVirtualSurplus_sign
    (D : ValueDistribution) (lowestType highestType cutoff : ℝ)
    (density : ℝ → ℝ) (continuationValue acquisitionCost : ℝ)
    (hcutoff : cutoff ∈ Icc lowestType highestType)
    (hsupport : D.IsSupportedOnInterval lowestType highestType)
    (hD : (D : Measure ℝ) ≪ volume)
    (hdensity :
      density =ᵐ[volume.restrict (Icc lowestType highestType)] D.realDensity)
    (hbelow :
      ∀ᵐ value ∂volume.restrict (Icc lowestType cutoff),
        D.virtualSurplusWeight density value -
          continuationValue * density value ≤ 0)
    (habove :
      ∀ᵐ value ∂volume.restrict (Icc cutoff highestType),
        0 ≤ D.virtualSurplusWeight density value -
          continuationValue * density value) :
    IsMaxOn
      (fun price =>
        D.sellerProfit (postedPriceProblem lowestType highestType price)
          continuationValue acquisitionCost)
      (Icc lowestType highestType) cutoff := by
  intro price hprice
  change
    D.sellerProfit (postedPriceProblem lowestType highestType price)
        continuationValue acquisitionCost ≤
      D.sellerProfit (postedPriceProblem lowestType highestType cutoff)
        continuationValue acquisitionCost
  have horder : lowestType ≤ highestType :=
    hcutoff.1.trans hcutoff.2
  have hnet :=
    intervalIntegrable_netVirtualSurplus D lowestType highestType density
      continuationValue horder hsupport hD hdensity
  have htailComparison :=
    intervalIntegral_le_of_ae_nonpos_below_nonneg_above
      hcutoff hprice hnet hbelow habove
  rw [D.sellerProfit_postedPriceProblem_eq_intervalIntegral_netVirtualSurplus
      lowestType highestType price density continuationValue acquisitionCost
      hprice hsupport hD hdensity,
    D.sellerProfit_postedPriceProblem_eq_intervalIntegral_netVirtualSurplus
      lowestType highestType cutoff density continuationValue acquisitionCost
      hcutoff hsupport hD hdensity]
  simpa [add_comm] using
    add_le_add_left htailComparison (continuationValue - acquisitionCost)

/-! ## Boundary optimality -/

/-- The lowest feasible posted price is optimal when net virtual surplus is
nonnegative almost everywhere on the entire type interval. -/
theorem isMaxOn_sellerProfit_postedPriceProblem_lowestType_of_netVirtualSurplus_nonneg
    (D : ValueDistribution) (lowestType highestType : ℝ)
    (density : ℝ → ℝ) (continuationValue acquisitionCost : ℝ)
    (horder : lowestType ≤ highestType)
    (hsupport : D.IsSupportedOnInterval lowestType highestType)
    (hD : (D : Measure ℝ) ≪ volume)
    (hdensity :
      density =ᵐ[volume.restrict (Icc lowestType highestType)] D.realDensity)
    (hnonneg :
      ∀ᵐ value ∂volume.restrict (Icc lowestType highestType),
        0 ≤ D.virtualSurplusWeight density value -
          continuationValue * density value) :
    IsMaxOn
      (fun price =>
        D.sellerProfit (postedPriceProblem lowestType highestType price)
          continuationValue acquisitionCost)
      (Icc lowestType highestType) lowestType := by
  apply
    D.isMaxOn_sellerProfit_postedPriceProblem_of_netVirtualSurplus_sign
      lowestType highestType lowestType density continuationValue
      acquisitionCost ⟨le_rfl, horder⟩ hsupport hD hdensity
  · simp
  · exact hnonneg

/-- The highest feasible posted price is optimal when net virtual surplus is
nonpositive almost everywhere on the entire type interval. -/
theorem isMaxOn_sellerProfit_postedPriceProblem_highestType_of_netVirtualSurplus_nonpos
    (D : ValueDistribution) (lowestType highestType : ℝ)
    (density : ℝ → ℝ) (continuationValue acquisitionCost : ℝ)
    (horder : lowestType ≤ highestType)
    (hsupport : D.IsSupportedOnInterval lowestType highestType)
    (hD : (D : Measure ℝ) ≪ volume)
    (hdensity :
      density =ᵐ[volume.restrict (Icc lowestType highestType)] D.realDensity)
    (hnonpos :
      ∀ᵐ value ∂volume.restrict (Icc lowestType highestType),
        D.virtualSurplusWeight density value -
          continuationValue * density value ≤ 0) :
    IsMaxOn
      (fun price =>
        D.sellerProfit (postedPriceProblem lowestType highestType price)
          continuationValue acquisitionCost)
      (Icc lowestType highestType) highestType := by
  apply
    D.isMaxOn_sellerProfit_postedPriceProblem_of_netVirtualSurplus_sign
      lowestType highestType highestType density continuationValue
      acquisitionCost ⟨horder, le_rfl⟩ hsupport hD hdensity
  · exact hnonpos
  · simp

end ValueDistribution

end

end MathEconLib
