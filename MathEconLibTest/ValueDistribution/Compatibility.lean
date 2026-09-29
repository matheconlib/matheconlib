module

import MathEconLib.Auction.ValueDistribution
import MathEconLib.ValueDistribution
import Mathlib.MeasureTheory.Measure.DiracProba

/-!
# Compatibility Checks for Value Distributions and Posted Pricing

This file pins the principal public contracts of the young value-distribution
layer without adding declarations to the production library. It also checks
the atomic tie-breaking behavior of the distributional posted-price example.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set SingleParameterProblem

namespace ValueDistributionCompatibility

universe u

/-! ## Distribution and demand semantics -/

/-- The distribution of a random variable uses the ordinary pushforward
measure. -/
example {Ω : Type*} [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω) (X : Ω → ℝ) (hX : AEMeasurable X μ) :
    ((ValueDistribution.ofRandomVariable μ X hX : ValueDistribution) :
        Measure ℝ) = Measure.map X μ :=
  ValueDistribution.toMeasure_ofRandomVariable μ X hX

/-- Bounded support remains an optional almost-everywhere predicate. -/
example (D : ValueDistribution) (lower upper : ℝ) :
    D.IsSupportedOnInterval lower upper ↔
      ∀ᵐ value ∂(D : Measure ℝ), value ∈ Icc lower upper :=
  Iff.rfl

/-- Posted-price demand is the probability of the closed upper tail. -/
example (D : ValueDistribution) (price : ℝ) :
    D.probAtLeast price = D (Ici price) :=
  rfl

/-- Demand remains nonnegative. -/
example (D : ValueDistribution) (price : ℝ) :
    0 ≤ D.probAtLeast price :=
  D.probAtLeast_nonneg price

/-- Demand remains at most one. -/
example (D : ValueDistribution) (price : ℝ) :
    D.probAtLeast price ≤ 1 :=
  D.probAtLeast_le_one price

/-- Demand is antitone in the posted price. -/
example (D : ValueDistribution) :
    Antitone D.probAtLeast :=
  D.antitone_probAtLeast

/-- The atom-sensitive CDF identity remains part of the distribution API. -/
example (D : ValueDistribution) (price : ℝ) :
    D.probAtLeast price =
      1 - cdf (D : Measure ℝ) price + D {price} :=
  D.probAtLeast_eq_one_sub_cdf_add_mass price

/-- Atomless demand remains one minus the CDF. -/
example (D : ValueDistribution) [NoAtoms (D : Measure ℝ)] (price : ℝ) :
    D.probAtLeast price = 1 - cdf (D : Measure ℝ) price :=
  D.probAtLeast_eq_one_sub_cdf price

/-! ## Density, virtual surplus, and tail integration -/

/-- The canonical real density remains the real-valued Radon--Nikodym
representative with respect to Lebesgue measure. -/
example (D : ValueDistribution) (value : ℝ) :
    D.realDensity value =
      ((D : Measure ℝ).rnDeriv (volume : Measure ℝ) value).toReal :=
  rfl

/-- Under absolute continuity, integration against a value distribution can
be rewritten using its canonical real density. -/
example (D : ValueDistribution) (g : ℝ → ℝ)
    (hD : (D : Measure ℝ) ≪ volume) :
    (∫ value, g value ∂(D : Measure ℝ)) =
      ∫ value, D.realDensity value * g value ∂volume :=
  D.integral_eq_integral_realDensity_mul g hD

/-- Virtual-surplus weight is value times density minus closed-tail demand. -/
example (D : ValueDistribution) (density : ℝ → ℝ) (value : ℝ) :
    D.virtualSurplusWeight density value =
      value * density value - D.probAtLeast value :=
  rfl

/-- Virtual value is defined secondarily by dividing virtual-surplus weight
by the chosen density. -/
example (D : ValueDistribution) (density : ℝ → ℝ) (value : ℝ) :
    D.virtualValue density value =
      D.virtualSurplusWeight density value / density value :=
  rfl

/-- The economically useful factorization explicitly requires nonzero
density, even though division itself is total in Lean. -/
example (D : ValueDistribution) (density : ℝ → ℝ) (value : ℝ)
    (hdensity : density value ≠ 0) :
    D.virtualSurplusWeight density value =
      density value * D.virtualValue density value :=
  D.virtualSurplusWeight_eq_density_mul_virtualValue
    density value hdensity

/-- The density-free tail identity preserves the closed-tail convention and
therefore does not assume atomlessness. -/
example (D : ValueDistribution) {lower upper : ℝ}
    (horder : lower ≤ upper)
    (hsupport : D.IsSupportedOnInterval lower upper)
    {q : ℝ → ℝ}
    (hq_measurable : Measurable q)
    (hq_integrable : IntervalIntegrable q volume lower upper)
    (hq_nonneg : ∀ cutoff ∈ Icc lower upper, 0 ≤ q cutoff) :
    (∫ value, (∫ cutoff in lower..value, q cutoff) ∂D) =
      ∫ cutoff in lower..upper,
        q cutoff * D.probAtLeast cutoff :=
  D.integral_intervalIntegral_eq_integral_mul_probAtLeast
    horder hsupport hq_measurable hq_integrable hq_nonneg

/-- Changing a density representative at one point does not change the
resulting Lebesgue integral. -/
example (D : ValueDistribution) (g : ℝ → ℝ)
    (point replacement : ℝ) (hD : (D : Measure ℝ) ≪ volume) :
    (∫ value, g value ∂(D : Measure ℝ)) =
      ∫ value,
        Function.update D.realDensity point replacement value * g value
          ∂volume := by
  apply D.integral_eq_integral_density_mul
    (Function.update D.realDensity point replacement) g hD
  filter_upwards [show ∀ᵐ value ∂volume, value ≠ point by
    simp [ae_iff]] with value hvalue
  simp [hvalue]

/-! ## Expected quantities and seller objective -/

section SingleParameter

variable {Action : Type u} (D : ValueDistribution)
  (P : SingleParameterProblem Action)

/-- Expected allocation integrates the induced on-strategy allocation. -/
example :
    D.expectedAllocation P = ∫ value, P.q value ∂(D : Measure ℝ) :=
  rfl

/-- Expected payment integrates the payment generated by the strategy. -/
example :
    D.expectedPayment P =
      ∫ value, P.payment (P.strategy value) ∂(D : Measure ℝ) :=
  rfl

/-- Seller profit keeps continuation value, acquisition cost, payment, and
allocation economically distinct. -/
example (continuationValue acquisitionCost : ℝ) :
    D.sellerProfit P continuationValue acquisitionCost =
      continuationValue - acquisitionCost + D.expectedPayment P -
        continuationValue * D.expectedAllocation P :=
  rfl

/-- Reduction preserves expected allocation. -/
example :
    D.expectedAllocation P.reduce = D.expectedAllocation P :=
  D.expectedAllocation_reduce P

/-- Reduction preserves expected payment. -/
example :
    D.expectedPayment P.reduce = D.expectedPayment P :=
  D.expectedPayment_reduce P

/-- Reduction preserves the seller objective. -/
example (continuationValue acquisitionCost : ℝ) :
    D.sellerProfit P.reduce continuationValue acquisitionCost =
      D.sellerProfit P continuationValue acquisitionCost :=
  D.sellerProfit_reduce P continuationValue acquisitionCost

/-! ### Expected-payment and seller-profit representations -/

/-- Under envelope IC and absolute continuity, allocation weighted by the
canonical real density remains interval integrable. -/
example [SingleParameterProblem.HasEnvelopeIC P]
    (horder : P.lowestType ≤ P.highestType)
    (hD : (D : Measure ℝ) ≪ volume) :
    IntervalIntegrable
      (fun value => P.q value * D.realDensity value)
      volume P.lowestType P.highestType :=
  D.intervalIntegrable_q_mul_realDensity P horder hD

/-- With bounded support as well, allocation weighted by canonical virtual
surplus remains interval integrable. -/
example [SingleParameterProblem.HasEnvelopeIC P]
    (horder : P.lowestType ≤ P.highestType)
    (hsupport : D.IsSupportedOnInterval P.lowestType P.highestType)
    (hD : (D : Measure ℝ) ≪ volume) :
    IntervalIntegrable
      (fun value =>
        P.q value * D.virtualSurplusWeight D.realDensity value)
      volume P.lowestType P.highestType :=
  D.intervalIntegrable_q_mul_virtualSurplusWeight_realDensity
    P horder hsupport hD

/-- The primary expected-payment representation is density-free. -/
example [SingleParameterProblem.HasEnvelopeIC P]
    (horder : P.lowestType ≤ P.highestType)
    (hsupport : D.IsSupportedOnInterval P.lowestType P.highestType) :
    D.expectedPayment P =
      (∫ value, value * P.q value ∂(D : Measure ℝ)) -
        P.U P.lowestType -
        ∫ cutoff in P.lowestType..P.highestType,
          P.q cutoff * D.probAtLeast cutoff :=
  D.expectedPayment_eq_integral_value_mul_q_sub_integral_tail
    P horder hsupport

/-- Under absolute continuity, expected payment is allocation-weighted
canonical virtual surplus minus lowest-type utility. -/
example [SingleParameterProblem.HasEnvelopeIC P]
    (horder : P.lowestType ≤ P.highestType)
    (hsupport : D.IsSupportedOnInterval P.lowestType P.highestType)
    (hD : (D : Measure ℝ) ≪ volume) :
    D.expectedPayment P =
      (∫ value in P.lowestType..P.highestType,
        P.q value *
          D.virtualSurplusWeight D.realDensity value) -
        P.U P.lowestType :=
  D.expectedPayment_eq_integral_q_mul_virtualSurplusWeight_realDensity
    P horder hsupport hD

/-- Any density agreeing almost everywhere with the canonical representative
on the type interval gives the same expected-payment identity. -/
example [SingleParameterProblem.HasEnvelopeIC P]
    (density : ℝ → ℝ)
    (horder : P.lowestType ≤ P.highestType)
    (hsupport : D.IsSupportedOnInterval P.lowestType P.highestType)
    (hD : (D : Measure ℝ) ≪ volume)
    (hdensity :
      density =ᵐ[volume.restrict P.typeInterval] D.realDensity) :
    D.expectedPayment P =
      (∫ value in P.lowestType..P.highestType,
        P.q value * D.virtualSurplusWeight density value) -
        P.U P.lowestType :=
  D.expectedPayment_eq_integral_q_mul_virtualSurplusWeight
    P density horder hsupport hD hdensity

/-- The canonical seller-profit representation keeps continuation value,
acquisition cost, and lowest-type information rent distinct. -/
example [SingleParameterProblem.HasEnvelopeIC P]
    (continuationValue acquisitionCost : ℝ)
    (horder : P.lowestType ≤ P.highestType)
    (hsupport : D.IsSupportedOnInterval P.lowestType P.highestType)
    (hD : (D : Measure ℝ) ≪ volume) :
    D.sellerProfit P continuationValue acquisitionCost =
      continuationValue - acquisitionCost - P.U P.lowestType +
        ∫ value in P.lowestType..P.highestType,
          P.q value *
            (D.virtualSurplusWeight D.realDensity value -
              continuationValue * D.realDensity value) :=
  D.sellerProfit_eq_virtualSurplus_realDensity P
    continuationValue acquisitionCost horder hsupport hD

/-- Any almost-everywhere equivalent density representative gives the same
seller-profit decomposition. -/
example [SingleParameterProblem.HasEnvelopeIC P]
    (density : ℝ → ℝ) (continuationValue acquisitionCost : ℝ)
    (horder : P.lowestType ≤ P.highestType)
    (hsupport : D.IsSupportedOnInterval P.lowestType P.highestType)
    (hD : (D : Measure ℝ) ≪ volume)
    (hdensity :
      density =ᵐ[volume.restrict P.typeInterval] D.realDensity) :
    D.sellerProfit P continuationValue acquisitionCost =
      continuationValue - acquisitionCost - P.U P.lowestType +
        ∫ value in P.lowestType..P.highestType,
          P.q value *
            (D.virtualSurplusWeight density value -
              continuationValue * density value) :=
  D.sellerProfit_eq_virtualSurplus P density
    continuationValue acquisitionCost horder hsupport hD hdensity

/-! ### Semantic examples -/

/-- The primary expected-payment theorem applies to an atomic value law. -/
example [SingleParameterProblem.HasEnvelopeIC P]
    (value : ℝ) (horder : P.lowestType ≤ P.highestType)
    (hvalue : value ∈ P.typeInterval) :
    ValueDistribution.expectedPayment (diracProba value) P =
      (∫ reportedValue,
          reportedValue * P.q reportedValue ∂(diracProba value)) -
        P.U P.lowestType -
        ∫ cutoff in P.lowestType..P.highestType,
          P.q cutoff *
            ValueDistribution.probAtLeast (diracProba value) cutoff := by
  apply ValueDistribution.expectedPayment_eq_integral_value_mul_q_sub_integral_tail
    (diracProba value) P horder
  rw [ValueDistribution.IsSupportedOnInterval]
  change ∀ᵐ reportedValue ∂Measure.dirac value,
    reportedValue ∈ P.typeInterval
  simpa [ae_dirac_eq] using hvalue

/-- Under absolute continuity, the chosen-density expected-payment theorem
uses the familiar one-minus-CDF tail. -/
example [SingleParameterProblem.HasEnvelopeIC P]
    (density : ℝ → ℝ)
    (horder : P.lowestType ≤ P.highestType)
    (hsupport : D.IsSupportedOnInterval P.lowestType P.highestType)
    (hD : (D : Measure ℝ) ≪ volume)
    (hdensity :
      density =ᵐ[volume.restrict P.typeInterval] D.realDensity) :
    D.expectedPayment P =
      (∫ value in P.lowestType..P.highestType,
        P.q value *
          (value * density value -
            (1 - cdf (D : Measure ℝ) value))) -
        P.U P.lowestType :=
  D.expectedPayment_eq_integral_q_mul_sub_one_sub_cdf
    P density horder hsupport hD hdensity

/-- Applying the density-free theorem to the reduced problem recovers the
original induced allocation and utility. -/
example [SingleParameterProblem.HasEnvelopeIC P]
    (horder : P.lowestType ≤ P.highestType)
    (hsupport : D.IsSupportedOnInterval P.lowestType P.highestType) :
    D.expectedPayment P.reduce =
      (∫ value, value * P.q value ∂(D : Measure ℝ)) -
        P.U P.lowestType -
        ∫ cutoff in P.lowestType..P.highestType,
          P.q cutoff * D.probAtLeast cutoff := by
  simpa [P.reduce_q, P.reduce_U] using
    D.expectedPayment_eq_integral_value_mul_q_sub_integral_tail
      P.reduce horder hsupport

end SingleParameter

/-! ## Distributional posted pricing -/

section PostedPrice

variable (D : ValueDistribution) (lowestType highestType price : ℝ)

/-- Expected allocation at a posted price equals demand. -/
example :
    D.expectedAllocation
        (postedPriceProblem lowestType highestType price) =
      D.probAtLeast price :=
  D.expectedAllocation_postedPriceProblem lowestType highestType price

/-- Expected payment is price times demand. -/
example :
    D.expectedPayment
        (postedPriceProblem lowestType highestType price) =
      price * D.probAtLeast price :=
  D.expectedPayment_postedPriceProblem lowestType highestType price

/-- The general posted-price seller-profit formula remains available. -/
example (continuationValue acquisitionCost : ℝ) :
    D.sellerProfit
        (postedPriceProblem lowestType highestType price)
        continuationValue acquisitionCost =
      continuationValue - acquisitionCost +
        (price - continuationValue) * D.probAtLeast price :=
  D.sellerProfit_postedPriceProblem lowestType highestType price
    continuationValue acquisitionCost

/-- The pointwise CDF derivative determines the posted-price profit
derivative. -/
example [NoAtoms (D : Measure ℝ)] (density : ℝ → ℝ)
    (continuationValue acquisitionCost : ℝ)
    (hcdf : HasDerivAt (cdf (D : Measure ℝ)) (density price) price) :
    HasDerivAt
      (fun candidatePrice ↦
        D.sellerProfit
          (postedPriceProblem lowestType highestType candidatePrice)
          continuationValue acquisitionCost)
      (-(D.virtualSurplusWeight density price -
          continuationValue * density price))
      price :=
  D.hasDerivAt_sellerProfit_postedPriceProblem
    lowestType highestType density continuationValue acquisitionCost price hcdf

/-- An interior local profit maximum has zero division-free net virtual
surplus. -/
example [NoAtoms (D : Measure ℝ)] (density : ℝ → ℝ)
    (continuationValue acquisitionCost : ℝ)
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
      continuationValue * density price = 0 :=
  D.netVirtualSurplus_eq_zero_of_isLocalMaxOn_sellerProfit_postedPriceProblem
    lowestType highestType density continuationValue acquisitionCost price
    hprice hcdf hmax

/-- Nonzero pointwise density turns the division-free condition into the
virtual-value equation. -/
example [NoAtoms (D : Measure ℝ)] (density : ℝ → ℝ)
    (continuationValue acquisitionCost : ℝ)
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
    D.virtualValue density price = continuationValue :=
  D.virtualValue_eq_continuationValue_of_isLocalMaxOn_sellerProfit_postedPriceProblem
    lowestType highestType density continuationValue acquisitionCost price
    hprice hcdf hmax hdensity

/-- With no continuation value, the interior first-order condition says that
virtual value is zero. -/
example [NoAtoms (D : Measure ℝ)] (density : ℝ → ℝ)
    (acquisitionCost : ℝ)
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
    D.virtualValue density price = 0 :=
  D.virtualValue_eq_zero_of_isLocalMaxOn_sellerProfit_postedPriceProblem
    lowestType highestType density acquisitionCost price hprice hcdf hmax hdensity

/-- Under absolute continuity, posted-price seller profit is the tail
integral of division-free net virtual surplus. -/
example (density : ℝ → ℝ) (continuationValue acquisitionCost : ℝ)
    (hprice : price ∈ Icc lowestType highestType)
    (hsupport : D.IsSupportedOnInterval lowestType highestType)
    (hD : (D : Measure ℝ) ≪ volume)
    (hdensity :
      density =ᵐ[volume.restrict (Icc lowestType highestType)] D.realDensity) :
    D.sellerProfit
        (postedPriceProblem lowestType highestType price)
        continuationValue acquisitionCost =
      continuationValue - acquisitionCost +
        ∫ value in price..highestType,
          (D.virtualSurplusWeight density value -
            continuationValue * density value) :=
  D.sellerProfit_postedPriceProblem_eq_intervalIntegral_netVirtualSurplus
    lowestType highestType price density continuationValue acquisitionCost
    hprice hsupport hD hdensity

/-- A single-crossing sign condition pins the global posted-price optimality
contract. -/
example (cutoff : ℝ) (density : ℝ → ℝ)
    (continuationValue acquisitionCost : ℝ)
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
      (fun candidatePrice =>
        D.sellerProfit
          (postedPriceProblem lowestType highestType candidatePrice)
          continuationValue acquisitionCost)
      (Icc lowestType highestType) cutoff :=
  D.isMaxOn_sellerProfit_postedPriceProblem_of_netVirtualSurplus_sign
    lowestType highestType cutoff density continuationValue acquisitionCost
    hcutoff hsupport hD hdensity hbelow habove

/-- Nonnegative net virtual surplus makes the lowest feasible price
optimal. -/
example (density : ℝ → ℝ) (continuationValue acquisitionCost : ℝ)
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
      (fun candidatePrice =>
        D.sellerProfit
          (postedPriceProblem lowestType highestType candidatePrice)
          continuationValue acquisitionCost)
      (Icc lowestType highestType) lowestType :=
  D.isMaxOn_sellerProfit_postedPriceProblem_lowestType_of_netVirtualSurplus_nonneg
    lowestType highestType density continuationValue acquisitionCost horder
    hsupport hD hdensity hnonneg

/-- Nonpositive net virtual surplus makes the highest feasible price
optimal. -/
example (density : ℝ → ℝ) (continuationValue acquisitionCost : ℝ)
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
      (fun candidatePrice =>
        D.sellerProfit
          (postedPriceProblem lowestType highestType candidatePrice)
          continuationValue acquisitionCost)
      (Icc lowestType highestType) highestType :=
  D.isMaxOn_sellerProfit_postedPriceProblem_highestType_of_netVirtualSurplus_nonpos
    lowestType highestType density continuationValue acquisitionCost horder
    hsupport hD hdensity hnonpos

/-- Zero continuation value and acquisition cost recover price-times-demand
revenue. -/
example :
    D.sellerProfit
        (postedPriceProblem lowestType highestType price) 0 0 =
      price * D.probAtLeast price :=
  D.sellerProfit_postedPriceProblem_zero lowestType highestType price

/-- A common unconditional acquisition cost cancels from price comparisons. -/
example (price₂ continuationValue acquisitionCost : ℝ) :
    D.sellerProfit
          (postedPriceProblem lowestType highestType price)
          continuationValue acquisitionCost -
        D.sellerProfit
          (postedPriceProblem lowestType highestType price₂)
          continuationValue acquisitionCost =
      (price - continuationValue) * D.probAtLeast price -
        (price₂ - continuationValue) * D.probAtLeast price₂ :=
  D.sellerProfit_postedPriceProblem_sub lowestType highestType price price₂
    continuationValue acquisitionCost

/-- A buyer whose value equals the posted price purchases: a Dirac mass at
the price therefore has expected allocation one. -/
example :
    ValueDistribution.expectedAllocation (diracProba price)
        (postedPriceProblem lowestType highestType price) = 1 := by
  rw [ValueDistribution.expectedAllocation_postedPriceProblem]
  unfold ValueDistribution.probAtLeast
  simp [ProbabilityMeasure.coeFn_def]

end PostedPrice

/-! ## Auction bridge -/

section Auction

variable {Ω : Type} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} (A : Auction Ω n)

/-- A bidder's value distribution has the expected pushforward measure. -/
example (i : Fin n) :
    ((A.valueDistribution i : ValueDistribution) : Measure ℝ) =
      Measure.map (A.θ i) ℙ :=
  A.toMeasure_valueDistribution i

/-- The existing auction density assumption makes each bidder's value
distribution absolutely continuous; no second density class is introduced. -/
example [Auction.HasDensity A] (i : Fin n) :
    ((A.valueDistribution i : ValueDistribution) : Measure ℝ) ≪ volume :=
  A.valueDistribution_absolutelyContinuous i

/-- Bounded auction types supply optional interval support. -/
example [Auction.HasBoundedTypes A] (i : Fin n) :
    (A.valueDistribution i).IsSupportedOnInterval
      (A.θmin i) (A.θmax i) :=
  A.valueDistribution_isSupportedOnInterval i

/-- Identically distributed auction types give equal bidder distributions. -/
example [NeZero n] [Auction.HasIdenticalTypes A] (i j : Fin n) :
    A.valueDistribution i = A.valueDistribution j :=
  A.valueDistribution_eq_of_identicalTypes i j

/-- Each bidder distribution's CDF agrees with the existing common CDF. -/
example [NeZero n] [Auction.HasIdenticalTypes A]
    (i : Fin n) (value : ℝ) :
    cdf ((A.valueDistribution i : ValueDistribution) : Measure ℝ) value =
      A.commonCDF value :=
  A.cdf_valueDistribution_eq_commonCDF i value

end Auction

end ValueDistributionCompatibility

end
