/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Auction.Typeclasses
public import MathEconLib.ValueDistribution.Basic

/-!
# Bidder Value Distributions

This file connects an auction's type random variables to the reusable
`ValueDistribution` layer. For bidder `i`, `A.valueDistribution i` is the
pushforward of the auction's probability measure along `A.θ i`.

The bridge is additive: it does not add a field to `Auction`, replace
`Auction.commonCDF`, or require boundedness, identical types, independence, or
a density. Later results in this file can request those assumptions separately
when they use them.
-/

namespace MathEconLib

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Auction

variable {Ω : Type} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} (A : Auction Ω n)

/-- The probability distribution of bidder `i`'s value.

This is the pushforward of the auction's probability measure along the type
random variable `A.θ i`. It is defined for every auction and bidder, without
distributional symmetry or bounded-support assumptions. -/
noncomputable def valueDistribution (i : Fin n) : ValueDistribution :=
  ValueDistribution.ofRandomVariable
    (⟨ℙ, inferInstance⟩ : ProbabilityMeasure Ω)
    (A.θ i)
    (A.θ_measurable i).aemeasurable

/-- The measure underlying a bidder's value distribution is the ordinary
pushforward of the auction measure along that bidder's type random variable. -/
@[simp]
theorem toMeasure_valueDistribution (i : Fin n) :
    ((A.valueDistribution i : ValueDistribution) : Measure ℝ) =
      Measure.map (A.θ i) ℙ := by
  exact ValueDistribution.toMeasure_ofRandomVariable _ _ (A.θ_measurable i).aemeasurable

/-- Under the auction's existing density assumption, bidder `i`'s value
distribution is absolutely continuous with respect to Lebesgue measure.

This is a named bridge rather than a global instance: auction-facing density
results reuse `Auction.HasDensity`, while standalone value-distribution
theorems continue to request absolute continuity explicitly. -/
theorem valueDistribution_absolutelyContinuous
    [HasDensity A] (i : Fin n) :
    ((A.valueDistribution i : ValueDistribution) : Measure ℝ) ≪ volume := by
  rw [A.toMeasure_valueDistribution]
  let : HasPDF (A.θ i) ℙ (volume : Measure ℝ) :=
    HasDensity.θ_hasPDF (A := A) i
  exact HasPDF.absolutelyContinuous

/-- Under the auction's bounded-types assumption, bidder `i`'s value
distribution is supported on that bidder's declared type interval. -/
theorem valueDistribution_isSupportedOnInterval
    [HasBoundedTypes A] (i : Fin n) :
    (A.valueDistribution i).IsSupportedOnInterval
      (A.θmin i) (A.θmax i) := by
  rw [ValueDistribution.IsSupportedOnInterval,
    A.toMeasure_valueDistribution]
  apply (ae_map_iff
    (p := fun value => value ∈ Set.Icc (A.θmin i) (A.θmax i))
    (A.θ_measurable i).aemeasurable measurableSet_Icc).2
  exact ae_of_all ℙ (HasBoundedTypes.θ_in (A := A) i)

/-- Under identical types, any two bidders have the same value distribution. -/
theorem valueDistribution_eq_of_identicalTypes
    [NeZero n] [HasIdenticalTypes A] (i j : Fin n) :
    A.valueDistribution i = A.valueDistribution j := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [A.toMeasure_valueDistribution, A.toMeasure_valueDistribution]
  exact (HasIdenticalTypes.θ_identical (A := A) i j).map_eq

/-- Under identical types, the CDF of any bidder's value distribution agrees
with the auction's existing common CDF. -/
theorem cdf_valueDistribution_eq_commonCDF
    [NeZero n] [HasIdenticalTypes A] (i : Fin n) (value : ℝ) :
    cdf ((A.valueDistribution i : ValueDistribution) : Measure ℝ) value =
      A.commonCDF value := by
  rw [A.valueDistribution_eq_of_identicalTypes i 0,
    A.toMeasure_valueDistribution]

end Auction

end

end MathEconLib
