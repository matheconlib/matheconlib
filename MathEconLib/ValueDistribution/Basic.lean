/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Real-Valued Probability Distributions

This file gives real-valued probability measures a small amount of economic
vocabulary. The underlying probability theory remains mathlib's
`ProbabilityMeasure ℝ`; `ValueDistribution` is a transparent abbreviation,
not a new representation.

Bounded support is an optional property. This lets the same definition
represent bounded, unbounded, continuous, discrete, and mixed distributions.
-/

namespace MathEconLib

@[expose] public section

open MeasureTheory Set

/-- A probability distribution for a real-valued economic type or value.

This is a transparent abbreviation for mathlib's `ProbabilityMeasure ℝ`.
It adds terminology and a namespace without wrapping the measure or creating
a separate probability theory. -/
abbrev ValueDistribution := ProbabilityMeasure ℝ

namespace ValueDistribution

/-- The distribution of a real-valued random variable.

The source is itself supplied as a probability measure. The result is its
pushforward along `X`. -/
noncomputable def ofRandomVariable
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω) (X : Ω → ℝ)
    (hX : AEMeasurable X μ) : ValueDistribution := by
  -- Measurability remains a precondition even though Mathlib's map is total.
  have _ := hX
  exact μ.map X

/-- The measure underlying `ofRandomVariable` is the ordinary pushforward
measure. -/
@[simp]
theorem toMeasure_ofRandomVariable
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω) (X : Ω → ℝ)
    (hX : AEMeasurable X μ) :
    ((ofRandomVariable μ X hX : ValueDistribution) : Measure ℝ) =
      Measure.map X μ :=
  ProbabilityMeasure.toMeasure_map μ

/-- The distribution is concentrated on the closed interval `[lower, upper]`.

This is deliberately a property rather than a field of `ValueDistribution`:
definitions such as demand and expectation make sense without bounded
support, while theorems that need bounds can request this predicate. -/
def IsSupportedOnInterval
    (D : ValueDistribution) (lower upper : ℝ) : Prop :=
  ∀ᵐ value ∂(D : Measure ℝ), value ∈ Icc lower upper

end ValueDistribution

end

end MathEconLib
