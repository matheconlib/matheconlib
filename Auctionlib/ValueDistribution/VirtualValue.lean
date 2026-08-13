module

public import Auctionlib.ValueDistribution.Demand

/-!
# Virtual Surplus for Real-Valued Distributions

This file defines the virtual-surplus weight associated with a value
distribution and a chosen real-valued density. The weight is primary because
it is division-free and remains meaningful where the density vanishes.

Virtual value is defined secondarily by dividing the weight by the density.
Lean's division is total, including at zero, but the familiar factorization of
virtual-surplus weight into density times virtual value requires a nonzero
density and is stated with that hypothesis explicitly.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ValueDistribution

/-- The virtual-surplus weight associated with distribution `D` and chosen
density `density`.

The closed-tail probability `D.probAtLeast value` preserves the library's
posted-price tie convention and remains meaningful for distributions with
atoms. Applications interpreting `density` as a density of `D` should supply
the appropriate absolute-continuity and almost-everywhere agreement
assumptions in the theorem that uses this definition. -/
def virtualSurplusWeight
    (D : ValueDistribution) (density : ℝ → ℝ) (value : ℝ) : ℝ :=
  value * density value - D.probAtLeast value

/-- Virtual value associated with distribution `D` and chosen density
`density`.

This is the virtual-surplus weight divided by the density. At a point where
`density value = 0`, Lean still assigns a value to the quotient, but the
economic factorization into density times virtual value is not valid without a
nonzero-density hypothesis. -/
noncomputable def virtualValue
    (D : ValueDistribution) (density : ℝ → ℝ) (value : ℝ) : ℝ :=
  D.virtualSurplusWeight density value / density value

/-- Where the chosen density is nonzero, virtual-surplus weight factors as
density times virtual value. -/
theorem virtualSurplusWeight_eq_density_mul_virtualValue
    (D : ValueDistribution) (density : ℝ → ℝ) (value : ℝ)
    (hdensity : density value ≠ 0) :
    D.virtualSurplusWeight density value =
      density value * D.virtualValue density value := by
  simpa [virtualValue] using
    (mul_div_cancel₀ (D.virtualSurplusWeight density value) hdensity).symm

/-- For an atomless distribution, virtual-surplus weight has the familiar CDF
form `value * density value - (1 - F(value))`. -/
theorem virtualSurplusWeight_eq_sub_one_sub_cdf
    (D : ValueDistribution) [NoAtoms (D : Measure ℝ)]
    (density : ℝ → ℝ) (value : ℝ) :
    D.virtualSurplusWeight density value =
      value * density value - (1 - cdf (D : Measure ℝ) value) := by
  rw [virtualSurplusWeight, D.probAtLeast_eq_one_sub_cdf]

end ValueDistribution

end
