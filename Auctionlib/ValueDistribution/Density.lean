module

public import Auctionlib.ValueDistribution.Basic
public import Mathlib.Probability.Density

/-!
# Densities of Real-Valued Probability Distributions

This file gives a `ValueDistribution` a real-valued view of mathlib's
Radon--Nikodym derivative with respect to Lebesgue measure.

The definition introduces no new density class. For a distribution that is
absolutely continuous with respect to Lebesgue measure, it is a density of the
whole distribution. Without absolute continuity, it describes only the
absolutely continuous part. Theorems that use it to rewrite integration must
therefore assume absolute continuity explicitly.

The Radon--Nikodym derivative is determined only almost everywhere. A chosen
pointwise density used in an application should consequently be related to
`realDensity` by almost-everywhere equality, not necessarily literal function
equality.
-/

@[expose] public section

open MeasureTheory

namespace ValueDistribution

/-- The canonical real-valued density representative of `D` with respect to
Lebesgue measure.

Mathlib's Radon--Nikodym derivative takes values in `ℝ≥0∞`. The conversion
`toReal` gives the real-valued representative used in economic integrals. This
definition is meaningful for every distribution, but it represents all of `D`
only when `(D : Measure ℝ) ≪ volume`. -/
noncomputable def realDensity (D : ValueDistribution) (value : ℝ) : ℝ :=
  ((D : Measure ℝ).rnDeriv (volume : Measure ℝ) value).toReal

/-- The canonical real-valued density representative is measurable. -/
theorem measurable_realDensity (D : ValueDistribution) :
    Measurable D.realDensity := by
  unfold realDensity
  fun_prop

/-- The canonical real-valued density representative is nonnegative. -/
theorem realDensity_nonneg (D : ValueDistribution) (value : ℝ) :
    0 ≤ D.realDensity value :=
  ENNReal.toReal_nonneg

/-! ## Integration -/

/-- Integration under an absolutely continuous value distribution can be
rewritten as integration against its canonical real-valued density. -/
theorem integral_eq_integral_realDensity_mul
    (D : ValueDistribution) (g : ℝ → ℝ)
    (hD : (D : Measure ℝ) ≪ volume) :
    ∫ value, g value ∂(D : Measure ℝ) =
      ∫ value, D.realDensity value * g value ∂volume := by
  simpa only [realDensity, smul_eq_mul] using
    (integral_rnDeriv_smul
      (μ := (D : Measure ℝ)) (ν := volume) (f := g) hD).symm

/-- A chosen real-valued density may replace the canonical representative in
an integral when the two agree almost everywhere. -/
theorem integral_eq_integral_density_mul
    (D : ValueDistribution) (f g : ℝ → ℝ)
    (hD : (D : Measure ℝ) ≪ volume)
    (hf : f =ᵐ[volume] D.realDensity) :
    ∫ value, g value ∂(D : Measure ℝ) =
      ∫ value, f value * g value ∂volume := by
  rw [D.integral_eq_integral_realDensity_mul g hD]
  apply integral_congr_ae
  filter_upwards [hf] with value hvalue
  rw [hvalue]

end ValueDistribution

end
