/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLib.Matching.Continuum.Stability
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# Matching identical points in two uniform populations

Both populations are uniform on `[0,1]`. Each agent prefers partners closer to their own point,
with utility minus absolute distance and outside-option utility `-1`. The identity assignment
is pointwise stable and induces a distributionally stable matching measure with the required
marginals. Its population measure is atomless.
-/

namespace MathEconLibExamples.Matching.Continuum

open MeasureTheory
open MathEconLib.Matching.Continuum

/-- Uniform population on the unit interval, represented as a measure on the real line. -/
noncomputable def population : ProbabilityMeasure ℝ :=
  ⟨volume.restrict (Set.Icc 0 1), ⟨by simp⟩⟩

instance : NoAtoms population.toMeasure :=
  inferInstanceAs (NoAtoms ((volume : Measure ℝ).restrict (Set.Icc 0 1)))

/-- Distance-based preferences with an outside option below the identity match. -/
def utilities : Utilities ℝ ℝ where
  left a b := -|a - b|
  right b a := -|b - a|
  outsideLeft _ := -1
  outsideRight _ := -1

theorem utilities_measurable : utilities.IsMeasurable :=
  ⟨(measurable_fst.sub measurable_snd).abs.neg, (measurable_fst.sub measurable_snd).abs.neg,
    measurable_const, measurable_const⟩

theorem identity_pointwiseStable : (MatchingMap.refl population).PointwiseStable utilities := by
  constructor
  · intro a
    norm_num [Utilities.IndividuallyRationalPair, MatchingMap.graph, utilities]
  · intro a b h
    exact (not_lt_of_ge (neg_nonpos.mpr (abs_nonneg (a - b))))
      (by simpa [MatchingMap.IsBlockingPair, utilities] using h.1)

/-- The distribution of pairs `(x,x)` for a uniform draw from the unit interval. -/
noncomputable def matching : MatchingMeasure population population :=
  (MatchingMap.refl population).toMatchingMeasure

/-- Apply the general bridge to the pointwise-stable continuum assignment. -/
theorem matching_distributionallyStable : matching.DistributionallyStable utilities :=
  identity_pointwiseStable.toMatchingMeasure utilities_measurable

end MathEconLibExamples.Matching.Continuum
