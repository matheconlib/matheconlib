/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Matching.Continuum
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.Probability.Distributions.Uniform

/-!
# Matching identical points in two uniform populations

Both populations are uniform on `[0,1]`. Each agent prefers partners closer to their own point,
with utility minus absolute distance and outside-option utility `-1`. The identity assignment
is pointwise stable and induces a distributionally stable matching measure with the required
marginals. Its population measure is atomless. A separate two-type example applies the bridge
between utility-based pointwise stability and classical marriage stability. A split-mass example
shows that matching measures need not come from bijections between the supplied type spaces.
-/

@[expose] public section

namespace MathEconLibExamples.Matching.Continuum

open MeasureTheory
open MathEconLib.Matching.Continuum

/-- Uniform population on the unit interval, represented as a measure on the real line. -/
noncomputable def population : ProbabilityMeasure ℝ :=
  ⟨volume.restrict (Set.Icc 0 1), ⟨by simp⟩⟩

instance : NullSingletonClass population.toMeasure :=
  inferInstanceAs (NullSingletonClass ((volume : Measure ℝ).restrict (Set.Icc 0 1)))

/-- Distance-based preferences with an outside option below the identity match. -/
def utilities : PartnerUtilities ℝ ℝ where
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
    norm_num [PartnerUtilities.IndividuallyRationalPair, MatchingMap.graphMap, utilities]
  · intro a b h
    have hab := (MatchingMap.isBlockingPair_iff _ _ _ _).mp h
    exact (not_lt_of_ge (neg_nonpos.mpr (abs_nonneg (a - b))))
      (by simpa [utilities] using hab.1)

/-- The distribution of pairs `(x,x)` for a uniform draw from the unit interval. -/
noncomputable def matching : MatchingMeasure population population :=
  (MatchingMap.refl population).toMatchingMeasure

/-- Apply the general bridge to the pointwise-stable continuum assignment. -/
theorem matching_distributionallyStable : matching.DistributionallyStable utilities :=
  identity_pointwiseStable.toMatchingMeasure utilities_measurable

namespace FiniteBridge

open MathEconLib.Matching

/-- Equal population weights on two types. -/
noncomputable def population : ProbabilityMeasure (Fin 2) :=
  ⟨Measure.uniformOfFinset (Finset.univ : Finset (Fin 2)),
    ⟨by norm_num [Measure.uniformOfFinset_apply, ENNReal.div_self]⟩⟩

/-- Both sides rank type 1 above type 0 and either partner above remaining unmatched. -/
def market : MarriageMarket (Fin 2) (Fin 2) :=
  ⟨fun _ ↦ inferInstanceAs (LinearOrder (WithBot (Fin 2))),
    fun _ ↦ inferInstanceAs (LinearOrder (WithBot (Fin 2)))⟩

/-- Partner ranks as utilities, with outside-option utility `-1`. -/
def utilities : PartnerUtilities (Fin 2) (Fin 2) :=
  ⟨fun _ b ↦ b.val, fun _ a ↦ a.val, fun _ ↦ -1, fun _ ↦ -1⟩

/-- The utility and classical descriptions give exactly the same partner comparisons. -/
theorem represents : market.toPartnerComparisons = utilities.toPartnerComparisons := by
  ext a x y <;> fin_cases x <;> fin_cases y <;>
    norm_num [market, MarriageMarket.toPartnerComparisons, MarriageMarket.ltM, MarriageMarket.ltW,
      PartnerUtilities.toPartnerComparisons, utilities] <;> decide +revert

/-- The identity assignment has no mutually profitable cross-match. -/
theorem identity_pointwiseStable : (MatchingMap.refl population).PointwiseStable utilities := by
  constructor
  · intro a
    constructor <;> exact le_trans (by norm_num [utilities]) (Nat.cast_nonneg _)
  · intro a b h
    exact lt_asymm h.1 h.2

/-- Apply the general bridge to obtain classical stability of the identity assignment. -/
theorem identity_classicallyStable :
    market.IsStableMatching (MatchingMap.refl population).toMeasurableEquiv.toEquiv.toPEquiv :=
  ((MatchingMap.refl population).pointwiseStable_iff_classical utilities market represents).mp
    identity_pointwiseStable

end FiniteBridge

namespace SplitMass

/-- One left type with total population mass one. -/
noncomputable def leftPopulation : ProbabilityMeasure (Fin 1) :=
  ⟨Measure.uniformOfFinset (Finset.univ : Finset (Fin 1)),
    ⟨by norm_num [Measure.uniformOfFinset_apply, ENNReal.div_self]⟩⟩

/-- Split the left type's mass equally between the two right types. -/
noncomputable def matching : MatchingMeasure leftPopulation FiniteBridge.population :=
  MatchingMeasure.product leftPopulation FiniteBridge.population

/-- Each of the two possible type pairs receives half the population mass. -/
theorem matching_mass (b : Fin 2) : matching.toMeasure {(0, b)} = (2 : ENNReal)⁻¹ := by
  change (leftPopulation.toMeasure.prod FiniteBridge.population.toMeasure) {(0, b)} = _
  rw [← Set.singleton_prod_singleton, Measure.prod_prod]
  simp [leftPopulation, FiniteBridge.population]

/-- Indifferent agents with zero outside options make this split assignment stable. -/
theorem matching_distributionallyStable : matching.DistributionallyStable
    ⟨fun _ _ ↦ 0, fun _ _ ↦ 0, fun _ ↦ 0, fun _ ↦ 0⟩ := by
  simp [MatchingMeasure.DistributionallyStable, MatchingMeasure.IndividuallyRational,
    MatchingMeasure.Unblocked, PartnerUtilities.IndividuallyRationalPair, PartnerUtilities.Blocks]

/-- There is no bijection from one left type to two right types. -/
theorem no_matchingMap : ¬Nonempty (MatchingMap leftPopulation FiniteBridge.population) := by
  rintro ⟨f⟩
  have h := Fintype.card_congr f.toMeasurableEquiv.toEquiv
  norm_num at h

end SplitMass

end MathEconLibExamples.Matching.Continuum
