/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Matching.Continuum
public import Mathlib.MeasureTheory.Group.AddCircle

/-!
# Product-null blocking involving every agent

Scott Duke Kominers' regression example: both populations are the uniform unit circle, matched
by the identity. Every agent strictly prefers their antipode to their assigned partner. The graph
of antipodal blocking pairs has product measure zero, so the matching is distributionally stable.
Nevertheless, arbitrary full-measure subsets on both sides still contain a blocking pair.
The spike utilities are measurable; they fail the open strict-comparison condition discussed in
`docs/MatchingArchitecture.md`.
-/

@[expose] public section

namespace MathEconLibTest.Matching.Continuum.Antipodal

open MeasureTheory MeasureTheory.Measure
open MathEconLib.Matching.Continuum

/-- Haar probability on the circle of circumference one. -/
noncomputable def population : ProbabilityMeasure UnitAddCircle := ⟨volume, ⟨by simp⟩⟩

instance : NullSingletonClass population.toMeasure := by
  constructor
  intro x
  change volume {x} = 0
  rw [← Metric.closedBall_zero (x := x), AddCircle.volume_closedBall]
  norm_num

/-- Rotation through half a circle. -/
noncomputable def antipode (x : UnitAddCircle) : UnitAddCircle := x + ((1 / 2 : ℝ) : UnitAddCircle)

theorem antipode_involutive (x : UnitAddCircle) : antipode (antipode x) = x := by
  norm_num [antipode, add_assoc, ← AddCircle.coe_add]

theorem antipode_ne (x : UnitAddCircle) : antipode x ≠ x := by
  norm_num [antipode, AddCircle.coe_eq_zero_iff_of_mem_Ico
    (by norm_num : (1 / 2 : ℝ) ∈ Set.Ico 0 1)]

theorem antipode_measurePreserving :
    MeasurePreserving antipode population.toMeasure population.toMeasure :=
  measurePreserving_add_right volume _

/-- Utility one only at the antipode, zero at other partners, and minus one when single. -/
noncomputable def utilities : PartnerUtilities UnitAddCircle UnitAddCircle := by
  classical
  exact ⟨fun a b ↦ if b = antipode a then 1 else 0,
    fun b a ↦ if a = antipode b then 1 else 0, fun _ ↦ -1, fun _ ↦ -1⟩

theorem utilities_measurable : utilities.IsMeasurable := by
  classical
  exact ⟨Measurable.ite (measurableSet_eq_fun measurable_snd (measurable_fst.add_const _))
      measurable_const measurable_const,
    Measurable.ite (measurableSet_eq_fun measurable_snd (measurable_fst.add_const _))
      measurable_const measurable_const, measurable_const, measurable_const⟩

/-- Every agent participates in a blocking pair. -/
theorem antipode_blockingPair (a : UnitAddCircle) :
    (MatchingMap.refl population).IsBlockingPair utilities a (antipode a) := by
  simp [MatchingMap.isBlockingPair_iff, MatchingMap.symm, MatchingMap.refl, utilities,
    antipode_ne, antipode_involutive, Ne.symm (antipode_ne a)]

/-- Independent circle draws almost surely miss the graph of the antipodal map. -/
theorem ae_not_antipode :
    ∀ᵐ z ∂population.toMeasure.prod population.toMeasure, z.2 ≠ antipode z.1 :=
  (ae_prod_iff_ae_ae
    (measurableSet_eq_fun measurable_snd (measurable_fst.add_const _)).compl).mpr
    (Filter.Eventually.of_forall fun a ↦ population.toMeasure.ae_ne (antipode a))

/-- The identity matching nevertheless satisfies product-almost-everywhere stability. -/
theorem identity_distributionallyStable :
    (MatchingMap.refl population).toMatchingMeasure.DistributionallyStable utilities := by
  constructor
  · refine MatchingMap.IndividuallyRational.toMatchingMeasure ?_ utilities_measurable
    intro a
    simp [PartnerUtilities.IndividuallyRationalPair, MatchingMap.graphMap, utilities,
      Ne.symm (antipode_ne a)]
  · change ∀ᵐ z ∂(population.toMeasure.map (MatchingMap.refl population).graphMap).prod
      (population.toMeasure.map (MatchingMap.refl population).graphMap),
      ¬utilities.Blocks z.1 z.2
    rw [Measure.map_prod_map _ _ (MatchingMap.refl population).measurable_graphMap
      (MatchingMap.refl population).measurable_graphMap]
    refine (ae_map_iff
      ((MatchingMap.refl population).measurable_graphMap.prodMap
        (MatchingMap.refl population).measurable_graphMap).aemeasurable
      utilities_measurable.measurableSet_blocks.compl).mpr ?_
    filter_upwards [ae_not_antipode] with z hz
    simp [PartnerUtilities.Blocks, MatchingMap.graphMap, utilities, hz,
      Ne.symm (antipode_ne z.1)]

/-- Removing arbitrary null sets of agents on either side cannot eliminate blocking.
Full measure in the a.e. filter suffices, without measurability of the retained sets. -/
theorem exists_blockingPair_on_full_measure_sets {s t : Set UnitAddCircle}
    (hs : ∀ᵐ a ∂population.toMeasure, a ∈ s) (ht : ∀ᵐ b ∂population.toMeasure, b ∈ t) :
    ∃ a ∈ s, ∃ b ∈ t, (MatchingMap.refl population).IsBlockingPair utilities a b := by
  obtain ⟨a, ha, hb⟩ := (hs.and (antipode_measurePreserving.quasiMeasurePreserving.ae ht)).exists
  exact ⟨a, ha, antipode a, hb, antipode_blockingPair a⟩

#print axioms utilities_measurable
#print axioms antipode_blockingPair
#print axioms identity_distributionallyStable
#print axioms exists_blockingPair_on_full_measure_sets

end MathEconLibTest.Matching.Continuum.Antipodal
