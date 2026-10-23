/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLib.Matching.Continuum
import MathEconLibExamples.Matching.Continuum

/-! Public API checks and semantic boundary cases for two-sided measured matching. -/

namespace MathEconLibTest.Matching.Continuum

open MeasureTheory
open MathEconLib.Matching.Continuum

example : MathEconLibExamples.Matching.Continuum.matching.DistributionallyStable
    MathEconLibExamples.Matching.Continuum.utilities :=
  MathEconLibExamples.Matching.Continuum.matching_distributionallyStable

open MathEconLibExamples.Matching.Continuum.FiniteBridge in
example : market.IsStableMatching
    (MatchingMap.refl population).toMeasurableEquiv.toEquiv.toPEquiv := identity_classicallyStable

#print axioms MathEconLibExamples.Matching.Continuum.FiniteBridge.identity_classicallyStable

open MathEconLibExamples.Matching.Continuum in
example : SplitMass.matching.DistributionallyStable
    ⟨fun _ _ ↦ 0, fun _ _ ↦ 0, fun _ ↦ 0, fun _ ↦ 0⟩ ∧
    ¬Nonempty (MatchingMap SplitMass.leftPopulation FiniteBridge.population) :=
  ⟨SplitMass.matching_distributionallyStable, SplitMass.no_matchingMap⟩

example (b : Fin 2) :
    MathEconLibExamples.Matching.Continuum.SplitMass.matching.toMeasure {(0, b)} =
      (2 : ENNReal)⁻¹ := MathEconLibExamples.Matching.Continuum.SplitMass.matching_mass b

#print axioms MathEconLibExamples.Matching.Continuum.SplitMass.matching_mass
#print axioms MathEconLibExamples.Matching.Continuum.SplitMass.matching_distributionallyStable
#print axioms MathEconLibExamples.Matching.Continuum.SplitMass.no_matchingMap

-- Only type 0 has population mass. Types 1 and 2 still matter for pointwise stability.
noncomputable def atomicPopulation : ProbabilityMeasure (Fin 3) :=
  ⟨Measure.dirac 0, inferInstance⟩

def nullSwap : MatchingMap atomicPopulation atomicPopulation where
  toMeasurableEquiv := {
    toEquiv := Equiv.swap 1 2
    measurable_toFun := Measurable.of_discrete
    measurable_invFun := Measurable.of_discrete }
  measurePreserving := ⟨Measurable.of_discrete, by
    simp [atomicPopulation, Measure.map_dirac Measurable.of_discrete, Equiv.swap_apply_def]⟩

def selfUtilities : Utilities (Fin 3) (Fin 3) where
  left a b := if a = b then 1 else 0
  right b a := if b = a then 1 else 0
  outsideLeft _ := -1
  outsideRight _ := -1

theorem nullSwap_blockingPair : nullSwap.IsBlockingPair selfUtilities 1 1 := by
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  norm_num [MatchingMap.IsBlockingPair, MatchingMap.symm, nullSwap, selfUtilities,
    Equiv.swap_apply_def, h12]

theorem nullSwap_not_pointwiseStable : ¬nullSwap.PointwiseStable selfUtilities :=
  fun h ↦ h.2 1 1 nullSwap_blockingPair

theorem nullSwap_toMeasure : nullSwap.toMatchingMeasure.toMeasure =
    Measure.dirac ((0, 0) : Fin 3 × Fin 3) := by
  simp [MatchingMap.graph, nullSwap, atomicPopulation,
    Measure.map_dirac Measurable.of_discrete, Equiv.swap_apply_def]

theorem nullSwap_distributionallyStable :
    nullSwap.toMatchingMeasure.DistributionallyStable selfUtilities := by
  rw [MatchingMeasure.DistributionallyStable, MatchingMeasure.IndividuallyRational,
    MatchingMeasure.Unblocked, nullSwap_toMeasure]
  simp [Measure.dirac_prod_dirac, ae_dirac_eq, Utilities.IndividuallyRationalPair,
    Utilities.Blocks, selfUtilities]

-- A matching can fail individual rationality even when there is no blocking cross-pair.
example : ¬nullSwap.toMatchingMeasure.DistributionallyStable
    { selfUtilities with outsideLeft := fun _ ↦ 2 } := by
  rw [MatchingMeasure.DistributionallyStable, MatchingMeasure.IndividuallyRational,
    nullSwap_toMeasure]
  simp [ae_dirac_eq, Utilities.IndividuallyRationalPair, selfUtilities]

-- Almost-everywhere equal maps induce the same matching measure.
example : nullSwap.toMatchingMeasure = (MatchingMap.refl atomicPopulation).toMatchingMeasure :=
  MatchingMap.toMatchingMeasure_congr (by
    change ∀ᵐ a ∂Measure.dirac (0 : Fin 3), nullSwap a = MatchingMap.refl atomicPopulation a
    simp [ae_dirac_eq, nullSwap, Equiv.swap_apply_def])

-- Positive-mass blocking must fail distributional stability.
noncomputable def twoPointPopulation : ProbabilityMeasure (Fin 3) :=
  ⟨(2 : ENNReal)⁻¹ • (Measure.dirac 1 + Measure.dirac 2), ⟨by
    norm_num [Measure.smul_apply, Measure.add_apply, ENNReal.inv_two_add_inv_two]⟩⟩

def crossUtilities : Utilities (Fin 3) (Fin 3) where
  left a b := if a = b then 0 else 1
  right b a := if b = a then 0 else 1
  outsideLeft _ := -1
  outsideRight _ := -1

theorem twoPoint_mass (i : Fin 3) :
    (MatchingMap.refl twoPointPopulation).toMatchingMeasure.toMeasure {(i, i)} =
      twoPointPopulation.toMeasure {i} := by
  rw [MatchingMap.toMeasure_toMatchingMeasure,
    Measure.map_apply (MatchingMap.refl twoPointPopulation).measurable_graph
      (measurableSet_singleton _)]
  congr 1
  ext a
  simp [MatchingMap.graph]

theorem positive_mass_blocking_not_stable :
    ¬(MatchingMap.refl twoPointPopulation).toMatchingMeasure.DistributionallyStable
      crossUtilities := by
  intro h
  have hz := (ae_iff_of_countable.mp h.2) (((1, 1), (2, 2)) : (Fin 3 × Fin 3) × (Fin 3 × Fin 3))
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have hmass : ((MatchingMap.refl twoPointPopulation).toMatchingMeasure.toMeasure.prod
      (MatchingMap.refl twoPointPopulation).toMatchingMeasure.toMeasure)
      {((1, 1), (2, 2))} ≠ 0 := by
    rw [← Set.singleton_prod_singleton,
      Measure.prod_prod, twoPoint_mass, twoPoint_mass]
    norm_num [twoPointPopulation, Measure.smul_apply, Measure.add_apply, h12, Ne.symm h12]
  exact hz hmass (by norm_num [Utilities.Blocks, crossUtilities, h12, Ne.symm h12])

#print axioms MatchingMap.toMatchingMeasure
#print axioms MatchingMap.toMatchingMeasure_symm
#print axioms MatchingMap.toMatchingMeasure_congr
#print axioms MatchingMap.PointwiseStable.toMatchingMeasure
#print axioms MatchingMap.PointwiseStable.symm
#print axioms MatchingMeasure.DistributionallyStable.symm
#print axioms MathEconLibExamples.Matching.Continuum.matching_distributionallyStable
#print axioms nullSwap_not_pointwiseStable
#print axioms nullSwap_distributionallyStable

end MathEconLibTest.Matching.Continuum
