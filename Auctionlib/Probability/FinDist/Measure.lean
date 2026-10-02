/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Auctionlib.Probability.FinDist.Expect
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Finite distributions and probability measures

A finite distribution determines a probability mass function and a probability measure. Converting
a probability mass function on a finite type to real-valued masses and back recovers the original
function. Finite expectations agree with Bochner integrals on discrete measurable spaces.

## Main definitions

* `FinDist.toPMF`, `FinDist.ofPMF`: Finite distributions as probability mass functions and
  probability mass functions on finite types as finite distributions.
* `FinDist.toMeasure`: The probability measure with the given masses.

## Main statements

* `FinDist.toPMF_ofPMF`: Converting a probability mass function to real-valued masses and back
  preserves it.
* `FinDist.integrable_toMeasure`: Functions on finite discrete spaces are integrable.
* `FinDist.expect_eq_integral`: Finite expectations agree with integrals.

## Tags

probability, finite distributions, probability measures, expectation
-/

@[expose] public noncomputable section

open BigOperators MeasureTheory

namespace Auctionlib.Probability.FinDist

/-- The probability mass function whose masses are those of the finite distribution. -/
noncomputable def toPMF {α : Type*} [Fintype α] (d : FinDist α) : PMF α where
  val a := ENNReal.ofReal (d.pmf a)
  property := by
    have hsum : HasSum (fun a => ENNReal.ofReal (d.pmf a)) (∑ a, ENNReal.ofReal (d.pmf a)) :=
      hasSum_fintype _
    convert hsum using 1
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => d.nonneg a), d.sum_one]
    simp

/-- A probability mass function on a finite type, expressed as real-valued probability masses. -/
noncomputable def ofPMF {α : Type*} [Fintype α] (p : PMF α) : FinDist α :=
  ⟨fun a ↦ (p a).toReal, fun _ ↦ ENNReal.toReal_nonneg, by
    have hmass_ne_top : ∀ a : α, (p a) ≠ ⊤ :=
      fun a => ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.coe_le_one p a)
    rw [← ENNReal.toReal_sum (fun a _ => hmass_ne_top a)]
    have hsum : (∑ a : α, p a) = 1 := by
      have htsum := p.tsum_coe
      rwa [tsum_fintype] at htsum
    rw [hsum]
    simp⟩

/-- `toPMF` is a left inverse of `ofPMF`. -/
lemma toPMF_ofPMF {α : Type*} [Fintype α] (p : PMF α) :
    FinDist.toPMF (FinDist.ofPMF p) = p := by
  ext a
  simp only [toPMF, ofPMF]
  exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.coe_le_one p a))

variable {α : Type*} [Fintype α] [MeasurableSpace α]

/-- The probability measure assigning each measurable event its total probability mass. -/
def toMeasure (d : FinDist α) : Measure α := d.toPMF.toMeasure

/-- The measure induced by a finite distribution is a probability measure. -/
instance (d : FinDist α) : IsProbabilityMeasure d.toMeasure :=
  PMF.toMeasure.isProbabilityMeasure d.toPMF

/-- Every function from a finite discrete space into a normed additive group is integrable. -/
lemma integrable_toMeasure [MeasurableSingletonClass α] {V : Type*} [NormedAddCommGroup V]
    (d : FinDist α) (f : α → V) :
    Integrable f d.toMeasure := Integrable.of_finite

/-- The integral with respect to a finite distribution is its finite expectation. -/
lemma expect_eq_integral [MeasurableSingletonClass α] {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V] (d : FinDist α) (f : α → V) :
    d.expect f = ∫ a, f a ∂d.toMeasure := by
  simp only [FinDist.expect, toMeasure]
  rw [PMF.integral_eq_sum]
  congr 1
  ext a
  congr 1
  exact (ENNReal.toReal_ofReal (d.nonneg a)).symm

end Auctionlib.Probability.FinDist
