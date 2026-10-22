/-
Copyright (c) 2026 Ruiz Chen, Jujian Zhang, Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiz Chen, Jujian Zhang, Scott Duke Kominers
-/
module

public import MathEconLib.Auction.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.CDF

/-! # Auction Environment Typeclasses (Section 3a) -/

namespace MathEconLib

@[expose] public section

open MeasureTheory ProbabilityTheory Set

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} [NeZero n]

namespace Auction

/-! ### Composable typeclasses -/

/-- Types are mutually independent (the "I" in IPV). -/
class HasIndependentTypes (A : Auction Ω n) : Prop where
  θ_indep : iIndepFun A.θ ℙ

/-- All bidders share the same type distribution and bounds (symmetric bidders). -/
class HasIdenticalTypes (A : Auction Ω n) : Prop where
  θ_identical : ∀ i j, IdentDistrib (A.θ i) (A.θ j) ℙ ℙ
  θmin_eq : ∀ i, A.θmin i = A.θmin 0
  θmax_eq : ∀ i, A.θmax i = A.θmax 0

/-- Each bidder's type lies in the declared interval. -/
class HasBoundedTypes (A : Auction Ω n) : Prop where
  θ_in : ∀ i (ω : Ω), A.θ i ω ∈ Icc (A.θmin i) (A.θmax i)

/-- Each bidder's type distribution has a density w.r.t. Lebesgue measure. -/
class HasDensity (A : Auction Ω n) : Prop where
  θ_hasPDF : ∀ i, HasPDF (A.θ i) ℙ volume

/-- The type distribution is atomless. -/
class HasAtomlessTypes (A : Auction Ω n) : Prop where
  θ_noAtoms : NoAtoms (Measure.map (A.θ 0) ℙ)

/-! ### IsSymmetricIPV (convenience bundle) -/

/-- Symmetric IPV: all five properties bundled. -/
class IsSymmetricIPV (A : Auction Ω n) : Prop extends
    HasIndependentTypes A, HasIdenticalTypes A, HasBoundedTypes A,
    HasDensity A, HasAtomlessTypes A

/-! ### Common type bounds (needs HasIdenticalTypes) -/

variable (A : Auction Ω n)

noncomputable def lowestType [HasIdenticalTypes A] : ℝ := A.θmin 0

@[simp] lemma θmin_eq_lowestType [HasIdenticalTypes A] (i) :
    A.θmin i = A.lowestType := by
  rw [HasIdenticalTypes.θmin_eq]; rfl

noncomputable def highestType [HasIdenticalTypes A] : ℝ := A.θmax 0

@[simp] lemma θmax_eq_highestType [HasIdenticalTypes A] (i) :
    A.θmax i = A.highestType := by
  rw [HasIdenticalTypes.θmax_eq]; rfl

/-! ### Common CDF (needs HasIdenticalTypes) -/

instance isProbabilityMeasure_map_θ₀ :
    IsProbabilityMeasure (Measure.map (A.θ 0) ℙ) :=
  Measure.isProbabilityMeasure_map (A.θ_measurable 0).aemeasurable

/-- The common CDF: `F(s) = cdf(Measure.map (θ₀) ℙ)(s)`. -/
noncomputable abbrev commonCDF [HasIdenticalTypes A] (s : ℝ) : ℝ :=
  ProbabilityTheory.cdf (Measure.map (A.θ 0) ℙ) s

set_option linter.unusedSectionVars false in
lemma commonCDF_nonneg [HasIdenticalTypes A] (s : ℝ) :
    0 ≤ A.commonCDF s := cdf_nonneg _ s

set_option linter.unusedSectionVars false in
lemma commonCDF_le_one [HasIdenticalTypes A] (s : ℝ) :
    A.commonCDF s ≤ 1 := cdf_le_one _ s

set_option linter.unusedSectionVars false in
lemma commonCDF_mono [HasIdenticalTypes A] :
    Monotone A.commonCDF := monotone_cdf _

lemma commonCDF_measurable [HasIdenticalTypes A] :
    Measurable A.commonCDF := (A.commonCDF_mono).measurable

lemma commonCDF_eq [HasIdenticalTypes A] (s : ℝ) :
    A.commonCDF s = Measure.real ℙ (A.θ 0 ⁻¹' Iic s) := by
  simp [ProbabilityTheory.cdf_eq_real, Measure.real,
    Measure.map_apply (A.θ_measurable 0) measurableSet_Iic]

/-! ### CDF boundary values (needs HasIdenticalTypes + HasBoundedTypes + HasAtomlessTypes) -/

@[simp] lemma commonCDF_lowestType
    [HasIdenticalTypes A] [HasBoundedTypes A] [HasAtomlessTypes A] :
    A.commonCDF A.lowestType = 0 := by
  rw [A.commonCDF_eq, Measure.real]
  suffices h : ℙ (A.θ 0 ⁻¹' Iic A.lowestType) = 0 by simp [h]
  have heq : A.θ 0 ⁻¹' Iic A.lowestType = A.θ 0 ⁻¹' {A.lowestType} := by
    ext ω
    simp only [mem_preimage, mem_Iic, mem_singleton_iff]
    constructor
    · intro h
      have hθ := HasBoundedTypes.θ_in (A := A) 0 ω
      rw [A.θmin_eq_lowestType] at hθ
      exact le_antisymm h hθ.1
    · intro h; exact le_of_eq h
  rw [heq, ← Measure.map_apply (A.θ_measurable 0) (measurableSet_singleton _)]
  have : NoAtoms (Measure.map (A.θ 0) ℙ) := HasAtomlessTypes.θ_noAtoms
  exact measure_singleton _

@[simp] lemma commonCDF_highestType
    [HasIdenticalTypes A] [HasBoundedTypes A] :
    A.commonCDF A.highestType = 1 := by
  rw [A.commonCDF_eq]
  have huniv : A.θ 0 ⁻¹' Iic A.highestType = Set.univ := by
    ext ω
    simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
    have hθ := HasBoundedTypes.θ_in (A := A) 0 ω
    rw [A.θmax_eq_highestType] at hθ
    exact hθ.2
  simp [huniv]

/-! ### Lowest-type normalization and revenue -/

/-- Zero lowest-type utility: the participation constraint binds at the lowest
type, so the lowest type earns exactly zero. This is the normalization used by
revenue equivalence; the actual participation predicates are the `InterimIR`
family. Matches `SingleParameterProblem.HasZeroLowestTypeUtility`. -/
class HasZeroLowestTypeUtility [HasIdenticalTypes A] : Prop where
  zeroLowestTypeUtility : ∀ i, A.U i A.lowestType = 0

/-- Expected total revenue. -/
noncomputable def expectedRevenue : ℝ :=
  𝔼[fun ω => ∑ i : Fin n, A.p i (A.θ i ω)]

end Auction

end

end MathEconLib
