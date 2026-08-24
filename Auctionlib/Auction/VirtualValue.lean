/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Auctionlib.Auction.Interim
public import Auctionlib.ValueDistribution.Ironing
public import Auctionlib.ValueDistribution.Regular
public import Mathlib.Probability.Density

/-!
# Virtual Values in Auctions

This file chooses one density representative for each bidder, lifts value-distribution virtual
values and their ironed versions to auctions, and defines the pointwise optimal virtual-surplus
bounds.
-/

@[expose] public section

open Function MeasureTheory ProbabilityTheory Set

noncomputable section

namespace Auction

variable {Ω : Type} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} (A : Auction Ω n)

/-- Chosen pointwise density representatives for all bidders. Agreement with the canonical real
density is required only almost everywhere on each bidder's support interval. -/
structure DensityFamily where
  f : Fin n → ℝ → ℝ
  measurable : ∀ i, Measurable (f i)
  continuousOn : ∀ i, ContinuousOn (f i) (A.interval i)
  pos : ∀ i, ∀ v ∈ A.interval i, 0 < f i v
  ae_eq : ∀ i, f i =ᵐ[volume.restrict (A.interval i)]
    (A.valueDistribution i).realDensity

/-- The canonical density of a bidder's value distribution is the real-valued PDF of that bidder's
type random variable. -/
lemma realDensity_valueDistribution (i : Fin n) :
    (A.valueDistribution i).realDensity =
      fun v => (pdf (A.θ i) ℙ volume v).toReal := by
  funext v
  rw [ValueDistribution.realDensity, A.toMeasure_valueDistribution]
  rfl

/-- A continuous chosen density is bounded above on its support interval. -/
lemma DensityFamily.exists_upperBound (ρ : A.DensityFamily) (i : Fin n) :
    ∃ C : ℝ, ∀ v ∈ A.interval i, ρ.f i v ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (ρ.continuousOn i)
  exact ⟨C, fun v hv =>
    (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC v hv)⟩

/-- A continuous strictly positive chosen density is bounded away from zero on its nonempty support
interval. -/
lemma DensityFamily.exists_pos_lowerBound [HasBoundedTypes A]
    (ρ : A.DensityFamily) (i : Fin n) :
    ∃ c : ℝ, 0 < c ∧ ∀ v ∈ A.interval i, c ≤ ρ.f i v := by
  obtain ⟨v, hv, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (A.θmin_le_θmax i)) (ρ.continuousOn i)
  exact ⟨ρ.f i v, ρ.pos i v hv, hmin⟩

/-- Bidder `i`'s virtual value for the chosen density representative. -/
noncomputable def virtualValue (ρ : A.DensityFamily) (i : Fin n) : ℝ → ℝ :=
  (A.valueDistribution i).virtualValue (ρ.f i)

lemma measurable_virtualValue (ρ : A.DensityFamily) (i : Fin n) :
    Measurable (A.virtualValue ρ i) :=
  (A.valueDistribution i).measurable_virtualValue (ρ.measurable i)

/-- Virtual value is continuous on the support interval when bidder types have densities. -/
lemma continuousOn_virtualValue [HasDensity A] (ρ : A.DensityFamily) (i : Fin n) :
    ContinuousOn (A.virtualValue ρ i) (A.interval i) := by
  letI : NoAtoms (A.valueDistribution i : Measure ℝ) :=
    noAtoms_of_absolutelyContinuous_volume (A.valueDistribution_absolutelyContinuous i)
  exact (A.valueDistribution i).continuousOn_virtualValue
    (ρ.continuousOn i) (ρ.pos i)

/-- Virtual value is bounded in absolute value on the support interval. -/
lemma exists_bound_virtualValue [HasDensity A] (ρ : A.DensityFamily) (i : Fin n) :
    ∃ C : ℝ, ∀ v ∈ A.interval i, |A.virtualValue ρ i v| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (A.continuousOn_virtualValue ρ i)
  exact ⟨C, fun v hv => by
    simpa [Real.norm_eq_abs] using hC v hv⟩

/-- A bidder's realized virtual value is integrable. -/
lemma integrable_virtualValue_comp_θ [HasBoundedTypes A] [HasDensity A]
    (ρ : A.DensityFamily) (i : Fin n) :
    Integrable (fun ω => A.virtualValue ρ i (A.θ i ω)) ℙ := by
  obtain ⟨C, hC⟩ := A.exists_bound_virtualValue ρ i
  exact A.integrable_comp_θ_of_bounded i (A.measurable_virtualValue ρ i) hC

/-- Realized virtual value times a valid allocation is integrable. -/
lemma integrable_virtualValue_mul_x [HasBoundedTypes A] [HasDensity A]
    [A.rules.HasValidAllocation] (ρ : A.DensityFamily) (i : Fin n) :
    Integrable
      (fun ω => A.virtualValue ρ i (A.θ i ω) * A.rules.x i (A.θ · ω)) ℙ := by
  have hx_meas : Measurable (fun ω => A.rules.x i (fun j => A.θ j ω)) :=
    (A.rules.x_measurable i).comp A.measurable_profile
  exact (A.integrable_virtualValue_comp_θ ρ i).mul_bdd
    hx_meas.aestronglyMeasurable (ae_of_all ℙ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (Mechanism.HasValidAllocation.x_range (M := A.rules) i _).1]
      exact (Mechanism.HasValidAllocation.x_range (M := A.rules) i _).2)

/-- All bidders' virtual values are regular on their support intervals. -/
def DensityFamily.IsRegular (ρ : A.DensityFamily) : Prop :=
  ∀ i, (A.valueDistribution i).IsRegular (ρ.f i) (A.θmin i) (A.θmax i)

/-- Bidder `i`'s ironed virtual value. -/
noncomputable def ironedVirtualValue (ρ : A.DensityFamily) (i : Fin n) : ℝ → ℝ :=
  (A.valueDistribution i).ironed (A.virtualValue ρ i)

/-- Ironed virtual value is globally monotone. -/
lemma monotone_ironedVirtualValue [HasBoundedTypes A] [HasDensity A]
    (ρ : A.DensityFamily) (i : Fin n) :
    Monotone (A.ironedVirtualValue ρ i) :=
  (A.valueDistribution i).monotone_ironed (A.virtualValue ρ i)
    (A.valueDistribution_isSupportedOnInterval i)
    (A.continuousOn_virtualValue ρ i)

lemma measurable_ironedVirtualValue [HasBoundedTypes A] [HasDensity A]
    (ρ : A.DensityFamily) (i : Fin n) :
    Measurable (A.ironedVirtualValue ρ i) :=
  (A.monotone_ironedVirtualValue ρ i).measurable

/-- Ironed virtual value is globally bounded by its endpoint quantile scores. -/
lemma exists_bound_ironedVirtualValue [HasBoundedTypes A] [HasDensity A]
    (ρ : A.DensityFamily) (i : Fin n) :
    ∃ C : ℝ, ∀ v, |A.ironedVirtualValue ρ i v| ≤ C := by
  let D := A.valueDistribution i
  let ψ := A.virtualValue ρ i
  let C := max |D.ironedQuantileScore ψ 0| |D.ironedQuantileScore ψ 1|
  refine ⟨C, fun v => ?_⟩
  obtain ⟨hlo, hhi⟩ := D.ironed_mem_Icc ψ
    (A.valueDistribution_isSupportedOnInterval i)
    (A.continuousOn_virtualValue ρ i) v
  rw [abs_le]
  exact ⟨(neg_le_neg (le_max_left _ _)).trans ((neg_abs_le _).trans hlo),
    hhi.trans ((le_abs_self _).trans (le_max_right _ _))⟩

/-- A bidder's realized ironed virtual value is integrable. -/
lemma integrable_ironedVirtualValue_comp_θ [HasBoundedTypes A] [HasDensity A]
    (ρ : A.DensityFamily) (i : Fin n) :
    Integrable (fun ω => A.ironedVirtualValue ρ i (A.θ i ω)) ℙ := by
  obtain ⟨C, hC⟩ := A.exists_bound_ironedVirtualValue ρ i
  apply Integrable.of_bound
    ((A.measurable_ironedVirtualValue ρ i).comp
      (A.θ_measurable i)).aestronglyMeasurable C
  exact ae_of_all ℙ fun ω => by
    rw [Real.norm_eq_abs]
    exact hC _

/-- Realized ironed virtual value times a valid allocation is integrable. -/
lemma integrable_ironedVirtualValue_mul_x [HasBoundedTypes A] [HasDensity A]
    [A.rules.HasValidAllocation] (ρ : A.DensityFamily) (i : Fin n) :
    Integrable
      (fun ω => A.ironedVirtualValue ρ i (A.θ i ω) * A.rules.x i (A.θ · ω)) ℙ := by
  have hx_meas : Measurable (fun ω => A.rules.x i (fun j => A.θ j ω)) :=
    (A.rules.x_measurable i).comp A.measurable_profile
  exact (A.integrable_ironedVirtualValue_comp_θ ρ i).mul_bdd
    hx_meas.aestronglyMeasurable (ae_of_all ℙ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (Mechanism.HasValidAllocation.x_range (M := A.rules) i _).1]
      exact (Mechanism.HasValidAllocation.x_range (M := A.rules) i _).2)

/-- In a regular environment, ironing leaves virtual value unchanged in the interior of the support
interval. -/
lemma ironedVirtualValue_eq_virtualValue_of_regular
    [HasBoundedTypes A] [HasDensity A] {ρ : A.DensityFamily}
    (hreg : ρ.IsRegular) (i : Fin n) {v : ℝ}
    (hv : v ∈ Ioo (A.θmin i) (A.θmax i)) :
    A.ironedVirtualValue ρ i v = A.virtualValue ρ i v :=
  (A.valueDistribution i).ironed_virtualValue_eq_of_isRegular (ρ.f i)
    (A.valueDistribution_isSupportedOnInterval i)
    (A.valueDistribution_absolutelyContinuous i) (ρ.ae_eq i)
    (ρ.continuousOn i) (ρ.pos i) (hreg i) hv

section NeZero

variable [NeZero n]

/-- The pointwise optimal raw virtual surplus over feasible single-unit allocations. -/
noncomputable def optimalVirtualSurplus (ρ : A.DensityFamily) (θ : Fin n → ℝ) : ℝ :=
  max 0 (Finset.univ.sup' Finset.univ_nonempty fun i => A.virtualValue ρ i (θ i))

/-- The pointwise optimal ironed virtual surplus over feasible single-unit allocations. -/
noncomputable def ironedOptimalVirtualSurplus
    (ρ : A.DensityFamily) (θ : Fin n → ℝ) : ℝ :=
  max 0 (Finset.univ.sup' Finset.univ_nonempty fun i => A.ironedVirtualValue ρ i (θ i))

lemma optimalVirtualSurplus_nonneg (ρ : A.DensityFamily) (θ : Fin n → ℝ) :
    0 ≤ A.optimalVirtualSurplus ρ θ :=
  le_max_left _ _

lemma ironedOptimalVirtualSurplus_nonneg (ρ : A.DensityFamily) (θ : Fin n → ℝ) :
    0 ≤ A.ironedOptimalVirtualSurplus ρ θ :=
  le_max_left _ _

/-- Every feasible allocation's raw virtual surplus is bounded by the pointwise optimum. -/
lemma sum_virtualValue_mul_x_le [A.rules.IsFeasible]
    (ρ : A.DensityFamily) (θ : Fin n → ℝ) :
    ∑ i, A.virtualValue ρ i (θ i) * A.rules.x i θ ≤
      A.optimalVirtualSurplus ρ θ :=
  Mechanism.sum_score_mul_x_le A.rules (A.virtualValue ρ) θ

/-- Every feasible allocation's ironed virtual surplus is bounded by the pointwise optimum. -/
lemma sum_ironedVirtualValue_mul_x_le [A.rules.IsFeasible]
    (ρ : A.DensityFamily) (θ : Fin n → ℝ) :
    ∑ i, A.ironedVirtualValue ρ i (θ i) * A.rules.x i θ ≤
      A.ironedOptimalVirtualSurplus ρ θ :=
  Mechanism.sum_score_mul_x_le A.rules (A.ironedVirtualValue ρ) θ

lemma measurable_optimalVirtualSurplus (ρ : A.DensityFamily) :
    Measurable (A.optimalVirtualSurplus ρ) := by
  have h_sup : Measurable
      (Finset.univ.sup' Finset.univ_nonempty
        (fun i (θ : Fin n → ℝ) => A.virtualValue ρ i (θ i))) :=
    Finset.measurable_sup' Finset.univ_nonempty fun i _ =>
      (A.measurable_virtualValue ρ i).comp (measurable_pi_apply i)
  simpa only [optimalVirtualSurplus, Finset.sup'_apply] using measurable_const.max h_sup

lemma measurable_ironedOptimalVirtualSurplus [HasBoundedTypes A] [HasDensity A]
    (ρ : A.DensityFamily) :
    Measurable (A.ironedOptimalVirtualSurplus ρ) := by
  have h_sup : Measurable
      (Finset.univ.sup' Finset.univ_nonempty
        (fun i (θ : Fin n → ℝ) => A.ironedVirtualValue ρ i (θ i))) :=
    Finset.measurable_sup' Finset.univ_nonempty fun i _ =>
      (A.measurable_ironedVirtualValue ρ i).comp (measurable_pi_apply i)
  simpa only [ironedOptimalVirtualSurplus, Finset.sup'_apply] using measurable_const.max h_sup

/-- The pointwise optimal raw virtual surplus is integrable at the realized type profile. -/
lemma integrable_optimalVirtualSurplus_comp_profile
    [HasBoundedTypes A] [HasDensity A] (ρ : A.DensityFamily) :
    Integrable (fun ω => A.optimalVirtualSurplus ρ (A.θ · ω)) ℙ := by
  have h_sup : Integrable
      (Finset.univ.sup' Finset.univ_nonempty
        (fun i (ω : Ω) => A.virtualValue ρ i (A.θ i ω))) ℙ :=
    Finset.sup'_induction (p := fun g : Ω → ℝ => Integrable g ℙ)
      Finset.univ_nonempty (fun i ω => A.virtualValue ρ i (A.θ i ω))
      (fun _ hf _ hg => hf.sup hg)
      (fun i _ => A.integrable_virtualValue_comp_θ ρ i)
  simpa only [optimalVirtualSurplus, Finset.sup'_apply, Pi.sup_def] using
    (integrable_const (0 : ℝ)).sup h_sup

/-- The pointwise optimal ironed virtual surplus is integrable at the realized type profile. -/
lemma integrable_ironedOptimalVirtualSurplus_comp_profile
    [HasBoundedTypes A] [HasDensity A] (ρ : A.DensityFamily) :
    Integrable (fun ω => A.ironedOptimalVirtualSurplus ρ (A.θ · ω)) ℙ := by
  have h_sup : Integrable
      (Finset.univ.sup' Finset.univ_nonempty
        (fun i (ω : Ω) => A.ironedVirtualValue ρ i (A.θ i ω))) ℙ :=
    Finset.sup'_induction (p := fun g : Ω → ℝ => Integrable g ℙ)
      Finset.univ_nonempty (fun i ω => A.ironedVirtualValue ρ i (A.θ i ω))
      (fun _ hf _ hg => hf.sup hg)
      (fun i _ => A.integrable_ironedVirtualValue_comp_θ ρ i)
  simpa only [ironedOptimalVirtualSurplus, Finset.sup'_apply, Pi.sup_def] using
    (integrable_const (0 : ℝ)).sup h_sup

/-- In a regular environment, the pointwise raw and ironed optima coincide at interior type
profiles. -/
lemma ironedOptimalVirtualSurplus_eq_of_regular
    [HasBoundedTypes A] [HasDensity A] {ρ : A.DensityFamily}
    (hreg : ρ.IsRegular) {θ : Fin n → ℝ}
    (hθ : ∀ i, θ i ∈ Ioo (A.θmin i) (A.θmax i)) :
    A.ironedOptimalVirtualSurplus ρ θ = A.optimalVirtualSurplus ρ θ := by
  unfold ironedOptimalVirtualSurplus optimalVirtualSurplus
  congr 1
  apply Finset.sup'_congr Finset.univ_nonempty rfl
  intro i _
  exact A.ironedVirtualValue_eq_virtualValue_of_regular hreg i (hθ i)

omit [NeZero n] in
/-- With bounded absolutely continuous types, every bidder's realized type lies in the interior of
its support interval almost surely. -/
lemma ae_θ_mem_Ioo [HasBoundedTypes A] [HasDensity A] :
    ∀ᵐ ω ∂ℙ, ∀ i, A.θ i ω ∈ Ioo (A.θmin i) (A.θmax i) := by
  apply ae_all_iff.mpr
  intro i
  let D := A.valueDistribution i
  have hsupport : ∀ᵐ v ∂(D : Measure ℝ), v ∈ A.interval i :=
    A.valueDistribution_isSupportedOnInterval i
  have hD : (D : Measure ℝ) ≪ volume :=
    A.valueDistribution_absolutelyContinuous i
  have hlower : (D : Measure ℝ) {A.θmin i} = 0 := hD (by simp)
  have hupper : (D : Measure ℝ) {A.θmax i} = 0 := hD (by simp)
  have hlower_ae : ∀ᵐ v ∂(D : Measure ℝ), v ≠ A.θmin i := by
    simpa [ae_iff] using hlower
  have hupper_ae : ∀ᵐ v ∂(D : Measure ℝ), v ≠ A.θmax i := by
    simpa [ae_iff] using hupper
  have hinterior : ∀ᵐ v ∂(D : Measure ℝ),
      v ∈ Ioo (A.θmin i) (A.θmax i) := by
    filter_upwards [hsupport, hlower_ae, hupper_ae] with v hv hlo hhi
    exact ⟨lt_of_le_of_ne hv.1 hlo.symm, lt_of_le_of_ne hv.2 hhi⟩
  rw [A.toMeasure_valueDistribution] at hinterior
  exact (ae_map_iff (p := fun v => v ∈ Ioo (A.θmin i) (A.θmax i))
    (A.θ_measurable i).aemeasurable measurableSet_Ioo).mp hinterior

/-- In a regular environment, expected raw and ironed pointwise optimal virtual surplus agree. -/
theorem integral_ironedOptimalVirtualSurplus_eq_of_regular
    [HasBoundedTypes A] [HasDensity A] {ρ : A.DensityFamily}
    (hreg : ρ.IsRegular) :
    𝔼[fun ω => A.ironedOptimalVirtualSurplus ρ (A.θ · ω)] =
      𝔼[fun ω => A.optimalVirtualSurplus ρ (A.θ · ω)] := by
  apply integral_congr_ae
  filter_upwards [A.ae_θ_mem_Ioo] with ω hω
  exact A.ironedOptimalVirtualSurplus_eq_of_regular hreg hω

end NeZero

end Auction

end
