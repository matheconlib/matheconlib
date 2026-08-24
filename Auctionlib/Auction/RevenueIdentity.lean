/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Auctionlib.Auction.VirtualValue

/-!
# Revenue Identities and Myerson Bounds

This file lifts the single-agent virtual-value revenue identity to auctions. Under Bayesian
incentive compatibility, expected revenue is expected virtual surplus up to the bidders'
lowest-type utilities. Individual rationality gives the corresponding raw and ironed Myerson bounds.
-/

@[expose] public section

open Function MeasureTheory ProbabilityTheory Set

noncomputable section

namespace Auction

variable {Ω : Type} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} (A : Auction Ω n)

/-- Under BIC and bounded types, a measurable interim payment evaluated at the realized type is
integrable. -/
lemma integrable_p_comp_θ [HasBoundedTypes A] [A.rules.HasValidAllocation] [A.BIC]
    (i : Fin n) (hp : Measurable (A.p i)) :
    Integrable (fun ω => A.p i (A.θ i ω)) ℙ := by
  let C := max |A.θmin i| |A.θmax i| + |A.U i (A.θmin i)| +
    (A.θmax i - A.θmin i)
  apply Integrable.of_bound
    ((hp.comp (A.θ_measurable i)).aestronglyMeasurable) C
  filter_upwards with ω
  have hθ := HasBoundedTypes.θ_in (A := A) i ω
  have hq := A.q_range i (A.θ i ω)
  have hmul : |A.θ i ω * A.q i (A.θ i ω)| ≤
      max |A.θmin i| |A.θmax i| := by
    calc
      |A.θ i ω * A.q i (A.θ i ω)| =
          |A.θ i ω| * A.q i (A.θ i ω) := by
        rw [abs_mul, abs_of_nonneg hq.1]
      _ ≤ |A.θ i ω| * 1 :=
        mul_le_mul_of_nonneg_left hq.2 (abs_nonneg _)
      _ = |A.θ i ω| := mul_one _
      _ ≤ max |A.θmin i| |A.θmax i| :=
        abs_le_max_abs_abs hθ.1 hθ.2
  have hintegral :
      |∫ s in A.θmin i..A.θ i ω, A.q i s| ≤ A.θmax i - A.θmin i := by
    calc
      |∫ s in A.θmin i..A.θ i ω, A.q i s| =
          ‖∫ s in A.θmin i..A.θ i ω, A.q i s‖ := by
        rw [Real.norm_eq_abs]
      _ ≤ 1 * |A.θ i ω - A.θmin i| :=
        intervalIntegral.norm_integral_le_of_norm_le_const fun s _ => by
          rw [Real.norm_eq_abs, abs_of_nonneg (A.q_range i s).1]
          exact (A.q_range i s).2
      _ = A.θ i ω - A.θmin i := by
        rw [one_mul, abs_of_nonneg (sub_nonneg.mpr hθ.1)]
      _ ≤ A.θmax i - A.θmin i :=
        sub_le_sub_right hθ.2 _
  change |A.p i (A.θ i ω)| ≤ C
  rw [A.payment_formula i hθ]
  calc
    |A.θ i ω * A.q i (A.θ i ω) - A.U i (A.θmin i) -
        ∫ s in A.θmin i..A.θ i ω, A.q i s| ≤
        |A.θ i ω * A.q i (A.θ i ω) - A.U i (A.θmin i)| +
          |∫ s in A.θmin i..A.θ i ω, A.q i s| :=
      abs_sub _ _
    _ ≤ (|A.θ i ω * A.q i (A.θ i ω)| + |A.U i (A.θmin i)|) +
          |∫ s in A.θmin i..A.θ i ω, A.q i s| :=
      add_le_add (abs_sub _ _) le_rfl
    _ ≤ C := by
      dsimp only [C]
      exact add_le_add (add_le_add hmul le_rfl) hintegral

/-- Bidder `i`'s expected payment is its expected raw virtual surplus minus its lowest-type
utility. -/
theorem expectedPayment_eq_integral_q_mul_virtualValue
    [HasBoundedTypes A] [HasDensity A] [A.rules.HasValidAllocation] [A.BIC]
    (ρ : A.DensityFamily) (i : Fin n) :
    (A.valueDistribution i).expectedPayment
        (A.toBidderProblem id i).toSingleParameterProblem =
      (∫ v, A.q i v * A.virtualValue ρ i v
        ∂(A.valueDistribution i : Measure ℝ)) - A.U i (A.θmin i) := by
  have hpos : ∀ᵐ v ∂(volume.restrict (A.interval i)), 0 < ρ.f i v :=
    ae_restrict_of_forall_mem measurableSet_Icc (ρ.pos i)
  simpa only [BidderProblem.toSingleParameterProblem_q,
    BidderProblem.toSingleParameterProblem_U, toBidderProblem_q,
    toBidderProblem_U, virtualValue] using
    (A.valueDistribution i).expectedPayment_eq_integral_q_mul_virtualValue
      (A.toBidderProblem id i).toSingleParameterProblem (ρ.f i)
      (A.θmin_le_θmax i) (A.valueDistribution_isSupportedOnInterval i)
      (A.valueDistribution_absolutelyContinuous i) (ρ.ae_eq i) hpos

/-- Expected revenue is the sum of bidders' expected raw virtual surpluses, less their lowest-type
utilities. -/
theorem expectedRevenue_eq_sum_integral_q_mul_virtualValue_sub
    [NeZero n] [HasIndependentTypes A] [HasBoundedTypes A] [HasDensity A]
    [A.rules.HasValidAllocation] [A.BIC] (ρ : A.DensityFamily)
    (ht : ∀ i, Measurable (A.rules.t i)) :
    A.expectedRevenue =
      ∑ i, ((∫ v, A.q i v * A.virtualValue ρ i v
        ∂(A.valueDistribution i : Measure ℝ)) - A.U i (A.θmin i)) := by
  rw [expectedRevenue,
    integral_finset_sum _ fun i _ =>
      A.integrable_p_comp_θ i (A.measurable_p i (ht i))]
  exact Finset.sum_congr rfl fun i _ => by
    calc
      (∫ ω, A.p i (A.θ i ω) ∂ℙ) =
          (A.valueDistribution i).expectedPayment
            (A.toBidderProblem id i).toSingleParameterProblem :=
        A.integral_p_comp_θ_eq_expectedPayment i (A.measurable_p i (ht i))
      _ = (∫ v, A.q i v * A.virtualValue ρ i v
            ∂(A.valueDistribution i : Measure ℝ)) - A.U i (A.θmin i) :=
        A.expectedPayment_eq_integral_q_mul_virtualValue ρ i

/-- If every lowest type receives zero utility, expected revenue is the sum of bidders' expected
raw virtual surpluses. -/
theorem expectedRevenue_eq_sum_integral_q_mul_virtualValue
    [NeZero n] [HasIndependentTypes A] [HasBoundedTypes A] [HasDensity A]
    [A.rules.HasValidAllocation] [A.BIC] (ρ : A.DensityFamily)
    (ht : ∀ i, Measurable (A.rules.t i))
    (hU0 : ∀ i, A.U i (A.θmin i) = 0) :
    A.expectedRevenue =
      ∑ i, ∫ v, A.q i v * A.virtualValue ρ i v
        ∂(A.valueDistribution i : Measure ℝ) := by
  rw [A.expectedRevenue_eq_sum_integral_q_mul_virtualValue_sub ρ ht]
  exact Finset.sum_congr rfl fun i _ => by rw [hU0 i, sub_zero]

/-- With zero lowest-type utilities, expected revenue equals expected ex-post raw virtual
surplus. -/
theorem expectedRevenue_eq_virtualSurplus
    [NeZero n] [HasIndependentTypes A] [HasBoundedTypes A] [HasDensity A]
    [A.rules.HasValidAllocation] [A.BIC] (ρ : A.DensityFamily)
    (ht : ∀ i, Measurable (A.rules.t i))
    (hU0 : ∀ i, A.U i (A.θmin i) = 0) :
    A.expectedRevenue =
      ∑ i, 𝔼[fun ω =>
        A.virtualValue ρ i (A.θ i ω) * A.rules.x i (A.θ · ω)] := by
  rw [A.expectedRevenue_eq_sum_integral_q_mul_virtualValue ρ ht hU0]
  exact Finset.sum_congr rfl fun i _ => by
    calc
      (∫ v, A.q i v * A.virtualValue ρ i v
          ∂(A.valueDistribution i : Measure ℝ)) =
          ∫ v, A.virtualValue ρ i v * A.q i v
            ∂(A.valueDistribution i : Measure ℝ) := by
        apply integral_congr_ae
        exact ae_of_all _ fun v => mul_comm _ _
      _ = 𝔼[fun ω =>
          A.virtualValue ρ i (A.θ i ω) * A.rules.x i (A.θ · ω)] :=
        (A.integral_mul_x_eq_integral_mul_q_valueDistribution i
          (A.measurable_virtualValue ρ i)
          (A.integrable_virtualValue_mul_x ρ i)).symm

/-- Interim individual rationality bounds expected revenue by the sum of bidders' expected raw
virtual surpluses. -/
theorem expectedRevenue_le_sum_integral_q_mul_virtualValue
    [NeZero n] [HasIndependentTypes A] [HasBoundedTypes A] [HasDensity A]
    [A.rules.HasValidAllocation] [A.BIC] (ρ : A.DensityFamily)
    (ht : ∀ i, Measurable (A.rules.t i)) (hIR : A.InterimIR) :
    A.expectedRevenue ≤
      ∑ i, ∫ v, A.q i v * A.virtualValue ρ i v
        ∂(A.valueDistribution i : Measure ℝ) := by
  rw [A.expectedRevenue_eq_sum_integral_q_mul_virtualValue_sub ρ ht]
  exact Finset.sum_le_sum fun i _ =>
    sub_le_self _ (hIR i (A.θmin i) ⟨le_rfl, A.θmin_le_θmax i⟩)

/-- Interim individual rationality bounds expected revenue by expected ex-post raw virtual
surplus. -/
theorem expectedRevenue_le_virtualSurplus
    [NeZero n] [HasIndependentTypes A] [HasBoundedTypes A] [HasDensity A]
    [A.rules.HasValidAllocation] [A.BIC] (ρ : A.DensityFamily)
    (ht : ∀ i, Measurable (A.rules.t i)) (hIR : A.InterimIR) :
    A.expectedRevenue ≤
      ∑ i, 𝔼[fun ω =>
        A.virtualValue ρ i (A.θ i ω) * A.rules.x i (A.θ · ω)] := by
  calc
    A.expectedRevenue ≤
        ∑ i, ∫ v, A.q i v * A.virtualValue ρ i v
          ∂(A.valueDistribution i : Measure ℝ) :=
      A.expectedRevenue_le_sum_integral_q_mul_virtualValue ρ ht hIR
    _ = ∑ i, 𝔼[fun ω =>
          A.virtualValue ρ i (A.θ i ω) * A.rules.x i (A.θ · ω)] := by
      exact Finset.sum_congr rfl fun i _ => by
        calc
          (∫ v, A.q i v * A.virtualValue ρ i v
              ∂(A.valueDistribution i : Measure ℝ)) =
              ∫ v, A.virtualValue ρ i v * A.q i v
                ∂(A.valueDistribution i : Measure ℝ) := by
            apply integral_congr_ae
            exact ae_of_all _ fun v => mul_comm _ _
          _ = 𝔼[fun ω =>
              A.virtualValue ρ i (A.θ i ω) * A.rules.x i (A.θ · ω)] :=
            (A.integral_mul_x_eq_integral_mul_q_valueDistribution i
              (A.measurable_virtualValue ρ i)
              (A.integrable_virtualValue_mul_x ρ i)).symm

/-- Myerson's raw virtual-surplus bound. It is universal but is generally tight only under
regularity. -/
theorem expectedRevenue_le_optimalVirtualSurplus
    [NeZero n] [HasIndependentTypes A] [HasBoundedTypes A] [HasDensity A]
    [A.rules.IsFeasible] [A.BIC] (ρ : A.DensityFamily)
    (ht : ∀ i, Measurable (A.rules.t i)) (hIR : A.InterimIR) :
    A.expectedRevenue ≤
      𝔼[fun ω => A.optimalVirtualSurplus ρ (A.θ · ω)] := by
  have hsum : Integrable
      (fun ω => ∑ i,
        A.virtualValue ρ i (A.θ i ω) * A.rules.x i (A.θ · ω)) ℙ :=
    integrable_finset_sum _ fun i _ => A.integrable_virtualValue_mul_x ρ i
  calc
    A.expectedRevenue ≤
        ∑ i, 𝔼[fun ω =>
          A.virtualValue ρ i (A.θ i ω) * A.rules.x i (A.θ · ω)] :=
      A.expectedRevenue_le_virtualSurplus ρ ht hIR
    _ = 𝔼[fun ω => ∑ i,
          A.virtualValue ρ i (A.θ i ω) * A.rules.x i (A.θ · ω)] :=
      (integral_finset_sum _ fun i _ => A.integrable_virtualValue_mul_x ρ i).symm
    _ ≤ 𝔼[fun ω => A.optimalVirtualSurplus ρ (A.θ · ω)] :=
      integral_mono hsum (A.integrable_optimalVirtualSurplus_comp_profile ρ)
        fun ω => A.sum_virtualValue_mul_x_le ρ (A.θ · ω)

/-- A BIC bidder's expected raw virtual surplus is at most its expected ironed virtual surplus. -/
theorem integral_q_mul_virtualValue_le_ironed
    [NeZero n] [HasIndependentTypes A] [HasBoundedTypes A] [HasDensity A]
    [A.rules.HasValidAllocation] [A.BIC] (ρ : A.DensityFamily) (i : Fin n) :
    (∫ v, A.q i v * A.virtualValue ρ i v
      ∂(A.valueDistribution i : Measure ℝ)) ≤
      ∫ v, A.q i v * A.ironedVirtualValue ρ i v
        ∂(A.valueDistribution i : Measure ℝ) := by
  letI : NoAtoms (A.valueDistribution i : Measure ℝ) :=
    noAtoms_of_absolutelyContinuous_volume
      (A.valueDistribution_absolutelyContinuous i)
  have hmono : MonotoneOn (A.q i) (A.interval i) := by
    simpa only [toBidderProblem_q] using
      (A.toBidderProblem id i).q_monotoneOn
  simpa only [ironedVirtualValue] using
    (A.valueDistribution i).integral_mul_le_integral_mul_ironed
      (A.virtualValue ρ i) (A.valueDistribution_isSupportedOnInterval i)
      (A.continuousOn_virtualValue ρ i) (fun v _ => A.q_range i v) hmono

/-- The universal ironed Myerson bound: Expected revenue is at most expected pointwise optimal
ironed virtual surplus. -/
theorem expectedRevenue_le_ironedOptimalVirtualSurplus
    [NeZero n] [HasIndependentTypes A] [HasBoundedTypes A] [HasDensity A]
    [A.rules.IsFeasible] [A.BIC] (ρ : A.DensityFamily)
    (ht : ∀ i, Measurable (A.rules.t i)) (hIR : A.InterimIR) :
    A.expectedRevenue ≤
      𝔼[fun ω => A.ironedOptimalVirtualSurplus ρ (A.θ · ω)] := by
  have hsum : Integrable
      (fun ω => ∑ i,
        A.ironedVirtualValue ρ i (A.θ i ω) * A.rules.x i (A.θ · ω)) ℙ :=
    integrable_finset_sum _ fun i _ => A.integrable_ironedVirtualValue_mul_x ρ i
  calc
    A.expectedRevenue ≤
        ∑ i, ∫ v, A.q i v * A.virtualValue ρ i v
          ∂(A.valueDistribution i : Measure ℝ) :=
      A.expectedRevenue_le_sum_integral_q_mul_virtualValue ρ ht hIR
    _ ≤ ∑ i, ∫ v, A.q i v * A.ironedVirtualValue ρ i v
          ∂(A.valueDistribution i : Measure ℝ) :=
      Finset.sum_le_sum fun i _ => A.integral_q_mul_virtualValue_le_ironed ρ i
    _ = ∑ i, 𝔼[fun ω =>
          A.ironedVirtualValue ρ i (A.θ i ω) * A.rules.x i (A.θ · ω)] := by
      exact Finset.sum_congr rfl fun i _ => by
        calc
          (∫ v, A.q i v * A.ironedVirtualValue ρ i v
              ∂(A.valueDistribution i : Measure ℝ)) =
              ∫ v, A.ironedVirtualValue ρ i v * A.q i v
                ∂(A.valueDistribution i : Measure ℝ) := by
            apply integral_congr_ae
            exact ae_of_all _ fun v => mul_comm _ _
          _ = 𝔼[fun ω =>
              A.ironedVirtualValue ρ i (A.θ i ω) * A.rules.x i (A.θ · ω)] :=
            (A.integral_mul_x_eq_integral_mul_q_valueDistribution i
              (A.measurable_ironedVirtualValue ρ i)
              (A.integrable_ironedVirtualValue_mul_x ρ i)).symm
    _ = 𝔼[fun ω => ∑ i,
          A.ironedVirtualValue ρ i (A.θ i ω) * A.rules.x i (A.θ · ω)] :=
      (integral_finset_sum _ fun i _ => A.integrable_ironedVirtualValue_mul_x ρ i).symm
    _ ≤ 𝔼[fun ω => A.ironedOptimalVirtualSurplus ρ (A.θ · ω)] :=
      integral_mono hsum (A.integrable_ironedOptimalVirtualSurplus_comp_profile ρ)
        fun ω => A.sum_ironedVirtualValue_mul_x_le ρ (A.θ · ω)

end Auction

end
