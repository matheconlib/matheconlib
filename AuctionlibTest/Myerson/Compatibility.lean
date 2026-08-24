/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

import Auctionlib.Auction.RevenueIdentity

/-!
# Myerson-Layer Compatibility Checks

These examples pin the public C5 and C6 contracts for feasible mechanisms, highest-score
allocation, the ex-post-to-interim bridge, virtual values, and Myerson revenue bounds.
-/

noncomputable section

open Function MeasureTheory ProbabilityTheory Set

namespace MyersonCompatibility

/-! ## Feasible and highest-score mechanisms -/

section Mechanism

variable {n : ℕ} (M : Mechanism n)

example [M.IsFeasible] (i : Fin n) (b : Fin n → ℝ) :
    M.x i b ≤ 1 :=
  Mechanism.IsFeasible.x_le_one (M := M) i b

example [M.IsFeasible] : M.HasValidAllocation :=
  inferInstance

example [M.IsEfficient] : M.IsFeasible :=
  inferInstance

variable (v : Fin n → ℝ → ℝ) (θ : Fin n → ℝ)

example (i : Fin n) :
    Mechanism.highestScoreAlloc v i θ ∈ Icc 0 1 :=
  Mechanism.highestScoreAlloc_mem_Icc v i θ

example :
    ∑ i, Mechanism.highestScoreAlloc v i θ ≤ 1 :=
  Mechanism.sum_highestScoreAlloc_le_one v θ

example [NeZero n] :
    ∑ i, v i (θ i) * Mechanism.highestScoreAlloc v i θ =
      max 0 (Finset.univ.sup' Finset.univ_nonempty fun i => v i (θ i)) :=
  Mechanism.sum_score_mul_highestScoreAlloc v θ

example [NeZero n] [M.IsFeasible] :
    ∑ i, v i (θ i) * M.x i θ ≤
      max 0 (Finset.univ.sup' Finset.univ_nonempty fun i => v i (θ i)) :=
  Mechanism.sum_score_mul_x_le M v θ

example (hv : ∀ i, Measurable (v i))
    (t : Fin n → (Fin n → ℝ) → ℝ) :
    (Mechanism.ofHighestScore v hv t).IsFeasible :=
  inferInstance

end Mechanism

/-! ## Interim bridge -/

section Auction

variable {Ω : Type} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} (A : Auction Ω n)

example [Auction.HasBoundedTypes A] (i : Fin n) :
    A.θmin i ≤ A.θmax i :=
  A.θmin_le_θmax i

example : Measurable (fun ω i => A.θ i ω) :=
  A.measurable_profile

example (i : Fin n) (s : ℝ) :
    A.q i s = A.interimAlloc A.rules.x i s :=
  A.q_eq_interimAlloc i s

example (i : Fin n) : Measurable (A.q i) :=
  A.measurable_q i

example [Auction.HasIndependentTypes A] (i : Fin n)
    {g : (Fin n → ℝ) → ℝ} (hg : Measurable g)
    (hint : Integrable (fun ω => g (A.θ · ω)) ℙ) :
    𝔼[fun ω => g (A.θ · ω)] =
      𝔼[fun ω => 𝔼[fun ω' =>
        g (update (A.θ · ω') i (A.θ i ω))]] :=
  A.integral_eq_integral_update i hg hint

example [Auction.HasIndependentTypes A] (i : Fin n)
    {φ : ℝ → ℝ} (hφ : Measurable φ)
    (hint : Integrable
      (fun ω => φ (A.θ i ω) * A.rules.x i (A.θ · ω)) ℙ) :
    𝔼[fun ω => φ (A.θ i ω) * A.rules.x i (A.θ · ω)] =
      ∫ s, φ s * A.q i s ∂(A.valueDistribution i : Measure ℝ) :=
  A.integral_mul_x_eq_integral_mul_q_valueDistribution i hφ hint

example [Auction.HasIndependentTypes A] (i : Fin n)
    (ht : Measurable (A.rules.t i))
    (hint : Integrable (fun ω => A.rules.t i (A.θ · ω)) ℙ) :
    𝔼[fun ω => A.rules.t i (A.θ · ω)] =
      𝔼[fun ω => A.p i (A.θ i ω)] :=
  A.integral_t_eq_integral_p i ht hint

example [A.rules.HasValidAllocation]
    (h : ∀ i, (A.toBidderProblem id i).HasTypeDeviationIC) :
    A.BIC :=
  A.bic_of_forall_typeDeviationIC h

example (v : Fin n → ℝ → ℝ) (hv : ∀ j, Measurable (v j))
    (i : Fin n) (hmono : MonotoneOn (v i) (A.interval i)) :
    MonotoneOn (A.interimAlloc (Mechanism.highestScoreAlloc v) i)
      (A.interval i) :=
  A.interimAlloc_highestScoreAlloc_monotoneOn v hv i hmono

example (v : Fin n → ℝ → ℝ) (i : Fin n) {t t' : ℝ}
    (h : v i t = v i t') :
    A.interimAlloc (Mechanism.highestScoreAlloc v) i t =
      A.interimAlloc (Mechanism.highestScoreAlloc v) i t' :=
  A.interimAlloc_highestScoreAlloc_congr v i h

end Auction

/-! ## Virtual values and revenue identities -/

section VirtualValue

variable {Ω : Type} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} [NeZero n] (A : Auction Ω n)
  [Auction.HasIndependentTypes A] [Auction.HasBoundedTypes A]
  [Auction.HasDensity A]
variable (ρ : A.DensityFamily)

example (i : Fin n) :
    A.virtualValue ρ i = (A.valueDistribution i).virtualValue (ρ.f i) :=
  rfl

example (i : Fin n) : Measurable (A.virtualValue ρ i) :=
  A.measurable_virtualValue ρ i

example (i : Fin n) : ContinuousOn (A.virtualValue ρ i) (A.interval i) :=
  A.continuousOn_virtualValue ρ i

example (i : Fin n) :
    Integrable (fun ω => A.virtualValue ρ i (A.θ i ω)) ℙ :=
  A.integrable_virtualValue_comp_θ ρ i

example :
    ρ.IsRegular ↔
      ∀ i, (A.valueDistribution i).IsRegular
        (ρ.f i) (A.θmin i) (A.θmax i) :=
  Iff.rfl

example (i : Fin n) :
    A.ironedVirtualValue ρ i =
      (A.valueDistribution i).ironed (A.virtualValue ρ i) :=
  rfl

example (i : Fin n) : Monotone (A.ironedVirtualValue ρ i) :=
  A.monotone_ironedVirtualValue ρ i

example (i : Fin n) : Measurable (A.ironedVirtualValue ρ i) :=
  A.measurable_ironedVirtualValue ρ i

example (i : Fin n) :
    Integrable (fun ω => A.ironedVirtualValue ρ i (A.θ i ω)) ℙ :=
  A.integrable_ironedVirtualValue_comp_θ ρ i

example (hreg : ρ.IsRegular) (i : Fin n) {v : ℝ}
    (hv : v ∈ Ioo (A.θmin i) (A.θmax i)) :
    A.ironedVirtualValue ρ i v = A.virtualValue ρ i v :=
  A.ironedVirtualValue_eq_virtualValue_of_regular hreg i hv

example (θ : Fin n → ℝ) :
    A.optimalVirtualSurplus ρ θ =
      max 0 (Finset.univ.sup' Finset.univ_nonempty fun i =>
        A.virtualValue ρ i (θ i)) :=
  rfl

example (θ : Fin n → ℝ) :
    A.ironedOptimalVirtualSurplus ρ θ =
      max 0 (Finset.univ.sup' Finset.univ_nonempty fun i =>
        A.ironedVirtualValue ρ i (θ i)) :=
  rfl

example : Measurable (A.optimalVirtualSurplus ρ) :=
  A.measurable_optimalVirtualSurplus ρ

example : Measurable (A.ironedOptimalVirtualSurplus ρ) :=
  A.measurable_ironedOptimalVirtualSurplus ρ

example : Integrable (fun ω => A.optimalVirtualSurplus ρ (A.θ · ω)) ℙ :=
  A.integrable_optimalVirtualSurplus_comp_profile ρ

example : Integrable (fun ω => A.ironedOptimalVirtualSurplus ρ (A.θ · ω)) ℙ :=
  A.integrable_ironedOptimalVirtualSurplus_comp_profile ρ

example (hreg : ρ.IsRegular) :
    𝔼[fun ω => A.ironedOptimalVirtualSurplus ρ (A.θ · ω)] =
      𝔼[fun ω => A.optimalVirtualSurplus ρ (A.θ · ω)] :=
  A.integral_ironedOptimalVirtualSurplus_eq_of_regular hreg

section ValidAllocation

variable [A.rules.HasValidAllocation] [A.BIC]

example (i : Fin n) (hp : Measurable (A.p i)) :
    Integrable (fun ω => A.p i (A.θ i ω)) ℙ :=
  A.integrable_p_comp_θ i hp

example (i : Fin n) :
    (A.valueDistribution i).expectedPayment
        (A.toBidderProblem id i).toSingleParameterProblem =
      (∫ v, A.q i v * A.virtualValue ρ i v
        ∂(A.valueDistribution i : Measure ℝ)) - A.U i (A.θmin i) :=
  A.expectedPayment_eq_integral_q_mul_virtualValue ρ i

example (ht : ∀ i, Measurable (A.rules.t i)) :
    A.expectedRevenue =
      ∑ i, ((∫ v, A.q i v * A.virtualValue ρ i v
        ∂(A.valueDistribution i : Measure ℝ)) - A.U i (A.θmin i)) :=
  A.expectedRevenue_eq_sum_integral_q_mul_virtualValue_sub ρ ht

example (ht : ∀ i, Measurable (A.rules.t i))
    (hU0 : ∀ i, A.U i (A.θmin i) = 0) :
    A.expectedRevenue =
      ∑ i, ∫ v, A.q i v * A.virtualValue ρ i v
        ∂(A.valueDistribution i : Measure ℝ) :=
  A.expectedRevenue_eq_sum_integral_q_mul_virtualValue ρ ht hU0

example (ht : ∀ i, Measurable (A.rules.t i))
    (hU0 : ∀ i, A.U i (A.θmin i) = 0) :
    A.expectedRevenue =
      ∑ i, 𝔼[fun ω =>
        A.virtualValue ρ i (A.θ i ω) * A.rules.x i (A.θ · ω)] :=
  A.expectedRevenue_eq_virtualSurplus ρ ht hU0

example (ht : ∀ i, Measurable (A.rules.t i)) (hIR : A.InterimIR) :
    A.expectedRevenue ≤
      ∑ i, ∫ v, A.q i v * A.virtualValue ρ i v
        ∂(A.valueDistribution i : Measure ℝ) :=
  A.expectedRevenue_le_sum_integral_q_mul_virtualValue ρ ht hIR

example (ht : ∀ i, Measurable (A.rules.t i)) (hIR : A.InterimIR) :
    A.expectedRevenue ≤
      ∑ i, 𝔼[fun ω =>
        A.virtualValue ρ i (A.θ i ω) * A.rules.x i (A.θ · ω)] :=
  A.expectedRevenue_le_virtualSurplus ρ ht hIR

example (i : Fin n) :
    (∫ v, A.q i v * A.virtualValue ρ i v
      ∂(A.valueDistribution i : Measure ℝ)) ≤
      ∫ v, A.q i v * A.ironedVirtualValue ρ i v
        ∂(A.valueDistribution i : Measure ℝ) :=
  A.integral_q_mul_virtualValue_le_ironed ρ i

end ValidAllocation

section Feasible

variable [A.rules.IsFeasible] [A.BIC]

example (θ : Fin n → ℝ) :
    ∑ i, A.virtualValue ρ i (θ i) * A.rules.x i θ ≤
      A.optimalVirtualSurplus ρ θ :=
  A.sum_virtualValue_mul_x_le ρ θ

example (θ : Fin n → ℝ) :
    ∑ i, A.ironedVirtualValue ρ i (θ i) * A.rules.x i θ ≤
      A.ironedOptimalVirtualSurplus ρ θ :=
  A.sum_ironedVirtualValue_mul_x_le ρ θ

example (ht : ∀ i, Measurable (A.rules.t i)) (hIR : A.InterimIR) :
    A.expectedRevenue ≤
      𝔼[fun ω => A.optimalVirtualSurplus ρ (A.θ · ω)] :=
  A.expectedRevenue_le_optimalVirtualSurplus ρ ht hIR

example (ht : ∀ i, Measurable (A.rules.t i)) (hIR : A.InterimIR) :
    A.expectedRevenue ≤
      𝔼[fun ω => A.ironedOptimalVirtualSurplus ρ (A.θ · ω)] :=
  A.expectedRevenue_le_ironedOptimalVirtualSurplus ρ ht hIR

end Feasible

end VirtualValue

end MyersonCompatibility

end
