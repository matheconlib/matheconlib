/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.MeasureTheory.Constructions.UnitInterval
import Auctionlib.Auction.OptimalAuction

/-!
# Myerson-layer compatibility checks

These examples pin the public C5–C7 contracts for feasible mechanisms, highest-score allocation,
the ex-post-to-interim bridge, virtual values, Myerson revenue bounds, and optimal auctions.
-/

noncomputable section

open scoped unitInterval

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

/-! ## Optimal auctions -/

section OptimalAuction

variable {Ω : Type} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} (A : Auction Ω n) (M : Mechanism n)

/-! ### Replacing an auction's rules -/

example : (A.withRules M).rules = M :=
  Auction.withRules_rules A M

example : (A.withRules M).θmin = A.θmin :=
  Auction.withRules_θmin A M

example : (A.withRules M).θmax = A.θmax :=
  Auction.withRules_θmax A M

example : (A.withRules M).θ = A.θ :=
  Auction.withRules_θ A M

example (i : Fin n) : (A.withRules M).interval i = A.interval i :=
  Auction.withRules_interval A M i

example (i : Fin n) :
    (A.withRules M).valueDistribution i = A.valueDistribution i :=
  Auction.withRules_valueDistribution A M i

example (i : Fin n) (s : ℝ) :
    (A.withRules M).q i s = A.interimAlloc M.x i s :=
  Auction.withRules_q A M i s

example (i : Fin n) (s : ℝ) :
    (A.withRules M).p i s =
      𝔼[fun ω => M.t i (update (A.θ · ω) i s)] :=
  Auction.withRules_p A M i s

example (i : Fin n) (s : ℝ) :
    (A.withRules M).U i s = s * A.interimAlloc M.x i s -
      𝔼[fun ω => M.t i (update (A.θ · ω) i s)] :=
  Auction.withRules_U A M i s

example [NeZero n] :
    (A.withRules M).expectedRevenue =
      𝔼[fun ω => ∑ i,
        𝔼[fun ω' => M.t i (update (A.θ · ω') i (A.θ i ω))]] :=
  Auction.withRules_expectedRevenue A M

example [Auction.HasIndependentTypes A] :
    Auction.HasIndependentTypes (A.withRules M) :=
  inferInstance

example [Auction.HasBoundedTypes A] :
    Auction.HasBoundedTypes (A.withRules M) :=
  inferInstance

example [Auction.HasDensity A] : Auction.HasDensity (A.withRules M) :=
  inferInstance

example [NeZero n] [Auction.HasIdenticalTypes A] :
    Auction.HasIdenticalTypes (A.withRules M) :=
  inferInstance

example [NeZero n] [Auction.HasAtomlessTypes A] :
    Auction.HasAtomlessTypes (A.withRules M) :=
  inferInstance

example [M.IsFeasible] : (A.withRules M).rules.IsFeasible :=
  inferInstance

example [M.HasValidAllocation] :
    (A.withRules M).rules.HasValidAllocation :=
  inferInstance

example [M.IsEfficient] : (A.withRules M).rules.IsEfficient :=
  inferInstance

/-! ### Transporting density families -/

variable (ρ : A.DensityFamily)

example : (A.withRules M).DensityFamily :=
  ρ.withRules M

example : (ρ.withRules M).f = ρ.f :=
  Auction.DensityFamily.withRules_f A ρ M

example (i : Fin n) :
    (A.withRules M).virtualValue (ρ.withRules M) i =
      A.virtualValue ρ i :=
  Auction.withRules_virtualValue A ρ M i

example (i : Fin n) :
    (A.withRules M).ironedVirtualValue (ρ.withRules M) i =
      A.ironedVirtualValue ρ i :=
  Auction.withRules_ironedVirtualValue A ρ M i

example [NeZero n] (θ : Fin n → ℝ) :
    (A.withRules M).optimalVirtualSurplus (ρ.withRules M) θ =
      A.optimalVirtualSurplus ρ θ :=
  Auction.withRules_optimalVirtualSurplus A ρ M θ

example [NeZero n] (θ : Fin n → ℝ) :
    (A.withRules M).ironedOptimalVirtualSurplus (ρ.withRules M) θ =
      A.ironedOptimalVirtualSurplus ρ θ :=
  Auction.withRules_ironedOptimalVirtualSurplus A ρ M θ

example : (ρ.withRules M).IsRegular ↔ ρ.IsRegular :=
  Auction.withRules_isRegular_iff A ρ M

/-! ### Myerson payments and mechanisms -/

example (x : Fin n → (Fin n → ℝ) → ℝ) (i : Fin n)
    (θ : Fin n → ℝ) :
    A.myersonPayment x i θ =
      θ i * A.interimAlloc x i (θ i) -
        ∫ s in A.θmin i..θ i, A.interimAlloc x i s :=
  rfl

example : (A.myersonMechanism M).x = M.x :=
  Auction.myersonMechanism_x A M

example : (A.myersonMechanism M).t = A.myersonPayment M.x :=
  Auction.myersonMechanism_t A M

example [M.IsFeasible] : (A.myersonMechanism M).IsFeasible :=
  inferInstance

example [M.HasValidAllocation] :
    (A.myersonMechanism M).HasValidAllocation :=
  inferInstance

example [M.HasValidAllocation] (i : Fin n) :
    Measurable (A.myersonPayment M.x i) :=
  A.measurable_myersonPayment M i

example (i : Fin n) (s : ℝ) :
    (A.withRules (A.myersonMechanism M)).q i s =
      A.interimAlloc M.x i s :=
  A.withRules_myersonMechanism_q M i s

example (i : Fin n) (s : ℝ) :
    (A.withRules (A.myersonMechanism M)).p i s =
      s * A.interimAlloc M.x i s -
        ∫ w in A.θmin i..s, A.interimAlloc M.x i w :=
  A.withRules_myersonMechanism_p M i s

example (i : Fin n) (s : ℝ) :
    (A.withRules (A.myersonMechanism M)).U i s =
      ∫ w in A.θmin i..s, A.interimAlloc M.x i w :=
  A.withRules_myersonMechanism_U M i s

example (i : Fin n) :
    (A.withRules (A.myersonMechanism M)).U i (A.θmin i) = 0 :=
  A.withRules_myersonMechanism_U_θmin M i

example [M.HasValidAllocation] :
    (A.withRules (A.myersonMechanism M)).InterimIR :=
  A.withRules_myersonMechanism_interimIR M

example [M.HasValidAllocation]
    (hmono : ∀ i, MonotoneOn (A.interimAlloc M.x i) (A.interval i)) :
    (A.withRules (A.myersonMechanism M)).BIC :=
  A.withRules_myersonMechanism_bic M hmono

variable (v : Fin n → ℝ → ℝ) (hv : ∀ i, Measurable (v i))

example :
    A.myersonRules v hv =
      A.myersonMechanism (Mechanism.ofHighestScore v hv 0) :=
  rfl

example :
    (A.myersonRules v hv).x = Mechanism.highestScoreAlloc v :=
  A.myersonRules_x v hv

example : (A.myersonRules v hv).IsFeasible :=
  inferInstance

example : (A.myersonRules v hv).HasValidAllocation :=
  inferInstance

example (hmono : ∀ i, MonotoneOn (v i) (A.interval i)) :
    (A.withRules (A.myersonRules v hv)).BIC :=
  A.myersonRules_bic v hv hmono

example : (A.withRules (A.myersonRules v hv)).InterimIR :=
  A.myersonRules_interimIR v hv

example (i : Fin n) :
    (A.withRules (A.myersonRules v hv)).U i (A.θmin i) = 0 :=
  A.myersonRules_U_θmin v hv i

example (i : Fin n) : Measurable ((A.myersonRules v hv).t i) :=
  A.measurable_myersonRules_t v hv i

end OptimalAuction

/-! ### Revenue, existence, and optimality -/

section OptimalRevenue

variable {Ω : Type} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} [NeZero n] (A : Auction Ω n)
  [Auction.HasIndependentTypes A] [Auction.HasBoundedTypes A]
  [Auction.HasDensity A]
variable (ρ : A.DensityFamily)

example (M : Mechanism n) [M.HasValidAllocation]
    (hmono : ∀ i, MonotoneOn (A.interimAlloc M.x i) (A.interval i)) :
    (A.withRules (A.myersonMechanism M)).expectedRevenue =
      ∑ i, ∫ v, A.interimAlloc M.x i v * A.virtualValue ρ i v
        ∂(A.valueDistribution i : Measure ℝ) :=
  A.withRules_myersonMechanism_expectedRevenue ρ M hmono

example :
    A.optimalRules ρ =
      A.myersonRules (A.virtualValue ρ) (A.measurable_virtualValue ρ) :=
  rfl

example :
    A.ironedOptimalRules ρ =
      A.myersonRules (A.ironedVirtualValue ρ)
        (A.measurable_ironedVirtualValue ρ) :=
  rfl

example : (A.optimalRules ρ).IsFeasible :=
  inferInstance

example : (A.ironedOptimalRules ρ).IsFeasible :=
  inferInstance

example (hreg : ρ.IsRegular) :
    (A.withRules (A.optimalRules ρ)).expectedRevenue =
      𝔼[fun ω => A.optimalVirtualSurplus ρ (A.θ · ω)] :=
  A.optimalRules_expectedRevenue ρ hreg

example :
    (A.withRules (A.ironedOptimalRules ρ)).expectedRevenue =
      𝔼[fun ω => A.ironedOptimalVirtualSurplus ρ (A.θ · ω)] :=
  A.ironedOptimalRules_expectedRevenue ρ

example (hreg : ρ.IsRegular) :
    ∃ M : Mechanism n, M.IsFeasible ∧ (A.withRules M).BIC ∧
      (A.withRules M).InterimIR ∧
      (∀ i, (A.withRules M).U i (A.θmin i) = 0) ∧
      (A.withRules M).expectedRevenue =
        𝔼[fun ω => A.optimalVirtualSurplus ρ (A.θ · ω)] :=
  A.exists_optimal_auction_regular ρ hreg

example :
    ∃ M : Mechanism n, M.IsFeasible ∧ (A.withRules M).BIC ∧
      (A.withRules M).InterimIR ∧
      (∀ i, (A.withRules M).U i (A.θmin i) = 0) ∧
      (A.withRules M).expectedRevenue =
        𝔼[fun ω => A.ironedOptimalVirtualSurplus ρ (A.θ · ω)] :=
  A.exists_optimal_auction_ironed ρ

example (hreg : ρ.IsRegular) (M : Mechanism n) [M.IsFeasible]
    [(A.withRules M).BIC] (hIR : (A.withRules M).InterimIR)
    (ht : ∀ i, Measurable (M.t i)) :
    (A.withRules M).expectedRevenue ≤
      (A.withRules (A.optimalRules ρ)).expectedRevenue :=
  A.expectedRevenue_le_optimalRules ρ hreg M hIR ht

example (M : Mechanism n) [M.IsFeasible] [(A.withRules M).BIC]
    (hIR : (A.withRules M).InterimIR)
    (ht : ∀ i, Measurable (M.t i)) :
    (A.withRules M).expectedRevenue ≤
      (A.withRules (A.ironedOptimalRules ρ)).expectedRevenue :=
  A.expectedRevenue_le_ironedOptimalRules ρ M hIR ht

end OptimalRevenue

/-! ## Two symmetric uniform bidders -/

section UniformSanity

/-- The sample space for two independent canonical uniform draws. Its volume measure is Mathlib's
finite product measure. -/
public abbrev TwoBidderUniformSample := Fin 2 → unitInterval

example :
    (volume : Measure TwoBidderUniformSample) =
      Measure.pi (fun _ : Fin 2 => (volume : Measure unitInterval)) :=
  rfl

private def uniformSanityRules : Mechanism 2 where
  x := fun _ _ => 0
  x_measurable := fun _ => measurable_const
  t := fun _ _ => 0

/-- A two-bidder auction whose types are the two coordinates of the canonical product of unit
intervals. The initial rules are immaterial because `exists_optimal_auction_regular` replaces
them. -/
private def uniformSanityAuction : Auction TwoBidderUniformSample 2 where
  rules := uniformSanityRules
  θmin := fun _ => 0
  θmax := fun _ => 1
  θ := fun i ω => ω i
  θ_measurable := fun i => measurable_subtype_coe.comp (measurable_pi_apply i)

private lemma uniformSanity_measurePreserving (i : Fin 2) :
    MeasurePreserving (uniformSanityAuction.θ i)
      (volume : Measure TwoBidderUniformSample)
      (volume.restrict (Icc 0 1) : Measure ℝ) := by
  change MeasurePreserving (fun ω : TwoBidderUniformSample => (ω i : ℝ))
    (Measure.pi fun _ : Fin 2 => (volume : Measure unitInterval))
    (volume.restrict (Icc 0 1))
  simpa only [Function.comp_apply] using
    unitInterval.measurePreserving_coe.comp
      (measurePreserving_eval
        (fun _ : Fin 2 => (volume : Measure unitInterval)) i)

local instance : Auction.HasIndependentTypes uniformSanityAuction where
  θ_indep := by
    change iIndepFun
      (fun i (ω : TwoBidderUniformSample) => (ω i : ℝ))
      (Measure.pi fun _ : Fin 2 => (volume : Measure unitInterval))
    exact iIndepFun_pi fun _ => measurable_subtype_coe.aemeasurable

local instance : Auction.HasIdenticalTypes uniformSanityAuction where
  θ_identical i j :=
    { aemeasurable_fst := (uniformSanityAuction.θ_measurable i).aemeasurable
      aemeasurable_snd := (uniformSanityAuction.θ_measurable j).aemeasurable
      map_eq := (uniformSanity_measurePreserving i).map_eq.trans
        (uniformSanity_measurePreserving j).map_eq.symm }
  θmin_eq := fun _ => rfl
  θmax_eq := fun _ => rfl

local instance : Auction.HasBoundedTypes uniformSanityAuction where
  θ_in := fun _ ω => (ω _).property

local instance : Auction.HasDensity uniformSanityAuction where
  θ_hasPDF i := by
    refine ⟨(uniformSanity_measurePreserving i).measurable.aemeasurable, ?_, ?_⟩
    · rw [(uniformSanity_measurePreserving i).map_eq]
      infer_instance
    · rw [(uniformSanity_measurePreserving i).map_eq]
      exact Measure.absolutelyContinuous_restrict

local instance : Auction.HasAtomlessTypes uniformSanityAuction where
  θ_noAtoms := by
    rw [(uniformSanity_measurePreserving 0).map_eq]
    infer_instance

private lemma uniformSanity_valueDistribution (i : Fin 2) :
    ((uniformSanityAuction.valueDistribution i : ValueDistribution) : Measure ℝ) =
      volume.restrict (Icc 0 1) := by
  rw [Auction.toMeasure_valueDistribution]
  exact (uniformSanity_measurePreserving i).map_eq

/-- The constant one density representative for both unit-interval coordinates. -/
private def uniformSanityDensity : uniformSanityAuction.DensityFamily where
  f := fun _ _ => 1
  measurable := fun _ => measurable_const
  continuousOn := fun _ => continuousOn_const
  pos := fun _ _ _ => by norm_num
  ae_eq i := by
    change (fun _ : ℝ => 1) =ᵐ[volume.restrict (Icc 0 1)]
      fun v =>
        (((uniformSanityAuction.valueDistribution i : ValueDistribution) : Measure ℝ).rnDeriv
          volume v).toReal
    rw [uniformSanity_valueDistribution i]
    filter_upwards [
      ae_restrict_of_ae
        (Measure.rnDeriv_restrict_self (volume : Measure ℝ) measurableSet_Icc),
      ae_restrict_mem (μ := volume) measurableSet_Icc] with v hv hmem
    rw [hv]
    simp [Set.indicator_of_mem hmem]

private lemma uniformSanityDensity_isRegular : uniformSanityDensity.IsRegular := by
  intro i x _ y _ hxy
  have htail :=
    (uniformSanityAuction.valueDistribution i).antitone_probAtLeast hxy
  simpa [Auction.virtualValue, uniformSanityDensity,
    ValueDistribution.virtualValue, ValueDistribution.virtualSurplusWeight] using
    sub_le_sub hxy htail

example : Auction.IsSymmetricIPV uniformSanityAuction where
  toHasIndependentTypes := inferInstance
  toHasIdenticalTypes := inferInstance
  toHasBoundedTypes := inferInstance
  toHasDensity := inferInstance
  toHasAtomlessTypes := inferInstance

example :
    ∃ M : Mechanism 2, M.IsFeasible ∧ (uniformSanityAuction.withRules M).BIC ∧
      (uniformSanityAuction.withRules M).InterimIR ∧
      (∀ i, (uniformSanityAuction.withRules M).U i (uniformSanityAuction.θmin i) = 0) ∧
      (uniformSanityAuction.withRules M).expectedRevenue =
        𝔼[fun ω => uniformSanityAuction.optimalVirtualSurplus uniformSanityDensity
          (uniformSanityAuction.θ · ω)] :=
  uniformSanityAuction.exists_optimal_auction_regular uniformSanityDensity
    uniformSanityDensity_isRegular

end UniformSanity

end MyersonCompatibility

end
