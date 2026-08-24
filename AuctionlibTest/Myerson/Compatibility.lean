/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

import Auctionlib.Auction.Interim

/-!
# Myerson-Layer Compatibility Checks

These examples pin the public C5 contracts for feasible mechanisms, highest-score allocation, and
the ex-post-to-interim bridge.
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

end MyersonCompatibility

end
