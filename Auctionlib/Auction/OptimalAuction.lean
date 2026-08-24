/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Auctionlib.Auction.RevenueIdentity

/-!
# Optimal Auctions

This file constructs Myerson mechanisms from ex-post allocation rules and proves achievability and
optimality of the raw and ironed virtual-surplus bounds.
-/

@[expose] public section

open Function MeasureTheory ProbabilityTheory Set

noncomputable section

namespace Auction

variable {Ω : Type} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} (A : Auction Ω n)

/-! ### Replacing an auction's rules -/

/-- Replace an auction's mechanism while preserving its type environment. -/
def withRules (M : Mechanism n) : Auction Ω n :=
  { A with rules := M }

@[simp] lemma withRules_rules (M : Mechanism n) :
    (A.withRules M).rules = M := rfl

@[simp] lemma withRules_θmin (M : Mechanism n) :
    (A.withRules M).θmin = A.θmin := rfl

@[simp] lemma withRules_θmax (M : Mechanism n) :
    (A.withRules M).θmax = A.θmax := rfl

@[simp] lemma withRules_θ (M : Mechanism n) :
    (A.withRules M).θ = A.θ := rfl

@[simp] lemma withRules_interval (M : Mechanism n) (i : Fin n) :
    (A.withRules M).interval i = A.interval i := rfl

@[simp] lemma withRules_valueDistribution (M : Mechanism n) (i : Fin n) :
    (A.withRules M).valueDistribution i = A.valueDistribution i := rfl

@[simp] lemma withRules_q (M : Mechanism n) (i : Fin n) (s : ℝ) :
    (A.withRules M).q i s = A.interimAlloc M.x i s := rfl

@[simp] lemma withRules_p (M : Mechanism n) (i : Fin n) (s : ℝ) :
    (A.withRules M).p i s =
      𝔼[fun ω => M.t i (update (A.θ · ω) i s)] := rfl

@[simp] lemma withRules_U (M : Mechanism n) (i : Fin n) (s : ℝ) :
    (A.withRules M).U i s = s * A.interimAlloc M.x i s -
      𝔼[fun ω => M.t i (update (A.θ · ω) i s)] := rfl

@[simp] lemma withRules_expectedRevenue [NeZero n] (M : Mechanism n) :
    (A.withRules M).expectedRevenue =
      𝔼[fun ω => ∑ i,
        𝔼[fun ω' => M.t i (update (A.θ · ω') i (A.θ i ω))]] := rfl

instance withRules_hasIndependentTypes (M : Mechanism n) [HasIndependentTypes A] :
    HasIndependentTypes (A.withRules M) where
  θ_indep := HasIndependentTypes.θ_indep (A := A)

instance withRules_hasBoundedTypes (M : Mechanism n) [HasBoundedTypes A] :
    HasBoundedTypes (A.withRules M) where
  θ_in := HasBoundedTypes.θ_in (A := A)

instance withRules_hasDensity (M : Mechanism n) [HasDensity A] :
    HasDensity (A.withRules M) where
  θ_hasPDF := HasDensity.θ_hasPDF (A := A)

instance withRules_hasIdenticalTypes [NeZero n] (M : Mechanism n) [HasIdenticalTypes A] :
    HasIdenticalTypes (A.withRules M) where
  θ_identical := HasIdenticalTypes.θ_identical (A := A)
  θmin_eq := HasIdenticalTypes.θmin_eq (A := A)
  θmax_eq := HasIdenticalTypes.θmax_eq (A := A)

instance withRules_hasAtomlessTypes [NeZero n] (M : Mechanism n) [HasAtomlessTypes A] :
    HasAtomlessTypes (A.withRules M) where
  θ_noAtoms := HasAtomlessTypes.θ_noAtoms (A := A)

instance withRules_isFeasible (M : Mechanism n) [M.IsFeasible] :
    (A.withRules M).rules.IsFeasible := by
  change M.IsFeasible
  infer_instance

instance withRules_hasValidAllocation (M : Mechanism n) [M.HasValidAllocation] :
    (A.withRules M).rules.HasValidAllocation := by
  change M.HasValidAllocation
  infer_instance

instance withRules_isEfficient (M : Mechanism n) [M.IsEfficient] :
    (A.withRules M).rules.IsEfficient := by
  change M.IsEfficient
  infer_instance

/-! ### Transporting chosen densities -/

/-- A chosen density family is unchanged when only the auction rules are replaced. -/
def DensityFamily.withRules {A : Auction Ω n} (ρ : A.DensityFamily) (M : Mechanism n) :
    (A.withRules M).DensityFamily where
  f := ρ.f
  measurable := ρ.measurable
  continuousOn i := by
    simpa only [withRules_interval] using ρ.continuousOn i
  pos i v hv := ρ.pos i v (by simpa only [withRules_interval] using hv)
  ae_eq i := by
    simpa only [withRules_interval, withRules_valueDistribution] using ρ.ae_eq i

@[simp] lemma DensityFamily.withRules_f (ρ : A.DensityFamily)
    (M : Mechanism n) : (ρ.withRules M).f = ρ.f := rfl

@[simp] lemma withRules_virtualValue (ρ : A.DensityFamily)
    (M : Mechanism n) (i : Fin n) :
    (A.withRules M).virtualValue (ρ.withRules M) i = A.virtualValue ρ i := rfl

@[simp] lemma withRules_ironedVirtualValue (ρ : A.DensityFamily)
    (M : Mechanism n) (i : Fin n) :
    (A.withRules M).ironedVirtualValue (ρ.withRules M) i =
      A.ironedVirtualValue ρ i := rfl

@[simp] lemma withRules_optimalVirtualSurplus [NeZero n]
    (ρ : A.DensityFamily) (M : Mechanism n) (θ : Fin n → ℝ) :
    (A.withRules M).optimalVirtualSurplus (ρ.withRules M) θ =
      A.optimalVirtualSurplus ρ θ := rfl

@[simp] lemma withRules_ironedOptimalVirtualSurplus [NeZero n]
    (ρ : A.DensityFamily) (M : Mechanism n) (θ : Fin n → ℝ) :
    (A.withRules M).ironedOptimalVirtualSurplus (ρ.withRules M) θ =
      A.ironedOptimalVirtualSurplus ρ θ := rfl

@[simp] lemma withRules_isRegular_iff (ρ : A.DensityFamily)
    (M : Mechanism n) :
    (ρ.withRules M).IsRegular ↔ ρ.IsRegular :=
  Iff.rfl

/-! ### Myerson payments and mechanisms -/

/-- The ex-post payment induced by an allocation rule's interim allocation. -/
noncomputable def myersonPayment
    (x : Fin n → (Fin n → ℝ) → ℝ) (i : Fin n) (θ : Fin n → ℝ) : ℝ :=
  θ i * A.interimAlloc x i (θ i) -
    ∫ s in A.θmin i..θ i, A.interimAlloc x i s

/-- Replace a mechanism's payment rule by the Myerson payment induced by its allocation rule. -/
noncomputable def myersonMechanism (M : Mechanism n) : Mechanism n :=
  { M with t := A.myersonPayment M.x }

@[simp] lemma myersonMechanism_x (M : Mechanism n) :
    (A.myersonMechanism M).x = M.x := rfl

@[simp] lemma myersonMechanism_t (M : Mechanism n) :
    (A.myersonMechanism M).t = A.myersonPayment M.x := rfl

instance myersonMechanism_isFeasible (M : Mechanism n) [M.IsFeasible] :
    (A.myersonMechanism M).IsFeasible where
  x_nonneg := Mechanism.IsFeasible.x_nonneg (M := M)
  sum_x_le_one := Mechanism.IsFeasible.sum_x_le_one (M := M)

instance myersonMechanism_hasValidAllocation
    (M : Mechanism n) [M.HasValidAllocation] :
    (A.myersonMechanism M).HasValidAllocation where
  x_range := Mechanism.HasValidAllocation.x_range (M := M)

/-- The Myerson payment is measurable in the report profile. -/
lemma measurable_myersonPayment (M : Mechanism n) [M.HasValidAllocation]
    (i : Fin n) : Measurable (A.myersonPayment M.x i) := by
  have hq : Measurable (A.interimAlloc M.x i) :=
    A.measurable_interimAlloc M.x M.x_measurable i
  have hprim : Continuous
      (fun t => ∫ s in A.θmin i..t, A.interimAlloc M.x i s) :=
    intervalIntegral.continuous_primitive
      (fun a b => A.intervalIntegrable_interimAlloc M.x
        (fun j θ => Mechanism.HasValidAllocation.x_range (M := M) j θ)
        M.x_measurable i a b) (A.θmin i)
  unfold myersonPayment
  exact
    ((measurable_pi_apply i).mul (hq.comp (measurable_pi_apply i))).sub
      (hprim.measurable.comp (measurable_pi_apply i))

@[simp] lemma withRules_myersonMechanism_q
    (M : Mechanism n) (i : Fin n) (s : ℝ) :
    (A.withRules (A.myersonMechanism M)).q i s =
      A.interimAlloc M.x i s := rfl

@[simp] lemma withRules_myersonMechanism_p
    (M : Mechanism n) (i : Fin n) (s : ℝ) :
    (A.withRules (A.myersonMechanism M)).p i s =
      s * A.interimAlloc M.x i s -
        ∫ w in A.θmin i..s, A.interimAlloc M.x i w := by
  rw [withRules_p]
  simp only [myersonMechanism, myersonPayment, update_self]
  rw [integral_const]
  simp

@[simp] lemma withRules_myersonMechanism_U
    (M : Mechanism n) (i : Fin n) (s : ℝ) :
    (A.withRules (A.myersonMechanism M)).U i s =
      ∫ w in A.θmin i..s, A.interimAlloc M.x i w := by
  rw [U, withRules_myersonMechanism_q, withRules_myersonMechanism_p]
  ring

@[simp] lemma withRules_myersonMechanism_U_θmin
    (M : Mechanism n) (i : Fin n) :
    (A.withRules (A.myersonMechanism M)).U i (A.θmin i) = 0 := by
  rw [withRules_myersonMechanism_U, intervalIntegral.integral_same]

/-- A Myerson mechanism is interim individually rational. -/
theorem withRules_myersonMechanism_interimIR
    (M : Mechanism n) [M.HasValidAllocation] :
    (A.withRules (A.myersonMechanism M)).InterimIR := by
  intro i s hs
  rw [withRules_myersonMechanism_U]
  exact intervalIntegral.integral_nonneg hs.1 fun w _ =>
    A.interimAlloc_nonneg M.x
      (fun j θ => Mechanism.HasValidAllocation.x_range (M := M) j θ) i w

/-- Monotone interim allocations make the associated Myerson mechanism Bayesian incentive
compatible. -/
theorem withRules_myersonMechanism_bic
    (M : Mechanism n) [M.HasValidAllocation]
    (hmono : ∀ i, MonotoneOn (A.interimAlloc M.x i) (A.interval i)) :
    (A.withRules (A.myersonMechanism M)).BIC := by
  apply (A.withRules (A.myersonMechanism M)).bic_of_forall_typeDeviationIC
  intro i
  apply BidderProblem.typeDeviationIC_of_monotone_q
    ((A.withRules (A.myersonMechanism M)).toBidderProblem id i)
  · simpa only [BidderProblem.q, comp_apply,
      toBidderProblem_winProb, toBidderProblem_strategy, id_eq,
      withRules_myersonMechanism_q, withRules_interval] using hmono i
  · intro s _
    change (A.withRules (A.myersonMechanism M)).p i s =
      s * (A.withRules (A.myersonMechanism M)).q i s -
        (A.withRules (A.myersonMechanism M)).U i (A.θmin i) -
          ∫ w in A.θmin i..s,
            (A.withRules (A.myersonMechanism M)).q i w
    rw [withRules_myersonMechanism_p, withRules_myersonMechanism_q,
      withRules_myersonMechanism_U_θmin, sub_zero]
    simp only [withRules_myersonMechanism_q]

/-! ### Highest-score Myerson rules -/

/-- The Myerson mechanism induced by the highest-score allocation. -/
noncomputable def myersonRules (v : Fin n → ℝ → ℝ)
    (hv : ∀ i, Measurable (v i)) : Mechanism n :=
  A.myersonMechanism (Mechanism.ofHighestScore v hv 0)

@[simp] lemma myersonRules_x (v : Fin n → ℝ → ℝ)
    (hv : ∀ i, Measurable (v i)) :
    (A.myersonRules v hv).x = Mechanism.highestScoreAlloc v := rfl

instance myersonRules_isFeasible (v : Fin n → ℝ → ℝ)
    (hv : ∀ i, Measurable (v i)) :
    (A.myersonRules v hv).IsFeasible := by
  unfold myersonRules
  infer_instance

instance myersonRules_hasValidAllocation (v : Fin n → ℝ → ℝ)
    (hv : ∀ i, Measurable (v i)) :
    (A.myersonRules v hv).HasValidAllocation := inferInstance

/-- Highest-score Myerson rules are BIC when every score is monotone on its type interval. -/
theorem myersonRules_bic (v : Fin n → ℝ → ℝ)
    (hv : ∀ i, Measurable (v i))
    (hmono : ∀ i, MonotoneOn (v i) (A.interval i)) :
    (A.withRules (A.myersonRules v hv)).BIC := by
  unfold myersonRules
  apply A.withRules_myersonMechanism_bic
  intro i
  simpa only [Mechanism.ofHighestScore_x] using
    A.interimAlloc_highestScoreAlloc_monotoneOn v hv i (hmono i)

/-- Highest-score Myerson rules are interim individually rational. -/
theorem myersonRules_interimIR (v : Fin n → ℝ → ℝ)
    (hv : ∀ i, Measurable (v i)) :
    (A.withRules (A.myersonRules v hv)).InterimIR := by
  unfold myersonRules
  exact A.withRules_myersonMechanism_interimIR _

/-- Highest-score Myerson rules give every lowest type zero utility. -/
@[simp] lemma myersonRules_U_θmin (v : Fin n → ℝ → ℝ)
    (hv : ∀ i, Measurable (v i)) (i : Fin n) :
    (A.withRules (A.myersonRules v hv)).U i (A.θmin i) = 0 := by
  unfold myersonRules
  exact A.withRules_myersonMechanism_U_θmin _ i

/-- Highest-score Myerson payments are measurable. -/
lemma measurable_myersonRules_t (v : Fin n → ℝ → ℝ)
    (hv : ∀ i, Measurable (v i)) (i : Fin n) :
    Measurable ((A.myersonRules v hv).t i) := by
  unfold myersonRules
  exact A.measurable_myersonPayment (Mechanism.ofHighestScore v hv 0) i

/-! ### Revenue of the optimal rules -/

section OptimalRevenue

variable [NeZero n] [HasIndependentTypes A] [HasBoundedTypes A] [HasDensity A]
variable (ρ : A.DensityFamily)

/-- The Myerson mechanism's revenue is the sum of interim raw virtual surpluses. -/
theorem withRules_myersonMechanism_expectedRevenue
    (M : Mechanism n) [M.HasValidAllocation]
    (hmono : ∀ i, MonotoneOn (A.interimAlloc M.x i) (A.interval i)) :
    (A.withRules (A.myersonMechanism M)).expectedRevenue =
      ∑ i, ∫ v, A.interimAlloc M.x i v * A.virtualValue ρ i v
        ∂(A.valueDistribution i : Measure ℝ) := by
  letI : (A.withRules (A.myersonMechanism M)).BIC :=
    A.withRules_myersonMechanism_bic M hmono
  have ht : ∀ i,
      Measurable ((A.withRules (A.myersonMechanism M)).rules.t i) :=
    fun i => A.measurable_myersonPayment M i
  have hU0 : ∀ i,
      (A.withRules (A.myersonMechanism M)).U i
        ((A.withRules (A.myersonMechanism M)).θmin i) = 0 :=
    fun i => A.withRules_myersonMechanism_U_θmin M i
  simpa only [withRules_q, myersonMechanism_x, withRules_virtualValue,
    withRules_valueDistribution] using
      (A.withRules (A.myersonMechanism M)).expectedRevenue_eq_sum_integral_q_mul_virtualValue
        (ρ.withRules (A.myersonMechanism M)) ht hU0

/-- Myerson rules based on raw virtual values. -/
noncomputable def optimalRules : Mechanism n :=
  A.myersonRules (A.virtualValue ρ) (A.measurable_virtualValue ρ)

/-- Myerson rules based on ironed virtual values. -/
noncomputable def ironedOptimalRules : Mechanism n :=
  A.myersonRules (A.ironedVirtualValue ρ) (A.measurable_ironedVirtualValue ρ)

instance optimalRules_isFeasible : (A.optimalRules ρ).IsFeasible := by
  unfold optimalRules
  infer_instance

instance ironedOptimalRules_isFeasible : (A.ironedOptimalRules ρ).IsFeasible := by
  unfold ironedOptimalRules
  infer_instance

/-- Under regularity, the raw virtual-value rules attain the raw pointwise bound. -/
theorem optimalRules_expectedRevenue (hreg : ρ.IsRegular) :
    (A.withRules (A.optimalRules ρ)).expectedRevenue =
      𝔼[fun ω => A.optimalVirtualSurplus ρ (A.θ · ω)] := by
  letI : (A.withRules (A.optimalRules ρ)).BIC := by
    unfold optimalRules
    exact A.myersonRules_bic (A.virtualValue ρ)
      (A.measurable_virtualValue ρ) hreg
  have ht : ∀ i, Measurable ((A.withRules (A.optimalRules ρ)).rules.t i) :=
    fun i => by
      simpa only [withRules_rules, optimalRules] using
        A.measurable_myersonRules_t (A.virtualValue ρ)
          (A.measurable_virtualValue ρ) i
  have hU0 : ∀ i,
      (A.withRules (A.optimalRules ρ)).U i
        ((A.withRules (A.optimalRules ρ)).θmin i) = 0 :=
    fun i => by
      simpa only [withRules_θmin, optimalRules] using
        A.myersonRules_U_θmin (A.virtualValue ρ)
          (A.measurable_virtualValue ρ) i
  have hrev := (A.withRules (A.optimalRules ρ)).expectedRevenue_eq_virtualSurplus
    (ρ.withRules (A.optimalRules ρ)) ht hU0
  have hint : ∀ i, Integrable
      (fun ω => A.virtualValue ρ i (A.θ i ω) *
        Mechanism.highestScoreAlloc (A.virtualValue ρ) i (A.θ · ω)) ℙ := by
    intro i
    simpa only [withRules_virtualValue, withRules_θ, withRules_rules,
      optimalRules, myersonRules_x] using
      (A.withRules (A.optimalRules ρ)).integrable_virtualValue_mul_x
        (ρ.withRules (A.optimalRules ρ)) i
  calc
    (A.withRules (A.optimalRules ρ)).expectedRevenue =
        ∑ i, 𝔼[fun ω => A.virtualValue ρ i (A.θ i ω) *
          Mechanism.highestScoreAlloc (A.virtualValue ρ) i (A.θ · ω)] := by
      simpa only [withRules_virtualValue, withRules_θ, withRules_rules,
        optimalRules, myersonRules_x] using hrev
    _ = 𝔼[fun ω => ∑ i, A.virtualValue ρ i (A.θ i ω) *
          Mechanism.highestScoreAlloc (A.virtualValue ρ) i (A.θ · ω)] :=
      (integral_finset_sum _ fun i _ => hint i).symm
    _ = 𝔼[fun ω => A.optimalVirtualSurplus ρ (A.θ · ω)] := by
      apply integral_congr_ae
      exact ae_of_all ℙ fun ω =>
        Mechanism.sum_score_mul_highestScoreAlloc
          (A.virtualValue ρ) (A.θ · ω)

/-- The ironed virtual-value rules attain the ironed pointwise bound. -/
theorem ironedOptimalRules_expectedRevenue :
    (A.withRules (A.ironedOptimalRules ρ)).expectedRevenue =
      𝔼[fun ω => A.ironedOptimalVirtualSurplus ρ (A.θ · ω)] := by
  have hqmono : ∀ i, MonotoneOn
      (A.interimAlloc (Mechanism.highestScoreAlloc (A.ironedVirtualValue ρ)) i)
        (A.interval i) := fun i =>
    A.interimAlloc_highestScoreAlloc_monotoneOn
      (A.ironedVirtualValue ρ) (A.measurable_ironedVirtualValue ρ) i
      ((A.monotone_ironedVirtualValue ρ i).monotoneOn (A.interval i))
  have hrev : (A.withRules (A.ironedOptimalRules ρ)).expectedRevenue =
      ∑ i, ∫ v,
        A.interimAlloc (Mechanism.highestScoreAlloc (A.ironedVirtualValue ρ)) i v *
          A.virtualValue ρ i v ∂(A.valueDistribution i : Measure ℝ) := by
    simpa only [ironedOptimalRules, myersonRules, Mechanism.ofHighestScore_x] using
      A.withRules_myersonMechanism_expectedRevenue ρ
        (Mechanism.ofHighestScore (A.ironedVirtualValue ρ)
          (A.measurable_ironedVirtualValue ρ) 0)
        (fun i => by
          simpa only [Mechanism.ofHighestScore_x] using hqmono i)
  have hiron : ∀ i,
      (∫ v,
        A.interimAlloc (Mechanism.highestScoreAlloc (A.ironedVirtualValue ρ)) i v *
          A.virtualValue ρ i v ∂(A.valueDistribution i : Measure ℝ)) =
      ∫ v,
        A.interimAlloc (Mechanism.highestScoreAlloc (A.ironedVirtualValue ρ)) i v *
          A.ironedVirtualValue ρ i v ∂(A.valueDistribution i : Measure ℝ) := by
    intro i
    letI : NoAtoms (A.valueDistribution i : Measure ℝ) :=
      noAtoms_of_absolutelyContinuous_volume
        (A.valueDistribution_absolutelyContinuous i)
    simpa only [ironedVirtualValue] using
      (A.valueDistribution i).integral_mul_eq_integral_mul_ironed
        (A.virtualValue ρ i) (A.valueDistribution_isSupportedOnInterval i)
        (A.continuousOn_virtualValue ρ i)
        (fun v _ => A.interimAlloc_mem_Icc
          (Mechanism.highestScoreAlloc (A.ironedVirtualValue ρ))
          (Mechanism.highestScoreAlloc_mem_Icc (A.ironedVirtualValue ρ)) i v)
        (hqmono i)
        (fun _ _ _ _ h =>
          A.interimAlloc_highestScoreAlloc_congr (A.ironedVirtualValue ρ) i h)
  have hbridge : ∀ i,
      𝔼[fun ω => A.ironedVirtualValue ρ i (A.θ i ω) *
        Mechanism.highestScoreAlloc (A.ironedVirtualValue ρ) i (A.θ · ω)] =
      ∫ v, A.ironedVirtualValue ρ i v *
        A.interimAlloc (Mechanism.highestScoreAlloc (A.ironedVirtualValue ρ)) i v
          ∂(A.valueDistribution i : Measure ℝ) := by
    intro i
    simpa only [withRules_ironedVirtualValue, withRules_θ, withRules_rules,
      withRules_q, withRules_valueDistribution, ironedOptimalRules, myersonRules_x] using
      (A.withRules (A.ironedOptimalRules ρ)).integral_mul_x_eq_integral_mul_q_valueDistribution i
        ((A.withRules (A.ironedOptimalRules ρ)).measurable_ironedVirtualValue
          (ρ.withRules (A.ironedOptimalRules ρ)) i)
        ((A.withRules (A.ironedOptimalRules ρ)).integrable_ironedVirtualValue_mul_x
          (ρ.withRules (A.ironedOptimalRules ρ)) i)
  have hint : ∀ i, Integrable
      (fun ω => A.ironedVirtualValue ρ i (A.θ i ω) *
        Mechanism.highestScoreAlloc (A.ironedVirtualValue ρ) i (A.θ · ω)) ℙ := by
    intro i
    simpa only [withRules_ironedVirtualValue, withRules_θ, withRules_rules,
      ironedOptimalRules, myersonRules_x] using
      (A.withRules (A.ironedOptimalRules ρ)).integrable_ironedVirtualValue_mul_x
        (ρ.withRules (A.ironedOptimalRules ρ)) i
  calc
    (A.withRules (A.ironedOptimalRules ρ)).expectedRevenue =
        ∑ i, ∫ v,
          A.interimAlloc (Mechanism.highestScoreAlloc (A.ironedVirtualValue ρ)) i v *
            A.virtualValue ρ i v ∂(A.valueDistribution i : Measure ℝ) := hrev
    _ = ∑ i, ∫ v,
          A.interimAlloc (Mechanism.highestScoreAlloc (A.ironedVirtualValue ρ)) i v *
            A.ironedVirtualValue ρ i v ∂(A.valueDistribution i : Measure ℝ) :=
      Finset.sum_congr rfl fun i _ => hiron i
    _ = ∑ i, 𝔼[fun ω => A.ironedVirtualValue ρ i (A.θ i ω) *
          Mechanism.highestScoreAlloc (A.ironedVirtualValue ρ) i (A.θ · ω)] :=
      Finset.sum_congr rfl fun i _ => by
        calc
          (∫ v,
              A.interimAlloc (Mechanism.highestScoreAlloc
                (A.ironedVirtualValue ρ)) i v * A.ironedVirtualValue ρ i v
                ∂(A.valueDistribution i : Measure ℝ)) =
              ∫ v, A.ironedVirtualValue ρ i v *
                A.interimAlloc (Mechanism.highestScoreAlloc
                  (A.ironedVirtualValue ρ)) i v
                  ∂(A.valueDistribution i : Measure ℝ) := by
            apply integral_congr_ae
            exact ae_of_all _ fun v => mul_comm _ _
          _ = 𝔼[fun ω => A.ironedVirtualValue ρ i (A.θ i ω) *
                Mechanism.highestScoreAlloc (A.ironedVirtualValue ρ) i (A.θ · ω)] :=
            (hbridge i).symm
    _ = 𝔼[fun ω => ∑ i, A.ironedVirtualValue ρ i (A.θ i ω) *
          Mechanism.highestScoreAlloc (A.ironedVirtualValue ρ) i (A.θ · ω)] :=
      (integral_finset_sum _ fun i _ => hint i).symm
    _ = 𝔼[fun ω => A.ironedOptimalVirtualSurplus ρ (A.θ · ω)] := by
      apply integral_congr_ae
      exact ae_of_all ℙ fun ω =>
        Mechanism.sum_score_mul_highestScoreAlloc
          (A.ironedVirtualValue ρ) (A.θ · ω)

/-! ### Achievability and optimality -/

/-- Myerson's optimal auction in a regular environment. -/
theorem exists_optimal_auction_regular (hreg : ρ.IsRegular) :
    ∃ M : Mechanism n, M.IsFeasible ∧ (A.withRules M).BIC ∧
      (A.withRules M).InterimIR ∧
      (∀ i, (A.withRules M).U i (A.θmin i) = 0) ∧
      (A.withRules M).expectedRevenue =
        𝔼[fun ω => A.optimalVirtualSurplus ρ (A.θ · ω)] := by
  refine ⟨A.optimalRules ρ, inferInstance, ?_, ?_, ?_,
    A.optimalRules_expectedRevenue ρ hreg⟩
  · unfold optimalRules
    exact A.myersonRules_bic (A.virtualValue ρ)
      (A.measurable_virtualValue ρ) hreg
  · simpa only [optimalRules] using
      A.myersonRules_interimIR (A.virtualValue ρ)
        (A.measurable_virtualValue ρ)
  · intro i
    simpa only [optimalRules] using
      A.myersonRules_U_θmin (A.virtualValue ρ)
        (A.measurable_virtualValue ρ) i

/-- Myerson's optimal auction in an arbitrary, possibly irregular, environment. -/
theorem exists_optimal_auction_ironed :
    ∃ M : Mechanism n, M.IsFeasible ∧ (A.withRules M).BIC ∧
      (A.withRules M).InterimIR ∧
      (∀ i, (A.withRules M).U i (A.θmin i) = 0) ∧
      (A.withRules M).expectedRevenue =
        𝔼[fun ω => A.ironedOptimalVirtualSurplus ρ (A.θ · ω)] := by
  refine ⟨A.ironedOptimalRules ρ, inferInstance, ?_, ?_, ?_,
    A.ironedOptimalRules_expectedRevenue ρ⟩
  · unfold ironedOptimalRules
    exact A.myersonRules_bic (A.ironedVirtualValue ρ)
      (A.measurable_ironedVirtualValue ρ) fun i =>
        (A.monotone_ironedVirtualValue ρ i).monotoneOn (A.interval i)
  · simpa only [ironedOptimalRules] using
      A.myersonRules_interimIR (A.ironedVirtualValue ρ)
        (A.measurable_ironedVirtualValue ρ)
  · intro i
    simpa only [ironedOptimalRules] using
      A.myersonRules_U_θmin (A.ironedVirtualValue ρ)
        (A.measurable_ironedVirtualValue ρ) i

/-- No admissible auction earns more than the regular optimal rules. -/
theorem expectedRevenue_le_optimalRules (hreg : ρ.IsRegular)
    (M : Mechanism n) [M.IsFeasible] [(A.withRules M).BIC]
    (hIR : (A.withRules M).InterimIR)
    (ht : ∀ i, Measurable (M.t i)) :
    (A.withRules M).expectedRevenue ≤
      (A.withRules (A.optimalRules ρ)).expectedRevenue := by
  calc
    (A.withRules M).expectedRevenue ≤
        𝔼[fun ω => A.optimalVirtualSurplus ρ (A.θ · ω)] := by
      simpa only [withRules_optimalVirtualSurplus, withRules_θ] using
        (A.withRules M).expectedRevenue_le_optimalVirtualSurplus
          (ρ.withRules M) (fun i => by
            change Measurable (M.t i)
            exact ht i) hIR
    _ = (A.withRules (A.optimalRules ρ)).expectedRevenue :=
      (A.optimalRules_expectedRevenue ρ hreg).symm

/-- No admissible auction earns more than the ironed optimal rules. -/
theorem expectedRevenue_le_ironedOptimalRules
    (M : Mechanism n) [M.IsFeasible] [(A.withRules M).BIC]
    (hIR : (A.withRules M).InterimIR)
    (ht : ∀ i, Measurable (M.t i)) :
    (A.withRules M).expectedRevenue ≤
      (A.withRules (A.ironedOptimalRules ρ)).expectedRevenue := by
  calc
    (A.withRules M).expectedRevenue ≤
        𝔼[fun ω => A.ironedOptimalVirtualSurplus ρ (A.θ · ω)] := by
      simpa only [withRules_ironedOptimalVirtualSurplus, withRules_θ] using
        (A.withRules M).expectedRevenue_le_ironedOptimalVirtualSurplus
          (ρ.withRules M) (fun i => by
            change Measurable (M.t i)
            exact ht i) hIR
    _ = (A.withRules (A.ironedOptimalRules ρ)).expectedRevenue :=
      (A.ironedOptimalRules_expectedRevenue ρ).symm

end OptimalRevenue

end Auction

end
