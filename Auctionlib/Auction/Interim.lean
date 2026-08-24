/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Auctionlib.Auction.ValueDistribution
public import Auctionlib.ForMathlib.IndepFun
public import Auctionlib.Mechanism.HighestScore
public import Auctionlib.ValueDistribution.SingleParameter

/-!
# Interim allocation and ex-post-to-interim identities

This file supplies measurable interim allocation rules and the independence bridge that rewrites
ex-post expectations as interim expectations.
-/

@[expose] public section

open Function MeasureTheory ProbabilityTheory Set

namespace Auction

variable {Ω : Type} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} (A : Auction Ω n)

/-- Bounded types force the declared type interval to be nonempty. -/
lemma θmin_le_θmax [HasBoundedTypes A] (i : Fin n) :
    A.θmin i ≤ A.θmax i := by
  let ω : Ω := Classical.choice (nonempty_of_isProbabilityMeasure ℙ)
  exact (HasBoundedTypes.θ_in (A := A) i ω).1.trans
    (HasBoundedTypes.θ_in (A := A) i ω).2

/-- The full type profile is measurable. -/
lemma measurable_profile : Measurable (fun ω i => A.θ i ω) := by
  rw [measurable_pi_iff]
  exact A.θ_measurable

/-- Updating one coordinate of a measurable random profile by a separate real input is
measurable. -/
lemma measurable_update_profile (i : Fin n) :
    Measurable (fun p : ℝ × Ω => update (A.θ · p.2) i p.1) := by
  rw [measurable_pi_iff]
  intro j
  by_cases hji : j = i
  · subst j
    simpa using (measurable_fst : Measurable (fun p : ℝ × Ω => p.1))
  · simpa [update_of_ne hji] using
      (A.θ_measurable j).comp (measurable_snd : Measurable (fun p : ℝ × Ω => p.2))

/-- A measurable function of one bidder's bounded type is integrable. -/
lemma integrable_comp_θ_of_bounded [HasBoundedTypes A] (i : Fin n)
    {φ : ℝ → ℝ} (hφ : Measurable φ) {C : ℝ}
    (hC : ∀ v ∈ A.interval i, |φ v| ≤ C) :
    Integrable (fun ω => φ (A.θ i ω)) ℙ := by
  apply Integrable.of_bound
    ((hφ.comp (A.θ_measurable i)).aestronglyMeasurable) C
  exact ae_of_all ℙ fun ω => by
    rw [Real.norm_eq_abs]
    exact hC _ (HasBoundedTypes.θ_in (A := A) i ω)

/-- Interim expectation for an allocation rule that need not be the auction's current allocation
rule. -/
noncomputable def interimAlloc
    (x : Fin n → (Fin n → ℝ) → ℝ) (i : Fin n) (s : ℝ) : ℝ :=
  𝔼[fun ω => x i (update (A.θ · ω) i s)]

/-- The auction's existing interim allocation is the generic interim allocation applied to its
current rules. -/
lemma q_eq_interimAlloc (i : Fin n) (s : ℝ) :
    A.q i s = A.interimAlloc A.rules.x i s :=
  rfl

/-- A generic interim allocation is nonnegative when the underlying allocation rule takes values in
`[0, 1]`. -/
lemma interimAlloc_nonneg (x : Fin n → (Fin n → ℝ) → ℝ)
    (hx : ∀ i b, x i b ∈ Icc 0 1) (i : Fin n) (s : ℝ) :
    0 ≤ A.interimAlloc x i s :=
  integral_nonneg fun _ => (hx i _).1

/-- A generic interim allocation is at most one when the underlying allocation rule takes values in
`[0, 1]`. -/
lemma interimAlloc_le_one (x : Fin n → (Fin n → ℝ) → ℝ)
    (hx : ∀ i b, x i b ∈ Icc 0 1) (i : Fin n) (s : ℝ) :
    A.interimAlloc x i s ≤ 1 := by
  calc
    A.interimAlloc x i s ≤ ∫ _, (1 : ℝ) ∂ℙ :=
      integral_mono_of_nonneg
        (ae_of_all _ fun ω => (hx i _).1) (integrable_const 1)
        (ae_of_all _ fun ω => (hx i _).2)
    _ = 1 := by
      rw [integral_const]
      simp [Measure.real, measure_univ]

/-- A generic interim allocation takes values in `[0, 1]` when the underlying allocation rule
does. -/
lemma interimAlloc_mem_Icc (x : Fin n → (Fin n → ℝ) → ℝ)
    (hx : ∀ i b, x i b ∈ Icc 0 1) (i : Fin n) (s : ℝ) :
    A.interimAlloc x i s ∈ Icc 0 1 :=
  ⟨A.interimAlloc_nonneg x hx i s, A.interimAlloc_le_one x hx i s⟩

/-- Interim allocation is measurable in the bidder's reported type. -/
lemma measurable_interimAlloc (x : Fin n → (Fin n → ℝ) → ℝ)
    (hx : ∀ i, Measurable (x i)) (i : Fin n) :
    Measurable (A.interimAlloc x i) := by
  have hg : Measurable
      (fun p : ℝ × Ω => x i (update (A.θ · p.2) i p.1)) :=
    (hx i).comp (A.measurable_update_profile i)
  exact hg.stronglyMeasurable.integral_prod_right'.measurable

/-- A bounded interim allocation is interval-integrable. -/
lemma intervalIntegrable_interimAlloc
    (x : Fin n → (Fin n → ℝ) → ℝ)
    (hx : ∀ i b, x i b ∈ Icc 0 1)
    (hxm : ∀ i, Measurable (x i)) (i : Fin n) (a b : ℝ) :
    IntervalIntegrable (A.interimAlloc x i) volume a b := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := 1) ?_
    (A.measurable_interimAlloc x hxm i).aestronglyMeasurable ?_
  · rw [Real.volume_uIoc]
    exact ENNReal.ofReal_lt_top.ne
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr
      (ae_of_all _ fun s _ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (A.interimAlloc_nonneg x hx i s)]
    exact A.interimAlloc_le_one x hx i s

/-- The auction's interim allocation is measurable in the bidder's reported type. -/
lemma measurable_q (i : Fin n) : Measurable (A.q i) := by
  change Measurable (A.interimAlloc A.rules.x i)
  exact A.measurable_interimAlloc A.rules.x A.rules.x_measurable i

/-- The auction's interim payment is measurable when its ex-post payment rule is measurable. -/
lemma measurable_p (i : Fin n) (ht : Measurable (A.rules.t i)) :
    Measurable (A.p i) := by
  have hg : Measurable
      (fun p : ℝ × Ω => A.rules.t i (update (A.θ · p.2) i p.1)) :=
    ht.comp (A.measurable_update_profile i)
  exact hg.stronglyMeasurable.integral_prod_right'.measurable

private theorem integral_update_aux [HasIndependentTypes A] (i : Fin n)
    {g : (Fin n → ℝ) → ℝ} (hg : Measurable g)
    (hint : Integrable (fun ω => g (A.θ · ω)) ℙ) :
    (𝔼[fun ω => g (A.θ · ω)] =
      𝔼[fun ω => 𝔼[fun ω' => g (update (A.θ · ω') i (A.θ i ω))]]) ∧
      Integrable
        (fun ω => 𝔼[fun ω' => g (update (A.θ · ω') i (A.θ i ω))]) ℙ := by
  let X : Ω → (({i} : Finset (Fin n)) → ℝ) := fun ω k => A.θ k ω
  let T : Finset (Fin n) := Finset.univ.erase i
  let Y : Ω → (T → ℝ) := fun ω k => A.θ k ω
  let combine : (({i} : Finset (Fin n)) → ℝ) →
      (T → ℝ) → (Fin n → ℝ) :=
    fun u y j => if hji : j = i then u ⟨i, Finset.mem_singleton_self i⟩
      else y ⟨j, by simp [T, hji]⟩
  let h := fun u y => g (combine u y)
  have hX : Measurable X := by
    rw [measurable_pi_iff]
    intro k
    exact A.θ_measurable k
  have hY : Measurable Y := by
    rw [measurable_pi_iff]
    intro k
    exact A.θ_measurable k
  have hXY : IndepFun X Y ℙ := by
    dsimp [X, Y, T]
    exact HasIndependentTypes.θ_indep.indepFun_finset
      ({i} : Finset (Fin n)) (Finset.univ.erase i)
      (Finset.disjoint_singleton_left.mpr (Finset.notMem_erase i _))
      A.θ_measurable
  have hcombine : Measurable combine.uncurry := by
    rw [measurable_pi_iff]
    intro j
    by_cases hji : j = i
    · subst j
      dsimp only [combine, Function.uncurry]
      split_ifs with heq
      · exact (measurable_pi_apply
          (⟨i, Finset.mem_singleton_self i⟩ : ({i} : Finset (Fin n)))).comp
            (measurable_fst : Measurable
              (fun p : (({i} : Finset (Fin n)) → ℝ) × (T → ℝ) => p.1))
      · exact (heq rfl).elim
    · dsimp only [combine, Function.uncurry]
      simp only [dif_neg hji]
      change Measurable
        (fun p : (({i} : Finset (Fin n)) → ℝ) × (T → ℝ) =>
          p.2 (⟨j, by simp [T, hji]⟩ : T))
      exact (measurable_pi_apply (⟨j, by simp [T, hji]⟩ : T)).comp
        (measurable_snd : Measurable
          (fun p : (({i} : Finset (Fin n)) → ℝ) × (T → ℝ) => p.2))
  have hh : Measurable h.uncurry := hg.comp hcombine
  have hcross : ∀ ω ω',
      h (X ω) (Y ω') = g (update (A.θ · ω') i (A.θ i ω)) := by
    intro ω ω'
    apply congrArg g
    funext j
    by_cases hji : j = i
    · subst j
      simp [combine, X, Y]
    · simp [combine, X, Y, hji]
  have hint' : Integrable (fun ω => h (X ω) (Y ω)) ℙ := by
    convert hint using 1
    funext ω
    rw [hcross, Function.update_eq_self]
  have heq := MeasureTheory.integral_indep_swap hXY hX hY h hh hint'
  have hint_swap :=
    MeasureTheory.integrable_integral_indep_swap hXY hX hY h hh hint'
  constructor
  · simpa only [hcross, Function.update_eq_self] using heq
  · exact hint_swap.congr
      (ae_of_all ℙ fun ω => by
        apply integral_congr_ae
        exact ae_of_all ℙ fun ω' => hcross ω ω')

/-- Independence lets one replace a bidder's opponents by an independent copy before conditioning
on that bidder's type. -/
theorem integral_eq_integral_update [HasIndependentTypes A] (i : Fin n)
    {g : (Fin n → ℝ) → ℝ} (hg : Measurable g)
    (hint : Integrable (fun ω => g (A.θ · ω)) ℙ) :
    𝔼[fun ω => g (A.θ · ω)] =
      𝔼[fun ω => 𝔼[fun ω' => g (update (A.θ · ω') i (A.θ i ω))]] :=
  (A.integral_update_aux i hg hint).1

/-- Ex-post score times allocation has the same expectation as score times interim allocation. -/
theorem integral_mul_x_eq_integral_mul_q [HasIndependentTypes A] (i : Fin n)
    {φ : ℝ → ℝ} (hφ : Measurable φ)
    (hint : Integrable
      (fun ω => φ (A.θ i ω) * A.rules.x i (A.θ · ω)) ℙ) :
    𝔼[fun ω => φ (A.θ i ω) * A.rules.x i (A.θ · ω)] =
      𝔼[fun ω => φ (A.θ i ω) * A.q i (A.θ i ω)] := by
  have hg : Measurable (fun b : Fin n → ℝ => φ (b i) * A.rules.x i b) :=
    (hφ.comp (measurable_pi_apply i)).mul (A.rules.x_measurable i)
  have heq := A.integral_eq_integral_update i hg hint
  simpa only [Function.update_self, integral_const_mul, q, q_strat, id_eq] using heq

/-- The ex-post/interim bridge expressed against bidder `i`'s value distribution. -/
theorem integral_mul_x_eq_integral_mul_q_valueDistribution
    [HasIndependentTypes A] (i : Fin n) {φ : ℝ → ℝ}
    (hφ : Measurable φ)
    (hint : Integrable
      (fun ω => φ (A.θ i ω) * A.rules.x i (A.θ · ω)) ℙ) :
    𝔼[fun ω => φ (A.θ i ω) * A.rules.x i (A.θ · ω)] =
      ∫ s, φ s * A.q i s ∂(A.valueDistribution i : Measure ℝ) := by
  rw [A.toMeasure_valueDistribution, integral_map (A.θ_measurable i).aemeasurable
    ((hφ.mul (A.measurable_q i)).aestronglyMeasurable)]
  exact A.integral_mul_x_eq_integral_mul_q i hφ hint

/-- A bounded score automatically supplies the integrability needed by the ex-post/interim
allocation bridge. -/
theorem integral_mul_x_eq_integral_mul_q_of_bounded
    [HasIndependentTypes A] [HasBoundedTypes A]
    [A.rules.HasValidAllocation] (i : Fin n) {φ : ℝ → ℝ}
    (hφ : Measurable φ) {C : ℝ}
    (hC : ∀ v ∈ A.interval i, |φ v| ≤ C) :
    𝔼[fun ω => φ (A.θ i ω) * A.rules.x i (A.θ · ω)] =
      𝔼[fun ω => φ (A.θ i ω) * A.q i (A.θ i ω)] := by
  have hφint := A.integrable_comp_θ_of_bounded i hφ hC
  have hxmeas : Measurable
      (fun ω => A.rules.x i (fun j => A.θ j ω)) :=
    (A.rules.x_measurable i).comp A.measurable_profile
  have hxint : Integrable
      (fun ω => φ (A.θ i ω) * A.rules.x i (A.θ · ω)) ℙ :=
    hφint.mul_bdd hxmeas.aestronglyMeasurable (ae_of_all ℙ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (Mechanism.HasValidAllocation.x_range (M := A.rules) i _).1]
      exact (Mechanism.HasValidAllocation.x_range (M := A.rules) i _).2)
  exact A.integral_mul_x_eq_integral_mul_q i hφ hxint

/-- Expected ex-post and interim payments agree. -/
theorem integral_t_eq_integral_p [HasIndependentTypes A] (i : Fin n)
    (ht : Measurable (A.rules.t i))
    (hint : Integrable (fun ω => A.rules.t i (A.θ · ω)) ℙ) :
    𝔼[fun ω => A.rules.t i (A.θ · ω)] =
      𝔼[fun ω => A.p i (A.θ i ω)] := by
  have heq := A.integral_eq_integral_update i ht hint
  simpa only [p, p_strat, id_eq] using heq

/-- Integrability of ex-post payments implies integrability of interim payments evaluated at the
realized type. -/
theorem integrable_p_comp_θ_of_integrable_t [HasIndependentTypes A] (i : Fin n)
    (ht : Measurable (A.rules.t i))
    (hint : Integrable (fun ω => A.rules.t i (A.θ · ω)) ℙ) :
    Integrable (fun ω => A.p i (A.θ i ω)) ℙ := by
  have hs := (A.integral_update_aux i ht hint).2
  simpa only [p, p_strat, id_eq] using hs

/-- Integrating interim payment against the realized type equals expected payment in the bidder's
value distribution. This identity needs no independence assumption. -/
theorem integral_p_comp_θ_eq_expectedPayment [A.rules.HasValidAllocation]
    (i : Fin n) (hp : Measurable (A.p i)) :
    𝔼[fun ω => A.p i (A.θ i ω)] =
      (A.valueDistribution i).expectedPayment
        (A.toBidderProblem id i).toSingleParameterProblem := by
  change (∫ ω, A.p i (A.θ i ω) ∂ℙ) =
    ∫ s, A.p i s ∂(A.valueDistribution i : Measure ℝ)
  rw [A.toMeasure_valueDistribution,
    integral_map (A.θ_measurable i).aemeasurable hp.aestronglyMeasurable]

/-- Expected revenue is also the expectation of the sum of ex-post payments. -/
theorem expectedRevenue_eq_integral_sum_t [NeZero n]
    [HasIndependentTypes A]
    (ht : ∀ i, Measurable (A.rules.t i))
    (hint : ∀ i, Integrable (fun ω => A.rules.t i (A.θ · ω)) ℙ) :
    A.expectedRevenue = 𝔼[fun ω => ∑ i, A.rules.t i (A.θ · ω)] := by
  rw [expectedRevenue,
    integral_finset_sum _ (fun i _ => A.integrable_p_comp_θ_of_integrable_t i (ht i) (hint i)),
    integral_finset_sum _ (fun i _ => hint i)]
  exact Finset.sum_congr rfl fun i _ =>
    (A.integral_t_eq_integral_p i (ht i) (hint i)).symm

/-- Per-bidder type-deviation incentive compatibility implies BIC. This is a theorem rather than an
instance to avoid an instance loop with the converse. -/
theorem bic_of_forall_typeDeviationIC [A.rules.HasValidAllocation]
    (h : ∀ i, (A.toBidderProblem id i).HasTypeDeviationIC) : A.BIC where
  bic i s hs s' hs' := by
    have hi := (h i).typeDeviationIC s hs s' hs'
    simpa only [BidderProblem.payoff, BidderProblem.q, Function.comp_apply,
      toBidderProblem_winProb, toBidderProblem_cost, toBidderProblem_strategy,
      id_eq, U] using hi

/-- Highest-score interim allocation is monotone when the bidder's own score is monotone on its
type interval. -/
theorem interimAlloc_highestScoreAlloc_monotoneOn
    (v : Fin n → ℝ → ℝ) (hv : ∀ j, Measurable (v j)) (i : Fin n)
    (hmono : MonotoneOn (v i) (A.interval i)) :
    MonotoneOn (A.interimAlloc (Mechanism.highestScoreAlloc v) i)
      (A.interval i) := by
  intro t ht t' ht' htt'
  unfold interimAlloc
  have hint : ∀ s, Integrable
      (fun ω => Mechanism.highestScoreAlloc v i (update (A.θ · ω) i s)) ℙ := by
    intro s
    have hupd : Measurable (fun ω => update (A.θ · ω) i s) :=
      (A.measurable_update_profile i).comp
        (measurable_const.prodMk measurable_id)
    apply Integrable.of_bound
      (((Mechanism.measurable_highestScoreAlloc v hv i).comp hupd).aestronglyMeasurable) 1
    exact ae_of_all ℙ fun ω => by
      change |Mechanism.highestScoreAlloc v i (update (A.θ · ω) i s)| ≤ 1
      rw [abs_of_nonneg
        (Mechanism.highestScoreAlloc_nonneg v i _)]
      exact Mechanism.highestScoreAlloc_le_one v i _
  refine integral_mono (hint t) (hint t') fun ω => ?_
  exact Mechanism.highestScoreAlloc_update_le v hmono ht ht' htt'

/-- Highest-score interim allocation is constant on level sets of the own score. -/
theorem interimAlloc_highestScoreAlloc_congr
    (v : Fin n → ℝ → ℝ) (i : Fin n) {t t' : ℝ}
    (h : v i t = v i t') :
    A.interimAlloc (Mechanism.highestScoreAlloc v) i t =
      A.interimAlloc (Mechanism.highestScoreAlloc v) i t' := by
  apply integral_congr_ae
  exact ae_of_all ℙ fun ω => Mechanism.highestScoreAlloc_update_congr v h

end Auction

end
