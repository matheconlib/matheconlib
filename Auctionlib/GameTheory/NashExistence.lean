module

public import Auctionlib.GameTheory.Basic

import Auctionlib.ForMathlib.Schauder

/-!
# Existence of Nash equilibria
This file contains an auto-formalisation of the existence of mixed-strategy Nash equilibria for
finite games. More classic results on the existence of Nash equilibria in other situations will be
added later on.

Currently, the only public declaration in this file is
`GameTheory.Game.exists_isNashEquilibrium_of_finite`; all other declarations are kept private.
-/

namespace GameTheory

/-! ## Nash equilibrium existence via the best-response map -/

section NashExistence

open MeasureTheory Classical

variable {ι : Type} {A : ι → Type} {O : Type}
  [Fintype ι] [DecidableEq ι] [∀ i, Fintype (A i)]
  (G : Game A O) (P : PayoffStructure O ι)

noncomputable def expectedPayoffPure (x : (i : ι) → A i → ℝ) (i : ι) (s : A i) : ℝ :=
  ∑ a : (j : ι) → A j,
    (∏ j ∈ Finset.univ.filter (· ≠ i), x j (a j)) *
    if a i = s then P.payoff i (G.outcome a) else 0

noncomputable def expectedPayoffMixed (x : (i : ι) → A i → ℝ) (i : ι) : ℝ :=
  ∑ a : (j : ι) → A j, (∏ j, x j (a j)) * P.payoff i (G.outcome a)

noncomputable def gain (x : (i : ι) → A i → ℝ) (i : ι) (s : A i) : ℝ :=
  max 0 (expectedPayoffPure G P x i s - expectedPayoffMixed G P x i)

noncomputable def unnormalizedResponse (x : (i : ι) → A i → ℝ) (i : ι) (s : A i) : ℝ :=
  x i s + gain G P x i s

noncomputable def normDenom (x : (i : ι) → A i → ℝ) (i : ι) : ℝ :=
  ∑ s, unnormalizedResponse G P x i s

noncomputable def bestResponseMap (x : (i : ι) → A i → ℝ) : (i : ι) → A i → ℝ :=
  fun i s ↦ unnormalizedResponse G P x i s / normDenom G P x i

lemma gain_nonneg (x : (i : ι) → A i → ℝ) (i : ι) (s : A i) :
    0 ≤ gain G P x i s :=
  le_max_left 0 _

lemma normDenom_eq (x : (i : ι) → A i → ℝ)
    (hx : x ∈ Set.univ.pi (fun i ↦ stdSimplex ℝ (A i))) (i : ι) :
    normDenom G P x i = 1 + ∑ s, gain G P x i s := by
  simp only [normDenom, unnormalizedResponse, Finset.sum_add_distrib,
    (Set.mem_univ_pi.mp hx i).2]

lemma normDenom_ge_one (x : (i : ι) → A i → ℝ)
    (hx : x ∈ Set.univ.pi (fun i ↦ stdSimplex ℝ (A i))) (i : ι) :
    1 ≤ normDenom G P x i := by
  rw [normDenom_eq G P x hx i]
  linarith [Finset.sum_nonneg fun s (_ : s ∈ Finset.univ) ↦ gain_nonneg G P x i s]

lemma bestResponseMap_mapsTo :
    Set.MapsTo (bestResponseMap G P)
      (Set.univ.pi (fun i ↦ stdSimplex ℝ (A i)))
      (Set.univ.pi (fun i ↦ stdSimplex ℝ (A i))) := by
  intro x hx
  simp only [Set.mem_univ_pi] at hx ⊢
  intro i
  have hnd_pos : 0 < normDenom G P x i :=
    one_pos.trans_le <| normDenom_ge_one G P x (Set.mem_univ_pi.mpr hx) i
  refine ⟨fun s ↦ div_nonneg (add_nonneg ((hx i).1 s) (le_max_left 0 _)) hnd_pos.le, ?_⟩
  show ∑ s, unnormalizedResponse G P x i s / normDenom G P x i = 1
  rw [← Finset.sum_div]
  exact div_self hnd_pos.ne'

private lemma continuous_unnormalizedResponse (i : ι) (s : A i) :
    Continuous (fun x ↦ unnormalizedResponse G P x i s) := by
  unfold unnormalizedResponse gain expectedPayoffPure expectedPayoffMixed
  fun_prop

lemma bestResponseMap_continuousOn :
    ContinuousOn (bestResponseMap G P)
      (Set.univ.pi (fun i ↦ stdSimplex ℝ (A i))) := by
  unfold bestResponseMap
  simp_rw [continuousOn_pi]
  intro i s
  exact (continuous_unnormalizedResponse G P i s).continuousOn.div
    (continuous_finset_sum _ fun t _ ↦
      continuous_unnormalizedResponse G P i t).continuousOn
    fun x hx ↦ (one_pos.trans_le (normDenom_ge_one G P x hx i)).ne'

lemma expectedPayoffMixed_eq_sum (x : (i : ι) → A i → ℝ) (i : ι) :
    expectedPayoffMixed G P x i =
    ∑ s, x i s * expectedPayoffPure G P x i s := by
  simp only [expectedPayoffMixed, expectedPayoffPure, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ ↦ by
    simp only [mul_ite, mul_zero, ← mul_assoc]
    rw [Fintype.sum_ite_eq, Finset.filter_ne',
      Finset.mul_prod_erase Finset.univ (fun j ↦ x j (a j)) (Finset.mem_univ i)]

lemma gain_eq_mul_sub (x : (i : ι) → A i → ℝ)
    (hx : x ∈ Set.univ.pi (fun i ↦ stdSimplex ℝ (A i)))
    (hfixed : bestResponseMap G P x = x) (i : ι) (s : A i) :
    gain G P x i s = x i s * (normDenom G P x i - 1) := by
  have hnd_pos := one_pos.trans_le (normDenom_ge_one G P x hx i)
  have key : unnormalizedResponse G P x i s / normDenom G P x i = x i s :=
    congr_fun (congr_fun hfixed i) s
  rw [div_eq_iff hnd_pos.ne'] at key
  simp only [unnormalizedResponse] at key
  linarith

private lemma weighted_avg_lt {α : Type} [Fintype α] (w : α → ℝ) (f : α → ℝ) (c : ℝ)
    (hw_nonneg : ∀ a, 0 ≤ w a) (hw_sum : ∑ a, w a = 1)
    (hcf : ∀ a, 0 < w a → c < f a) (ha : ∃ a, 0 < w a) :
    c < ∑ a, w a * f a := by
  rw [show c = ∑ a : α, w a * c from by rw [← Finset.sum_mul, hw_sum, one_mul]]
  obtain ⟨a₀, ha₀⟩ := ha
  exact Finset.sum_lt_sum
    (fun a _ ↦ by
      rcases (hw_nonneg a).eq_or_lt' with heq | hw_pos
      · simp [heq]
      · exact mul_le_mul_of_nonneg_left (hcf a hw_pos).le (hw_nonneg a))
    ⟨a₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (hcf a₀ ha₀) ha₀⟩

lemma fixedPoint_gains_zero (x : (i : ι) → A i → ℝ)
    (hx : x ∈ Set.univ.pi (fun i ↦ stdSimplex ℝ (A i)))
    (hfixed : bestResponseMap G P x = x)
    (i : ι) (s : A i) : gain G P x i s = 0 := by
  have hxi := Set.mem_univ_pi.mp hx i
  have hgain_eq := gain_eq_mul_sub G P x hx hfixed i
  by_contra h
  have hs_pos := (gain_nonneg G P x i s).lt_of_ne' h
  have hnd_sub : 0 < normDenom G P x i - 1 := by
    rw [normDenom_eq G P x hx i]
    linarith [Finset.sum_pos' (fun t _ ↦ gain_nonneg G P x i t)
      ⟨s, Finset.mem_univ s, hs_pos⟩]
  have hpure_gt (t : A i) (hxt : 0 < x i t) :
      expectedPayoffMixed G P x i < expectedPayoffPure G P x i t := by
    have := hgain_eq t ▸ mul_pos hxt hnd_sub
    simp only [gain, lt_max_iff] at this
    linarith [this.resolve_left (by linarith)]
  obtain ⟨t, ht⟩ : ∃ t, 0 < x i t := by
    by_contra hall
    push_neg at hall
    linarith [hxi.2, Finset.sum_nonpos fun t (_ : t ∈ Finset.univ) ↦ hall t]
  exact (expectedPayoffMixed_eq_sum G P x i ▸
    weighted_avg_lt (x i) _ _ hxi.1 hxi.2 hpure_gt ⟨t, ht⟩).ne rfl

/-! ### Connecting the simplex formulation to the measure-theoretic one -/

private lemma equivStdSimplex_symm_singleton_toReal
    {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α] [Fintype α]
    (w : α → ℝ) (hw : w ∈ stdSimplex ℝ α) (a : α) :
    ((↑(ProbabilityMeasure.equivStdSimplex.symm ⟨w, hw⟩) : Measure α) {a}).toReal = w a := by
  simp [ProbabilityMeasure.equivStdSimplex, Set.indicator]; rfl

variable [∀ i, MeasurableSpace (A i)] [MeasurableSpace O]
  [∀ i, DiscreteMeasurableSpace (A i)] [DiscreteMeasurableSpace O] [G.Measurable]

lemma integral_pi_eq_weighted_sum
    (σ : (j : ι) → ProbabilityMeasure (A j))
    (f : ((j : ι) → A j) → ℝ) :
    ∫ a, f a ∂(ProbabilityMeasure.pi σ) =
    ∑ a : (j : ι) → A j, (∏ j, ((σ j) {a j}).toReal) * f a := by
  rw [integral_fintype f Integrable.of_finite]
  exact Finset.sum_congr rfl fun a _ ↦ by
    rw [Measure.real.eq_1, smul_eq_mul, ProbabilityMeasure.toMeasure_pi,
      Measure.pi_singleton, ENNReal.toReal_prod]
    simp [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]

lemma payoff_as_weighted_sum
    (σ : (j : ι) → ProbabilityMeasure (A j)) (i : ι) :
    P.toExpected.payoff i (G.toMixed.outcome σ) =
    ∑ a : (j : ι) → A j, (∏ j, ((σ j) {a j}).toReal) * P.payoff i (G.outcome a) := by
  simp only [PayoffStructure.toExpected, Game.toMixed_outcome,
    ProbabilityMeasure.toMeasure_map, integral_map G.measurable_outcome.aemeasurable
    Measurable.of_discrete.aestronglyMeasurable, integral_pi_eq_weighted_sum]

lemma payoff_baseline_eq (x : (i : ι) → A i → ℝ)
    (hx_mem : ∀ j, x j ∈ stdSimplex ℝ (A j)) (i : ι) :
    P.toExpected.payoff i (G.toMixed.outcome
      (fun j ↦ ProbabilityMeasure.equivStdSimplex.symm ⟨x j, hx_mem j⟩)) =
    expectedPayoffMixed G P x i := by
  simp only [payoff_as_weighted_sum, expectedPayoffMixed]
  exact Finset.sum_congr rfl fun a _ ↦
    congrArg (· * _) (Finset.prod_congr rfl fun j _ ↦
      equivStdSimplex_symm_singleton_toReal (x j) (hx_mem j) (a j))

lemma prod_update_eq (x : (i : ι) → A i → ℝ)
    (hx_mem : ∀ j, x j ∈ stdSimplex ℝ (A j))
    (i : ι) (μ : ProbabilityMeasure (A i)) (a : (j : ι) → A j) :
    (∏ j, ((Function.update
      (fun j ↦ ProbabilityMeasure.equivStdSimplex.symm ⟨x j, hx_mem j⟩) i μ) j
      {a j}).toReal) =
    (μ {a i}).toReal * ∏ j ∈ Finset.univ.filter (· ≠ i), x j (a j) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  refine congr_arg₂ (· * ·) (by simp [Function.update_self]) ?_
  rw [Finset.filter_ne']
  exact Finset.prod_congr rfl fun j hj ↦ by
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
    exact equivStdSimplex_symm_singleton_toReal (x j) (hx_mem j) (a j)

lemma payoff_deviation_eq (x : (i : ι) → A i → ℝ)
    (hx_mem : ∀ j, x j ∈ stdSimplex ℝ (A j))
    (i : ι) (μ : ProbabilityMeasure (A i)) :
    P.toExpected.payoff i (G.toMixed.outcome
      (Function.update (fun j ↦ ProbabilityMeasure.equivStdSimplex.symm ⟨x j, hx_mem j⟩) i μ)) =
    ∑ s : A i, (μ {s}).toReal * expectedPayoffPure G P x i s := by
  rw [payoff_as_weighted_sum]
  simp_rw [prod_update_eq x hx_mem i μ, expectedPayoffPure, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ ↦ by
    simp_rw [mul_ite, mul_zero, ← mul_assoc]
    rw [Fintype.sum_ite_eq]

lemma nash_from_simplex_le (x : (i : ι) → A i → ℝ)
    (hx : x ∈ Set.univ.pi (fun i ↦ stdSimplex ℝ (A i)))
    (hle : ∀ i (s : A i), expectedPayoffPure G P x i s ≤ expectedPayoffMixed G P x i) :
    G.toMixed.IsNashEquilibrium P.toExpected
      (fun j ↦ ProbabilityMeasure.equivStdSimplex.symm ⟨x j, Set.mem_univ_pi.mp hx j⟩) := by
  intro i μ
  rw [payoff_deviation_eq G P x (Set.mem_univ_pi.mp hx) i μ,
    payoff_baseline_eq G P x (Set.mem_univ_pi.mp hx) i]
  calc ∑ s, (μ {s}).toReal * expectedPayoffPure G P x i s
      ≤ ∑ s, (μ {s}).toReal * expectedPayoffMixed G P x i :=
        Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left (hle i s) ENNReal.toReal_nonneg
    _ = expectedPayoffMixed G P x i := by
        simp_rw [← Finset.sum_mul, ← μ.measureReal_eq_coe_coeFn, sum_measureReal_singleton]
        simp

end NashExistence

@[expose] public section

variable {ι : Type} {A : ι → Type} {O : Type}

lemma Game.exists_isNashEquilibrium_of_finite (G : Game A O) (P : PayoffStructure O ι)
    [∀ i, MeasurableSpace (A i)] [MeasurableSpace O]
    [∀ i, DiscreteMeasurableSpace (A i)] [DiscreteMeasurableSpace O] [G.Measurable]
    [Fintype ι] [DecidableEq ι] [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] :
    ∃ a, G.toMixed.IsNashEquilibrium P.toExpected a := by
  obtain ⟨⟨x, hx⟩, hfixed⟩ := Continuous.exists_fixedPt_of_isConvex_isCompact
    (isCompact_univ_pi fun i ↦ isCompact_stdSimplex (A i))
    (convex_pi fun i _ ↦ convex_stdSimplex ℝ (A i))
    (Set.univ_pi_nonempty_iff.mpr fun i ↦
      ⟨_, (stdSimplex.instNonemptyElemForall (S := ℝ) (X := A i)).some.2⟩)
    ((bestResponseMap_continuousOn G P).mapsToRestrict (bestResponseMap_mapsTo G P))
  have hfixed' : bestResponseMap G P x = x := by
    simpa [Set.MapsTo.restrict] using congr_arg Subtype.val hfixed
  exact ⟨_, nash_from_simplex_le G P x hx fun i s ↦ by
    have h := fixedPoint_gains_zero G P x hx hfixed' i s
    simp only [gain, max_eq_left_iff] at h
    linarith⟩

end

end GameTheory
