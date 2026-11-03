/-
Copyright (c) 2026 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib
public import MathEconLib.ForMathlib.AbsolutelyContinuous

/-!
# Order Statistics

Given `n` values `v 0, v 1, …, v (n-1)`, the k-th order statistic (0-indexed)
is the `(k+1)`-smallest value. This file develops the theory from deterministic
definitions through to the probabilistic CDF/density formulas for i.i.d. random
variables (Section 4 of the reference), and culminates in the revenue equivalence
identity used in auction theory (Section 5.3).

## Main definitions

* `orderStatistics v k`: the `(k+1)`-smallest value of the family `v : Fin n → α`.
  Index `0` gives the minimum, index `n-1` gives the maximum.
* `OrderStatisticsSetup`: bundled setup for `n` i.i.d. real-valued random variables
  with a common density, carrying measurability, independence, identical distribution,
  and absolute continuity hypotheses.

## Main results

### Probabilistic (CDF and density)

* `OrderStatisticsSetup.prob_count_eq`: binomial probability that exactly `l` of `n` i.i.d.
  variables fall below `x`.
* `OrderStatisticsSetup.cdf_val` (Theorem 4.2): CDF of the k-th order statistic,
  `cdf(X_{(k+1)}) = Σ_{l=k+1}^{n} C(n,l) F(x)^l (1-F(x))^{n-l}`.
* `OrderStatisticsSetup.pdf_val` (Corollary 4.3): density of the k-th order statistic,
  `n!/(k!(n-1-k)!) · F(x)^k · (1-F(x))^{n-1-k} · f(x)`.
* `OrderStatisticsSetup.identDistrib_val`: if two setups have identically distributed
  base variables, then their k-th order statistics are identically distributed.

### Expected value and integration by parts

* `OrderStatisticsSetup.expected_val_eq_sub_integral_cdf`: layer-cake representation,
  `E[X_{(k)}] = b - ∫_{a}^{b} cdf(X_{(k)}) dx`.
* `OrderStatisticsSetup.expected_val`: expected value of the k-th order statistic
  for `n` i.i.d. random variables with `F(a) = 0`, `F(b) = 1`:
  `E[X_{(k)}] = n!/(k!(n-1-k)!) · ∫ₐᵇ ψ · F(ψ)^k · (1-F(ψ))^{n-1-k} · f(ψ) dψ`.
* `OrderStatisticsSetup.integral_cdf_pow`: integration by parts for `∫ₐˢ F(ψ)^m dψ`.
* `OrderStatisticsSetup.expected_second_highest`: for `n ≥ 2` i.i.d. random variables,
  `E[X_{(n-1)}] = n · E[s · F(s)^{n-1} - ∫ₐˢ F(ψ)^{n-1} dψ]`.
  This is the key identity underlying the Revenue Equivalence Theorem (Theorem 5.3).

-/

namespace MathEconLib

@[expose] public section

open Finset Nat ENNReal

/-! ## Definition and basic properties -/

section orderStatistics_def

variable {α : Type*} [LinearOrder α] {n : ℕ}

/-- The k-th order statistic (0-indexed) of `n` values.

`orderStatistics v k` is the `(k+1)`-smallest among `v 0, …, v (n-1)`.
In particular, `orderStatistics v 0` is the minimum and
`orderStatistics v ⟨n-1, _⟩` is the maximum.

This corresponds to `X_{(k+1)}` in the 1-indexed convention of the reference. -/
noncomputable def orderStatistics (v : Fin n → α) (k : Fin n) : α :=
  Finset.univ.val.map v |>.sort (· ≤ ·) |>.get ⟨k, by simp⟩

/-- The order statistics form a monotone (non-decreasing) sequence. -/
lemma orderStatistics_mono (v : Fin n → α) : Monotone (orderStatistics v) := by
  intro ⟨i, hi⟩ ⟨j, hj⟩ hij
  simpa only [orderStatistics] using (List.sortedLE_iff_pairwise.mpr (Multiset.pairwise_sort _ _))
    |>.monotone_get hij

/-- Every order-statistic value appears among the original sample values. -/
lemma orderStatistics_mem_range (v : Fin n → α) (k : Fin n) :
    orderStatistics v k ∈ Set.range v := by
  have h1 : orderStatistics v k ∈ (Finset.univ.val.map v |>.sort (· ≤ ·) : Multiset α) := by
    simpa only [orderStatistics, List.get_eq_getElem, Multiset.mem_coe] using
      List.getElem_mem (by simp)
  rw [Multiset.sort_eq] at h1
  obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp h1
  grind

end orderStatistics_def

/-! ## Counting characterization -/

section Counting

variable {α : Type*} [LinearOrder α] {n : ℕ}

/-- `orderStatistics v k ≤ x` iff at least `k + 1` of the values `v i` are `≤ x`. -/
theorem orderStatistics_le_iff (v : Fin n → α) (k : Fin n) (x : α) :
    orderStatistics v k ≤ x ↔
      k.val + 1 ≤ (Finset.univ.filter (fun i => v i ≤ x)).card := by
  set L := Finset.univ.val.map v |>.sort (· ≤ ·) with hL_def
  have hLen : L.length = n := by simp [L]
  have hSorted : L.SortedLE := List.sortedLE_iff_pairwise.mpr <| Multiset.pairwise_sort _ _
  rw [show (Finset.univ.filter (v · ≤ x)).card = (L.filter (· ≤ x)).length by
    simpa [show Finset.univ.val.map v = (L : Multiset α) from (Multiset.sort_eq _ _).symm,
        Multiset.coe_countP, List.countP_eq_length_filter, Finset.card_def, Finset.filter_val] using
        Multiset.countP_map v Finset.univ.val (· ≤ x) |>.symm]
  rw [orderStatistics]
  constructor
  · intro hle
    have h_take_sat : ∀ a ∈ L.take (k.val + 1), a ≤ x := by
      intro a ha
      obtain ⟨⟨j, hj⟩, rfl⟩ := List.mem_iff_get.mp ha
      have hj' : j ≤ k.val := by
        rw [List.length_take, min_eq_left (by omega)] at hj; omega
      rw [show (L.take (k.val + 1)).get ⟨j, hj⟩ = L.get ⟨j, by omega⟩ from List.getElem_take]
      exact le_trans (hSorted.monotone_get (Fin.mk_le_mk.mpr hj')) hle
    have h_filter_take : (L.take (k.val + 1)).filter (· ≤ x) = L.take (k.val + 1) :=
      List.filter_eq_self.mpr (by simpa [decide_eq_true_eq] using h_take_sat)
    have h_sub : L.take (k.val + 1) |>.Sublist <| L.filter (· ≤ x) := by
      rw [← h_filter_take]; exact (L.take_sublist (k.val + 1)).filter _
    grind
  · intro hlen
    by_contra! hc
    have h_drop_none : ∀ a ∈ L.drop k.val, ¬(a ≤ x) := by
      intro a ha hax
      obtain ⟨⟨j, hj⟩, rfl⟩ := List.mem_iff_get.mp ha
      simp only [List.get_eq_getElem, List.getElem_drop] at hax
      exact not_le.mpr (lt_of_lt_of_le hc (hSorted.monotone_get
        (Fin.mk_le_mk.mpr (by omega)))) hax
    have h_split : L.filter (· ≤ x) =
        (L.take k.val).filter (· ≤ x) ++ (L.drop k.val).filter (· ≤ x) := by
      rw [← List.filter_append, List.take_append_drop]
    have h_drop_nil : (L.drop k.val).filter (· ≤ x) = [] :=
      List.filter_eq_nil_iff.mpr (by simpa [decide_eq_true_eq] using h_drop_none)
    rw [h_split, h_drop_nil, List.append_nil] at hlen
    have := calc ((L.take k.val).filter (· ≤ x)).length
        _ ≤ (L.take k.val).length := List.length_filter_le _ _
        _ = min k.val L.length := by rw [List.length_take]
        _ = k.val := min_eq_left (by omega)
    omega

end Counting

/-! ## CDF of the k-th order statistic -/

section Probability

open MeasureTheory ProbabilityTheory

/-- Setup for `n` i.i.d. real-valued random variables with a common density. -/
structure OrderStatisticsSetup (Ω : Type*) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (n : ℕ) where
  /-- The random variables -/
  X : Fin n → Ω → ℝ
  /-- Each Xᵢ is measurable -/
  X_measurable : ∀ i, Measurable (X i)
  /-- The Xᵢ are mutually independent -/
  X_indep : iIndepFun X ℙ
  /-- The Xᵢ are identically distributed -/
  X_ident : ∀ i j, IdentDistrib (X i) (X j) ℙ ℙ
  /-- Each Xᵢ has a density w.r.t. Lebesgue measure -/
  X_hasPDF : ∀ i, HasPDF (X i) ℙ volume

namespace OrderStatisticsSetup

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} (S : OrderStatisticsSetup Ω n)

/-- The k-th order statistic as a random variable. -/
noncomputable def val (k : Fin n) (ω : Ω) : ℝ :=
  orderStatistics (fun i => S.X i ω) k

/-- The set `{ω | #{i | X i ω ≤ x} = l}` is measurable. -/
theorem measurableSet_count_eq (l : ℕ) (x : ℝ) :
    MeasurableSet {ω : Ω | #(Finset.univ.filter (S.X · ω ≤ x)) = l} := by
  suffices h : Measurable fun ω : Ω => #(Finset.univ.filter (S.X · ω ≤ x)) from
    h (measurableSet_singleton l)
  simp_rw [Finset.card_filter]
  exact Finset.measurable_sum _ fun i _ =>
    Measurable.ite ((S.X_measurable i) measurableSet_Iic) measurable_const measurable_const

/-- The k-th order statistic is a measurable function.

We show `f ⁻¹' Iic x` is measurable for every `x` using `orderStatistics_le_iff`:
the preimage equals `{ω | k+1 ≤ #{i | X i ω ≤ x}}`, which is measurable because
the counting function is measurable. -/
theorem measurable_val (k : Fin n) : Measurable <| S.val k := by
  apply measurable_of_Iic
  intro x
  rw [show S.val k ⁻¹' Set.Iic x =
      {ω | k.val + 1 ≤ #(Finset.univ.filter (S.X · ω ≤ x))} by
    ext; simpa [val] using orderStatistics_le_iff _ k x]
  have h_count : Measurable fun ω : Ω => #(Finset.univ.filter (S.X · ω ≤ x)) := by
    simp_rw [Finset.card_filter]
    exact Finset.measurable_sum _ fun i _ => Measurable.ite ((S.X_measurable i) measurableSet_Iic)
        measurable_const measurable_const
  exact h_count measurableSet_Ici

theorem map_val_absolutelyContinuous (k : Fin n) :
    Measure.map (S.val k) ℙ ≪ volume := by
  refine Measure.AbsolutelyContinuous.mk fun A hAmeas hA => ?_
  rw [Measure.map_apply (S.measurable_val k) hAmeas]
  have h_sub : S.val k ⁻¹' A ⊆ ⋃ j, S.X j ⁻¹' A := fun ω hω => by
    obtain ⟨j, hj⟩ := orderStatistics_mem_range (fun i => S.X i ω) k
    exact Set.mem_iUnion.mpr ⟨j, by grind [show S.val k ω = S.X j ω from hj.symm]⟩
  exact le_antisymm (calc ℙ (S.val k ⁻¹' A)
    _ ≤ ℙ (⋃ j, S.X j ⁻¹' A) := measure_mono h_sub
    _ ≤ ∑' j, ℙ (S.X j ⁻¹' A) := measure_iUnion_le _
    _ = ∑' j, (Measure.map (S.X j) ℙ) A := by
      congr 1; ext j; rw [Measure.map_apply (S.X_measurable j) hAmeas]
    _ = 0 := by simp [fun j => (S.X_hasPDF j).absolutelyContinuous hA]) <| bot_le

/-- The k-th order statistic has a density (PDF) w.r.t. Lebesgue measure. -/
noncomputable instance hasPDF_val (k : Fin n) : HasPDF (S.val k) ℙ volume where
  aemeasurable' := (S.measurable_val k).aemeasurable
  haveLebesgueDecomposition' := inferInstance
  absolutelyContinuous' := S.map_val_absolutelyContinuous k

-- Compatibility name; Mathlib now supplies the instance.
theorem isProbabilityMeasure_map_val (k : Fin n) :
    IsProbabilityMeasure (Measure.map (S.val k) ℙ) :=
  inferInstance

/-- Tail expectation formula for order statistics.

For a.s. bounded i.i.d. random variables `X_i ∈ [a, b]`:
  `E[X_{(k+1)}] = b - ∫ₐᵇ F_{(k+1)}(x) dx`
where `F_{(k+1)}` is the CDF of the `(k+1)`-smallest value. -/
theorem expected_val_eq_sub_integral_cdf (k : Fin n) {a b : ℝ} (hab : a ≤ b)
    (hbounded : ∀ i, ∀ᵐ ω, S.X i ω ∈ Set.Icc a b) :
    𝔼[S.val k] = b - ∫ x in a..b, cdf (Measure.map (S.val k) ℙ) x := by
  have h_cdf : ∀ x, cdf (Measure.map (S.val k) ℙ) x =
      Measure.real ℙ (S.val k ⁻¹' Set.Iic x) := fun x => by
    rw [cdf_eq_real, measureReal_def,
      Measure.map_apply (S.measurable_val k) measurableSet_Iic, ← measureReal_def]
  simp_rw [h_cdf]
  delta Measure.real
  have val_bdd : ∀ᵐ ω, a ≤ S.val k ω ∧ S.val k ω ≤ b := by
    filter_upwards [ae_all_iff.mpr hbounded] with ω hω
    obtain ⟨i, hi⟩ := orderStatistics_mem_range (fun j => S.X j ω) k
    rw [show S.val k ω = S.X i ω from hi.symm]
    exact hω i
  have val_int : Integrable (S.val k) ℙ :=
    integrable_const (max |a| |b|) |>.mono' (S.measurable_val k).aestronglyMeasurable <| by
      filter_upwards [val_bdd] with ω ⟨ha, hb⟩
      simpa only [Real.norm_eq_abs, abs_le] using ⟨by linarith [neg_abs_le a, le_max_left |a| |b|],
        by linarith [le_abs_self b, le_max_right |a| |b|]⟩
  have val_int' : Integrable (fun ω => b - S.val k ω) ℙ := (integrable_const b).sub val_int
  have val_nonneg : 0 ≤ᵐ[ℙ] fun ω => b - S.val k ω := by
    filter_upwards [val_bdd] with ω ⟨_, hb⟩
    rw [Pi.zero_apply]
    linarith
  have val_bdd : (fun ω => b - S.val k ω) ≤ᵐ[ℙ] fun _ => b - a := by
    filter_upwards [val_bdd] with ω ⟨ha, _⟩
    linarith
  have eq1 := val_int'.integral_eq_integral_Ioc_meas_le val_nonneg val_bdd
  have eq2 t : Measure.real ℙ {ω : Ω | t ≤ b - S.val k ω} =
      Measure.real ℙ (S.val k ⁻¹' Set.Iic (b - t)) := by
    rw [show {ω : Ω | t ≤ b - S.val k ω} = S.val k ⁻¹' Set.Iic (b - t) by grind]
  have eq3 := intervalIntegral.integral_comp_sub_left (a := 0) (b := b - a)
    (fun x => Measure.real ℙ (S.val k ⁻¹' Set.Iic x)) b
  simp_rw [show b - (b - a) = a by ring, show b - 0 = b by ring, Measure.real_def] at eq3
  simp_rw [eq2, Measure.real_def] at eq1
  rw [← intervalIntegral.integral_of_le (show 0 ≤ b - a by linarith), eq3] at eq1
  have eq4 : ∫ ω, (b - S.val k ω) = b - ∫ ω, S.val k ω := by
    rw [integral_sub (integrable_const b) val_int, integral_const,
        Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  linarith

/-- For a fixed subset `T ⊆ Fin n`, the probability that exactly `T`'s indices
satisfy `X_i ω ≤ x` (and the rest satisfy `X_i ω > x`) equals `F(x)^|T| · (1 - F(x))^{n - |T|}`. -/
theorem prob_iInter_inter_iInter_eq (i₀ : Fin n) (T : Finset (Fin n)) (x : ℝ) :
    Measure.real ℙ
      ((⋂ i ∈ T, {ω : Ω | S.X i ω ≤ x}) ∩ (⋂ i ∉ T, {ω : Ω | ¬ S.X i ω ≤ x})) =
    cdf (Measure.map (S.X i₀) ℙ) x ^ T.card *
      (1 - cdf (Measure.map (S.X i₀) ℙ) x) ^ (n - T.card) := by
  set F := cdf (Measure.map (S.X i₀) ℙ) x
  set A : Fin n → Set ℝ := fun i => if i ∈ T then Set.Iic x else Set.Ioi x
  rw [show (⋂ i ∈ T, {ω : Ω | S.X i ω ≤ x}) ∩ (⋂ i ∉ T, {ω : Ω | ¬ S.X i ω ≤ x}) =
      ⋂ i, S.X i ⁻¹' A i by simpa [Set.ext_iff] using by grind]
  have h_ms i :
      MeasurableSet[(inferInstance : MeasurableSpace ℝ).comap (S.X i)] (S.X i ⁻¹' A i) := by
    rw [MeasurableSpace.measurableSet_comap]
    exact ⟨A i, by simp only [A]; split_ifs <;> measurability, rfl⟩
  rw [Measure.real, congr($(S.X_indep.meas_iInter h_ms).toReal)]
  set p := ENNReal.ofReal F
  have h_in : ∀ i ∈ T, ℙ (S.X i ⁻¹' A i) = p := by
    intro i hi
    simp only [A, hi, ite_true]
    rw [← Measure.map_apply (S.X_measurable i) measurableSet_Iic, (S.X_ident i i₀).map_eq]
    exact (ofReal_cdf _ x).symm
  have h_out : ∀ i ∉ T, ℙ (S.X i ⁻¹' A i) = 1 - p := by
    intro i hi
    simp only [A, hi, ite_false]
    rw [show S.X i ⁻¹' Set.Ioi x = (S.X i ⁻¹' Set.Iic x)ᶜ by ext ω; simp [Set.mem_Ioi, Set.mem_Iic,
        not_le], measure_compl ((S.X_measurable i) measurableSet_Iic) (measure_ne_top ℙ _),
        measure_univ]
    congr 1
    rw [← Measure.map_apply (S.X_measurable i) measurableSet_Iic, (S.X_ident i i₀).map_eq]
    exact (ofReal_cdf _ x).symm
  rw [← Finset.prod_sdiff (Finset.subset_univ T),
      Finset.prod_congr rfl (fun i hi => h_out i (Finset.mem_sdiff.mp hi).2),
      Finset.prod_congr rfl h_in, Finset.prod_const, Finset.prod_const]
  have hp_real : p.toReal = F := ENNReal.toReal_ofReal <| cdf_nonneg _ _
  have hq_real : (1 - p).toReal = 1 - F := by
    rw [ENNReal.toReal_sub_of_le (ENNReal.ofReal_le_one.mpr (cdf_le_one _ _)) ENNReal.one_ne_top,
      hp_real]
    simp
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow, hp_real, hq_real]
  simpa [Finset.card_sdiff] using by ring

/-- Binomial probability formula: for `n` i.i.d. random variables, the probability that
exactly `l` of them fall in `Set.Iic x` equals `C(n,l) · F(x)^l · (1-F(x))^{n-l}`. -/
theorem prob_count_eq (i₀ : Fin n) (l : ℕ) (x : ℝ) :
    Measure.real ℙ {ω : Ω | #(Finset.univ.filter (S.X · ω ≤ x)) = l} =
      (n.choose l : ℝ) * cdf (Measure.map (S.X i₀) ℙ) x ^ l *
      (1 - cdf (Measure.map (S.X i₀) ℙ) x) ^ (n - l) := by
  set F := cdf (Measure.map (S.X i₀) ℙ) x
  set E : Finset (Fin n) → Set Ω := fun T =>
    (⋂ i ∈ T, {ω : Ω | S.X i ω ≤ x}) ∩ (⋂ i ∉ T, {ω : Ω | ¬ S.X i ω ≤ x})
  have h_E_iff T ω :  ω ∈ E T ↔ Finset.univ.filter (fun i => S.X i ω ≤ x) = T := by
    constructor
    · rintro ⟨hω_in, hω_out⟩
      ext i
      simpa using ⟨fun h => by_contra fun h' => Set.mem_iInter₂.mp hω_out i h' h,
        fun h => Set.mem_iInter₂.mp hω_in i h⟩
    · intro h_eq
      exact ⟨Set.mem_iInter₂.mpr fun i h => by rw [← h_eq] at h; exact (Finset.mem_filter.mp h).2,
        Set.mem_iInter₂.mpr fun i hi h => hi
          (by rw [← h_eq]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)⟩
  have h_decomp : {ω : Ω | #(Finset.univ.filter (S.X · ω ≤ x)) = l} =
      ⋃ T ∈ Finset.univ.powersetCard l, E T := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hω
      exact Set.mem_iUnion₂.mpr ⟨univ.filter (S.X · ω ≤ x), Finset.mem_powersetCard.mpr
        ⟨Finset.filter_subset _ _, hω⟩, (h_E_iff _ ω).mpr rfl⟩
    · intro hω
      obtain ⟨T, hT, hωT⟩ := Set.mem_iUnion₂.mp hω
      rw [(h_E_iff T ω).mp hωT]
      exact (Finset.mem_powersetCard.mp hT).2
  have h_disj : Set.PairwiseDisjoint ((Finset.univ : Finset (Fin n)).powersetCard l) E := by
    intro T₁ _ T₂ _ hne
    exact Set.disjoint_left.mpr fun ω hω₁ hω₂ => hne <| ((h_E_iff T₁ ω).mp hω₁).symm.trans <|
      (h_E_iff T₂ ω).mp hω₂
  have h_meas : ∀ T ∈ Finset.univ.powersetCard l, MeasurableSet (E T) := by
    intro T _
    apply MeasurableSet.inter <;>
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => by
      first | exact (S.X_measurable i) measurableSet_Iic |
      exact ((S.X_measurable i) measurableSet_Iic).compl
  rw [h_decomp, Measure.real, measure_biUnion_finset h_disj h_meas,
    ENNReal.toReal_sum (fun T _ => measure_ne_top ℙ _)]
  have h_each : ∀ T ∈ Finset.univ.powersetCard l,
      Measure.real ℙ (E T) = F ^ l * (1 - F) ^ (n - l) := by
    intro T hT
    have hT_card := (Finset.mem_powersetCard.mp hT).2
    simp only [E]
    rw [S.prob_iInter_inter_iInter_eq i₀ T x, hT_card]
  delta Measure.real at h_each
  rw [Finset.sum_congr rfl h_each, Finset.sum_const,
      Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/--
For `n` i.i.d. random variables with common CDF `F`, the CDF of the `(k+1)`-smallest
(0-indexed `k`) is:
  `P(X_{(k+1)} ≤ x) = ∑_{l=k+1}^{n} C(n,l) · F(x)^l · (1 − F(x))^{n−l}`
where `F = cdf (Measure.map (X₀) ℙ)` -/
theorem cdf_val (i₀ : Fin n) (k : Fin n) (x : ℝ) :
    cdf (Measure.map (S.val k) ℙ) x =
    ∑ l ∈ Finset.Icc (k.val + 1) n,
      n.choose l * cdf (Measure.map (S.X i₀) ℙ) x ^ l *
      (1 - cdf (Measure.map (S.X i₀) ℙ) x) ^ (n - l) := by
  rw [cdf_eq_real, measureReal_def,
    Measure.map_apply (S.measurable_val k) measurableSet_Iic, ← measureReal_def]
  rw [show S.val k ⁻¹' Set.Iic x = {ω | k.val + 1 ≤ #(Finset.univ.filter (S.X · ω ≤ x))} by
    ext ω; simpa [val] using orderStatistics_le_iff _ k x,
    show {ω : Ω | k.val + 1 ≤ #(Finset.univ.filter (S.X · ω ≤ x))} =
      ⋃ l ∈ Finset.Icc (k.val + 1) n, {ω : Ω | #(Finset.univ.filter (S.X · ω ≤ x)) = l} by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_Icc, exists_prop]
    constructor
    · intro h
      exact ⟨_, ⟨h, (Finset.card_filter_le _ _).trans (by simp)⟩, rfl⟩
    · rintro ⟨l, ⟨hlo, -⟩, heq⟩; omega]
  have h_disj : Set.PairwiseDisjoint (Finset.Icc (k.val + 1) n)
      (fun l => {ω : Ω | #(Finset.univ.filter (S.X · ω ≤ x)) = l}) := by
    intro l₁ _ l₂ _ hne; grind
  delta Measure.real
  rw [measure_biUnion_finset h_disj (fun l _ => S.measurableSet_count_eq l x),
    ENNReal.toReal_sum (fun l _ => measure_ne_top ℙ _)]
  exact Finset.sum_congr rfl (fun l _ => S.prob_count_eq i₀ l x)

/-- The derivative of the binomial tail sum `B(p) = Σ_{l=k+1}^{n} C(n,l) p^l (1-p)^{n-l}`
telescopes to `B'(p) = n!/(k!(n-1-k)!) · p^k · (1-p)^{n-1-k}`. -/
theorem hasDerivAt_binomial_tail_sum (k : Fin n) (p : ℝ) :
    HasDerivAt
      (fun q : ℝ => ∑ l ∈ Finset.Icc (k.val + 1) n, n.choose l * q ^ l * (1 - q) ^ (n - l))
      ((n ! / (k.1 ! * (n - 1 - k) !)) * p ^ k.1 * (1 - p) ^ (n - 1 - k.val))
      p := by
  let g : ℕ → ℝ := fun m => ((n - 1).choose m) * p ^ m * (1 - p) ^ (n - 1 - m)
  have eq1 : ∀ l ∈ Finset.Icc (k.val + 1) n,
      HasDerivAt (fun q : ℝ => n.choose l * q ^ l * (1 - q) ^ (n - l))
      (n * (g (l - 1) - g l)) p := by
    intro l hl
    have hl_range := Finset.mem_Icc.mp hl
    have hl_pos : 1 ≤ l := by omega
    have hl_le : l ≤ n := hl_range.2
    have h_raw := hasDerivAt_pow l p |>.mul (hasDerivAt_id' p |>.const_sub 1 |>.pow (n - l))
      |>.const_mul (n.choose l : ℝ)
    have h_fn : HasDerivAt (fun q : ℝ => n.choose l * q ^ l * (1 - q) ^ (n - l))
        (n.choose l * (l * p ^ (l - 1) * (1 - p) ^ (n - l) +
          p ^ l * ((n - l : ℕ) * (1 - p) ^ (n - l - 1) * (-1)))) p := by
      convert h_raw using 1; ext q; simp only [Pi.mul_apply, Pi.pow_apply]; ring
    suffices h_eq : n.choose l * (l * p ^ (l - 1) * (1 - p) ^ (n - l) +
        p ^ l * ((n - l : ℕ) * (1 - p) ^ (n - l - 1) * (-1))) =
        n * (g (l - 1) - g l) by rwa [h_eq] at h_fn
    have h_id1 : n.choose l * l = n * (n - 1).choose (l - 1) := by
      have ineq := Nat.add_one_mul_choose_eq (n - 1) (l - 1)
      rw [show (n - 1) + 1 = n from by omega, show (l - 1) + 1 = l from by omega] at ineq
      linarith
    have h_id2 : n.choose l * (n - l) = n * (n - 1).choose l := by
      by_cases hln : l = n
      · simp [hln, mul_zero, Nat.choose_eq_zero_of_lt (show n - 1 < n from by omega)]
      · have h2 := Nat.add_one_mul_choose_eq (n - 1) l
        rw [show (n - 1) + 1 = n from by omega] at h2
        linarith [Nat.choose_succ_right_eq n l]
    have h_exp1 : n - 1 - (l - 1) = n - l := by omega
    have h_exp2 : n - 1 - l = n - l - 1 := by omega
    simp only [g]
    rw [h_exp1, h_exp2]
    have h_id1r : (n.choose l : ℝ) * l = n * (n - 1).choose (l - 1) := by
      exact_mod_cast h_id1
    have h_id2r : (n.choose l : ℝ) * (n - l : ℕ) = n * (n - 1).choose l := by
      exact_mod_cast h_id2
    linear_combination
      h_id1r * (p ^ (l - 1) * (1 - p) ^ (n - l)) -
      h_id2r * (p ^ l * (1 - p) ^ (n - l - 1))
  have eq2 := HasDerivAt.fun_sum eq1
  suffices ∑ l ∈ Finset.Icc (k.val + 1) n, n * (g (l - 1) - g l) =
      n ! / (k.val ! * (n - 1 - k.val) !) *
        p ^ k.val * (1 - p) ^ (n - 1 - k.val) by rwa [this] at eq2
  rw [← Finset.mul_sum]
  have h_reindex : ∑ l ∈ Finset.Icc (k.val + 1) n, (g (l - 1) - g l) =
      ∑ m ∈ Finset.Ico k.val n, (g m - g (m + 1)) := by
    have h_set : Finset.Icc (k.val + 1) n =
        (Finset.Ico k.val n).map ⟨Nat.succ, Nat.succ_injective⟩ := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_Ico,
        Function.Embedding.coeFn_mk]; constructor
      · intro ⟨hlo, hhi⟩; exact ⟨x - 1, ⟨by omega, by omega⟩, by omega⟩
      · rintro ⟨y, ⟨hlo, hhi⟩, rfl⟩; omega
    rw [h_set, Finset.sum_map]
    congr 1
  rw [h_reindex, show ∑ m ∈ Finset.Ico k.val n, (g m - g (m + 1)) = g k.val - g n by
    simp_rw [show ∀ m, g m - g (m + 1) = -(g (m + 1) - g m) from fun _ => by ring,
      Finset.sum_neg_distrib, Finset.sum_Ico_sub g (show k.val ≤ n from by omega), neg_sub]]
  simp only [sub_zero, g,
    show g n = 0 by have := k.isLt; simp [Nat.choose_eq_zero_of_lt (by omega : n - 1 < n), g]]
  have eq3 := Nat.choose_mul_factorial_mul_factorial (show k.val ≤ n - 1 from by omega)
  have eq4 : n * (n - 1)! = n ! := by
    have : k.val < n := k.isLt
    have h := Nat.factorial_succ (n - 1)
    rw [show (n - 1) + 1 = n from by omega] at h
    linarith
  have eq5 : (n : ℝ) * ((n - 1).choose k.val) =
      n ! / (k.val ! * (n - 1 - k.val) !) := by
    rw [eq_div_iff (show (0 : ℝ) < k.val ! * (n - 1 - k.val) ! from by positivity).ne']
    push_cast [← eq3, ← eq4]
    ring
  linear_combination eq5 * (p ^ k.val * (1 - p) ^ (n - 1 - k.val))

/-- If two `OrderStatisticsSetup`s have identically distributed base random variables
(`X₀` has the same law), then the k-th order statistics are identically distributed.

The proof uses `cdf_orderStatistics`: the CDF of `orderStat k` is determined entirely
by the common CDF `F = cdf (Measure.map (X 0) ℙ)`. Since `IdentDistrib` gives
`Measure.map (S₁.X 0) ℙ = Measure.map (S₂.X 0) ℙ`, both order statistics have
the same CDF, hence the same distribution (by `Measure.eq_of_cdf`). -/
theorem identDistrib_val
    {Ω₁ : Type*} [MeasureSpace Ω₁] [IsProbabilityMeasure (ℙ : Measure Ω₁)]
    {Ω₂ : Type*} [MeasureSpace Ω₂] [IsProbabilityMeasure (ℙ : Measure Ω₂)]
    (S₁ : OrderStatisticsSetup Ω₁ n) (S₂ : OrderStatisticsSetup Ω₂ n)
    (hident : ∀ i j, IdentDistrib (S₁.X i) (S₂.X j) ℙ ℙ)
    (k : Fin n) :
    IdentDistrib (S₁.val k) (S₂.val k) ℙ ℙ where
  aemeasurable_fst := (S₁.measurable_val k).aemeasurable
  aemeasurable_snd := (S₂.measurable_val k).aemeasurable
  map_eq := MeasureTheory.Measure.eq_of_cdf _ _ <| StieltjesFunction.ext fun x => by
    rw [S₁.cdf_val k k x, S₂.cdf_val k k x, (hident k k).map_eq]

/--
If the common distribution has density `f` w.r.t. Lebesgue measure, then the
`(k+1)`-smallest order statistic has density:
  `f_{X_{(k+1)}}(x) = n! / (k! · (n-1-k)!) · F(x)^k · (1-F(x))^{n-1-k} · f(x)` -/
theorem pdf_val (i₀ : Fin n) (k : Fin n) :
    pdf (S.val k) ℙ volume =ᵐ[volume] fun x =>
    ENNReal.ofReal (n ! / (k ! * (n - 1 - k.val) !) *
      cdf (Measure.map (S.X i₀) ℙ) x ^ k.val *
      (1 - cdf (Measure.map (S.X i₀) ℙ) x) ^ (n - 1 - k.val)) *
      pdf (S.X i₀) ℙ volume x := by
  have cdf_eq : cdf (Measure.map (S.val k) ℙ) =
      (fun q => ∑ l ∈ Finset.Icc (k.val + 1) n,
        (n.choose l : ℝ) * q ^ l * (1 - q) ^ (n - l)) ∘ cdf (Measure.map (S.X i₀) ℙ) := by
    ext y; grind [S.cdf_val i₀ k y]
  have deriv_k : ∀ᵐ x, HasDerivAt (cdf (Measure.map (S.val k) ℙ))
      ((Measure.map (S.val k) ℙ).rnDeriv volume x).toReal x := by
    simpa [measure_cdf] using cdf (Measure.map (S.val k) ℙ) |>.ae_hasDerivAt
  have deriv_F : ∀ᵐ x, HasDerivAt (cdf (Measure.map (S.X i₀) ℙ))
        ((Measure.map (S.X i₀) ℙ).rnDeriv volume x).toReal x := by
    simpa [measure_cdf] using cdf (Measure.map (S.X i₀) ℙ) |>.ae_hasDerivAt
  have fin_k := (Measure.map (S.val k) ℙ).rnDeriv_lt_top volume
  have fin_0 := (Measure.map (S.X i₀) ℙ).rnDeriv_lt_top volume
  filter_upwards [deriv_k, deriv_F, fin_k, fin_0] with x hK hF hfk hf0
  rw [cdf_eq] at hK
  have eq0 := hK.unique <| hasDerivAt_binomial_tail_sum k (cdf (Measure.map (S.X i₀) ℙ) x)
    |>.comp x hF
  have hw_nn : 0 ≤ n ! / (k.val ! * (n - 1 - k.val) !) *
      cdf (Measure.map (S.X i₀) ℙ) x ^ k.val *
      (1 - cdf (Measure.map (S.X i₀) ℙ) x) ^ (n - 1 - k.val) :=
    mul_nonneg (mul_nonneg (div_nonneg (Nat.cast_nonneg' _)
      (mul_nonneg (Nat.cast_nonneg' _) (Nat.cast_nonneg' _)))
      (pow_nonneg (cdf_nonneg _ _) _))
      (pow_nonneg (sub_nonneg.mpr (cdf_le_one _ _)) _)
  simp only [pdf_def]
  rw [← ENNReal.ofReal_toReal hfk.ne, eq0, ENNReal.ofReal_mul hw_nn, ENNReal.ofReal_toReal hf0.ne]

-- theorem absolutelyContinuousOnInterval_cdf (i₀ : Fin n) (a s : ℝ)
--     (F_a : cdf (Measure.map (S.X i₀) ℙ) a = 0) :
--     AbsolutelyContinuousOnInterval (cdf (Measure.map (S.X i₀) ℙ)) a s :=
--   _root_.absolutelyContinuousOnInterval_cdf (S.X_hasPDF i₀).absolutelyContinuous F_a

/-- Integration by parts for CDF powers.
For a random variable with CDF `F`, density `f`, and `F(a) = 0`:
  `∫ₐˢ F(ψ)^m dψ = s · F(s)^m - m · ∫ₐˢ ψ · F(ψ)^{m-1} · f(ψ) dψ`
where `f(ψ) = (pdf (X₀) ℙ volume ψ).toReal`.
The boundary term `a · F(a)^m` vanishes since `F(a) = 0`. -/
theorem integral_cdf_pow (i₀ : Fin n) (a s : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (F_a : cdf (Measure.map (S.X i₀) ℙ) a = 0) :
    ∫ ψ in a..s, cdf (Measure.map (S.X i₀) ℙ) ψ ^ m =
      s * cdf (Measure.map (S.X i₀) ℙ) s ^ m -
      m * ∫ ψ in a..s,
        ψ * cdf (Measure.map (S.X i₀) ℙ) ψ ^ (m - 1) * (pdf (S.X i₀) ℙ volume ψ).toReal := by
  simp only [pdf]
  set F := cdf (Measure.map (S.X i₀) ℙ)
  have h0 : AbsolutelyContinuousOnInterval (fun x => F x ^ m) a s :=
    (absolutelyContinuousOnInterval_cdf (S.X_hasPDF i₀).absolutelyContinuous F_a).pow m
  have ibp := LipschitzWith.id.lipschitzOnWith.absolutelyContinuousOnInterval
    |>.integral_mul_deriv_eq_deriv_mul h0
  simp only [id_eq, F_a, zero_pow (by omega : m ≠ 0), mul_zero, sub_zero, deriv_id', one_mul] at ibp
  have h_deriv_ae : ∀ᵐ x ∂volume.restrict (Set.uIoc a s),
      x * deriv (fun y => F y ^ m) x =
      m * (x * F x ^ (m - 1) * ((Measure.map (S.X i₀) ℙ).rnDeriv volume x).toReal) := by
    filter_upwards [F.ae_hasDerivAt.filter_mono (ae_mono Measure.restrict_le_self)] with x hx
    rw [measure_cdf _] at hx
    rw [(hx.fun_pow m).deriv]
    ring
  have : ∫ x in a..s, x * deriv (F · ^ m) x =
      m * ∫ x in a..s, x * F x ^ (m - 1) * ((Measure.map (S.X i₀) ℙ).rnDeriv volume x).toReal := by
    rw [intervalIntegral.integral_congr_ae_restrict h_deriv_ae, intervalIntegral.integral_const_mul]
  linarith

/-- Expected value of the k-th order statistic.

For `n` i.i.d. random variables bounded in `[a, b]` with CDF `F`, density `f`, `F(a) = 0`,
`F(b) = 1`:

  `E[X_{(k+1)}] = n!/(k!(n-1-k)!) · ∫ₐᵇ ψ · F(ψ)^k · (1-F(ψ))^{n-1-k} · f(ψ) dψ`

where `k` is 0-indexed, so `X_{(0)}` is the minimum and `X_{(n-1)}` is the maximum. -/
theorem expected_val (k : Fin n) (i₀ : Fin n) (a b : ℝ) (hab : a ≤ b)
    (hF_a : cdf (Measure.map (S.X i₀) ℙ) a = 0)
    (hF_b : cdf (Measure.map (S.X i₀) ℙ) b = 1) :
    𝔼[S.val k] =
      n ! / (k.val ! * (n - 1 - k.val) !) *
        ∫ ψ in a..b, ψ * cdf (Measure.map (S.X i₀) ℙ) ψ ^ k.val *
          (1 - cdf (Measure.map (S.X i₀) ℙ) ψ) ^ (n - 1 - k.val) *
          (pdf (S.X i₀) ℙ volume ψ).toReal := by
  set F := cdf (Measure.map (S.X i₀) ℙ) with hF_def
  set μ := Measure.map (S.X i₀) ℙ
  set C : ℝ := n ! / (k.val ! * ((n - 1 - k.val) ! : ℝ)) with hC_def
  rw [show (𝔼[S.val k] : ℝ) = ∫ ψ, ψ * (pdf (S.val k) ℙ volume ψ).toReal from
    pdf.integral_mul_eq_integral.symm]
  have eq0 := S.pdf_val i₀ k
  have ineq1 : ∀ ψ, 0 ≤ C * F ψ ^ k.val * (1 - F ψ) ^ (n - 1 - k.val) :=
    fun ψ => mul_nonneg (mul_nonneg (div_nonneg (Nat.cast_nonneg' _)
      (mul_nonneg (Nat.cast_nonneg' _) (Nat.cast_nonneg' _)))
      (pow_nonneg (cdf_nonneg _ _) _))
      (pow_nonneg (sub_nonneg.mpr (cdf_le_one _ _)) _)
  have eq2 : ∀ᵐ ψ, ψ * (pdf (S.val k) ℙ volume ψ).toReal =
      C * (ψ * F ψ ^ k.val * (1 - F ψ) ^ (n - 1 - k.val) * (pdf (S.X i₀) ℙ volume ψ).toReal) := by
    filter_upwards [eq0] with ψ hψ
    rw [hψ, ENNReal.toReal_mul, ENNReal.toReal_ofReal (ineq1 ψ)]
    ring
  rw [integral_congr_ae eq2, integral_const_mul]
  congr 1
  have abs_cont : μ ≪ volume := (S.X_hasPDF i₀).absolutelyContinuous
  have pdf_eq_zero0 : ∀ᵐ ψ, ψ ∈ Set.Iic a → (pdf (S.X i₀) ℙ volume ψ).toReal = 0 :=
    ae_restrict_rnDeriv_eq_zero abs_cont measurableSet_Iic
      (by rw [← ofReal_cdf, hF_a, ENNReal.ofReal_zero])
  have pdf_eq_zero1 : ∀ᵐ ψ, ψ ∈ Set.Ioi b → (pdf (S.X i₀) ℙ volume ψ).toReal = 0 :=
    ae_restrict_rnDeriv_eq_zero abs_cont measurableSet_Ioi (by
      have h1 : μ (Set.Iic b) = 1 := by rw [← ofReal_cdf, hF_b, ENNReal.ofReal_one]
      rw [← Set.compl_Iic, measure_compl measurableSet_Iic (measure_ne_top μ _),
        measure_univ, h1, tsub_self])
  rw [eq_comm, intervalIntegral.integral_of_le hab]
  exact setIntegral_eq_integral_of_ae_compl_eq_zero (by
    filter_upwards [pdf_eq_zero0, pdf_eq_zero1] with ψ h_lo h_hi h_not_mem
    by_cases h : ψ ≤ a
    · rw [h_lo (Set.mem_Iic.mpr h), mul_zero]
    · push Not at h
      have hb : b < ψ := by
        by_contra! h'
        exact h_not_mem (Set.mem_Ioc.mpr ⟨h, h'⟩)
      rw [h_hi (Set.mem_Ioi.mpr hb), mul_zero])

/-- For `n ≥ 2` i.i.d. random variables bounded in `[a, b]` with CDF `F`, `F(a) = 0`, `F(b) = 1`:

  `n · E[s · F(s)^{n-1} - ∫ₐˢ F(ψ)^{n-1} dψ] = E[X_{(n-1)}]`

where the expectation on the left is over `s = X₀`, and `X_{(n-1)}` is the
second-highest order statistic (0-indexed as `n-2`).
-/
theorem expected_second_highest [Nat.AtLeastTwo n]
    (i₀ : Fin n) (a b : ℝ) (hab : a ≤ b)
    (bounded : ∀ i, ∀ᵐ ω, S.X i ω ∈ Set.Icc a b)
    (F_a : cdf (Measure.map (S.X i₀) ℙ) a = 0)
    (F_b : cdf (Measure.map (S.X i₀) ℙ) b = 1) :
    𝔼[S.val ⟨n - 2, by grind [Nat.AtLeastTwo.prop (n := n)]⟩] =
    n * ∫ ω, S.X i₀ ω * cdf (Measure.map (S.X i₀) ℙ) (S.X i₀ ω) ^ (n - 1) -
      ∫ ψ in a..(S.X i₀ ω), cdf (Measure.map (S.X i₀) ℙ) ψ ^ (n - 1) ∂ℙ := by
  have ibp_ae : ∀ᵐ ω,
      S.X i₀ ω * cdf (Measure.map (S.X i₀) ℙ) (S.X i₀ ω) ^ (n - 1) -
        ∫ ψ in a..(S.X i₀ ω), cdf (Measure.map (S.X i₀) ℙ) ψ ^ (n - 1) =
      (n - 1 : ℕ) * ∫ ψ in a..(S.X i₀ ω), ψ * cdf (Measure.map (S.X i₀) ℙ) ψ ^ (n - 2) *
        ((Measure.map (S.X i₀) ℙ).rnDeriv volume ψ).toReal := by
    filter_upwards [bounded i₀] with ω hω
    have h := S.integral_cdf_pow i₀ a (S.X i₀ ω) (n - 1) (by grind [Nat.AtLeastTwo.prop (n := n)])
      F_a
    simp only [pdf] at h
    rw [show (n - 1 : ℕ) - 1 = n - 2 by omega] at h
    linarith
  rw [integral_congr_ae ibp_ae, integral_const_mul]
  set F := cdf (Measure.map (S.X i₀) ℙ) with hF_def
  set f₀ : ℝ → ℝ := fun ψ => ((Measure.map (S.X i₀) ℙ).rnDeriv volume ψ).toReal with hf₀_def
  set g : ℝ → ℝ := fun ψ => ψ * F ψ ^ (n - 2) * f₀ ψ with hg_def
  set k : Fin n := ⟨n - 2, by have := Nat.AtLeastTwo.prop (n := n); omega⟩ with hk_def
  rw [show ∫ (ω : Ω), (∫ ψ in a..(S.X i₀ ω), g ψ) ∂ℙ = ∫ ψ in a..b, g ψ * (1 - F ψ) by
    rw [integral_congr_ae <| show ∀ᵐ ω ∂ℙ, ∫ ψ in a..(S.X i₀ ω), g ψ =
        ∫ ψ in a..b, (Set.Iic (S.X i₀ ω)).indicator g ψ by
      filter_upwards [bounded i₀] with ω ⟨haω, hωb⟩
      rw [intervalIntegral.integral_of_le haω, intervalIntegral.integral_of_le hab,
          setIntegral_indicator measurableSet_Iic]
      rw [show Set.Ioc a (S.X i₀ ω) = Set.Ioc a b ∩ Set.Iic (S.X i₀ ω) from by
        ext ψ; simp only [Set.mem_Ioc, Set.mem_inter_iff, Set.mem_Iic]
        exact ⟨fun ⟨h1, h3⟩ => ⟨⟨h1, le_trans h3 hωb⟩, h3⟩,
               fun ⟨⟨h1, _⟩, h3⟩ => ⟨h1, h3⟩⟩]]
    have int0 : Integrable
        (Function.uncurry fun ψ ω => (Set.Iic (S.X i₀ ω)).indicator g ψ)
        ((volume.restrict (Set.uIoc a b)).prod ℙ) := by
      have hg_meas : Measurable g :=
        measurable_id.mul (F.mono.measurable.pow_const _) |>.mul <|
          (Measure.measurable_rnDeriv _ _).ennreal_toReal
      have hS_meas : MeasurableSet {p : ℝ × Ω | p.1 ≤ S.X i₀ p.2} :=
        measurableSet_le measurable_fst <| S.X_measurable i₀ |>.comp measurable_snd
      have hf_sm : StronglyMeasurable
          (Function.uncurry fun ψ ω => (Set.Iic (S.X i₀ ω)).indicator g ψ) :=
        hg_meas.comp measurable_fst |>.stronglyMeasurable |>.indicator hS_meas
      have hg_intOn : IntegrableOn g (Set.uIoc a b) volume := by
        have hbound : Integrable (fun x => max |a| |b| * ‖f₀ x‖)
            (volume.restrict (Set.uIoc a b)) :=
          Measure.integrable_toReal_rnDeriv.norm.const_mul (max |a| |b|) |>.integrableOn
        exact Integrable.mono hbound hg_meas.aestronglyMeasurable (by
          filter_upwards [ae_restrict_mem measurableSet_uIoc] with ψ hψ
          simp only [Set.uIoc, min_eq_left hab, max_eq_right hab, Set.mem_Ioc] at hψ
          simp only [Real.norm_eq_abs, norm_mul, abs_of_nonneg (le_max_of_le_left (abs_nonneg a)),
            abs_abs, g]
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          have hF0 : 0 ≤ F ψ := cdf_nonneg _ ψ
          have hF1 : F ψ ≤ 1 := cdf_le_one _ ψ
          have hψ_le : |ψ| ≤ max |a| |b| := abs_le.2 <|
            ⟨by linarith [neg_abs_le a, le_max_left |a| |b|],
              by linarith [le_abs_self b, le_max_right |a| |b|]⟩
          have hpow_le : |F ψ ^ (n - 2)| ≤ 1 := by
            rw [abs_pow, abs_of_nonneg hF0]; exact pow_le_one₀ hF0 hF1
          exact le_trans (mul_le_mul_of_nonneg_right hψ_le (abs_nonneg _))
            (mul_le_of_le_one_right (le_max_of_le_left (abs_nonneg a)) hpow_le))
      exact Integrable.mono (hg_intOn.comp_fst ℙ) hf_sm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun p =>
          show ‖(Set.Iic (S.X i₀ p.2)).indicator g p.1‖ ≤ ‖g p.1‖ from
            norm_indicator_le_norm_self g p.1)
    rw [(intervalIntegral_integral_swap int0).symm]
    congr 1
    ext ψ
    have h_eq ω : (Set.Iic (S.X i₀ ω)).indicator g ψ =
        g ψ * (S.X i₀ ⁻¹' Set.Ici ψ).indicator 1 ω := by
      simp only [Set.indicator_apply, Set.mem_Iic]
      by_cases h : ψ ≤ S.X i₀ ω <;>
      simp [h]
    simp_rw [h_eq]
    rw [integral_const_mul, integral_indicator_one ((S.X_measurable i₀) measurableSet_Ici),
      measureReal_def, ← Measure.map_apply (S.X_measurable i₀) measurableSet_Ici]
    congr 1
    rw [show Set.Ici ψ = Set.Ioi ψ ∪ {ψ} from Set.Ioi_union_left.symm,
        measure_union (Set.disjoint_singleton_right.mpr (by simp))
          (measurableSet_singleton _), S.X_hasPDF i₀ |>.absolutelyContinuous Real.volume_singleton,
        add_zero, show Set.Ioi ψ = (Set.Iic ψ)ᶜ from Set.compl_Iic.symm,
        prob_compl_eq_one_sub measurableSet_Iic, ENNReal.toReal_sub_of_le prob_le_one one_ne_top,
        ENNReal.toReal_one, hF_def, ← measureReal_def, cdf_eq_real]]
  have hn2 := Nat.AtLeastTwo.prop (n := n)
  have eq_k := S.expected_val k i₀ a b hab F_a F_b
  simp only [pdf] at eq_k
  rw [show (k : ℕ) = n - 2 by simp [hk_def], show n - 1 - (n - 2) = 1 from by omega] at eq_k
  simp only [factorial_one, cast_one, mul_one, pow_one] at eq_k
  rw [eq_k, ← mul_assoc]
  congr 1
  · have eq0 := Nat.factorial_succ (n - 2)
    rw [show n - 2 + 1 = n - 1 from by omega] at eq0
    have eq1 := Nat.factorial_succ (n - 1)
    rw [show n - 1 + 1 = n from by omega] at eq1
    rw [eq1, eq0]
    push_cast
    field_simp
  · simpa [g, F, f₀] using by ring_nf

end OrderStatisticsSetup

end Probability

end

end MathEconLib
