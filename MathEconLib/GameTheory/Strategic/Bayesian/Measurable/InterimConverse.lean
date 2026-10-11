/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import MathEconLib.GameTheory.Strategic.Bayesian.Measurable.Interim
public import MathEconLib.ForMathlib.MeasureTheory.VonNeumannSelection

/-!
# The almost-everywhere interim characterization of Bayesian Nash equilibrium

For standard Borel type and action spaces, ex-ante Bayesian Nash equilibrium implies that almost
every type best responds against all actions simultaneously. Conditional deviation payoffs must be
integrable on one conull set protecting every action. Together with incumbent integrability, this
condition gives an equivalence between ex-ante equilibrium and interim optimality.

## Main statements

* `BayesianGame.ae_interim_of_isBNE`: Ex-ante equilibrium implies a.e. interim best response.
* `BayesianGame.isBNE_iff_ae_interim`: Equilibrium is equivalent to integrable incumbent payoffs
  and a.e. interim best response.

## Tags

bayesian nash equilibrium, interim payoff, measurable selection, integrability
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace MathEconLib.GameTheory.BayesianGame

open BayesianPrior

variable {I : Type*} {Θ : I → Type*} {A : I → Type*} [DecidableEq I]
  [∀ i, MeasurableSpace (Θ i)] [∀ i, MeasurableSpace (A i)]
  [∀ i, StandardBorelSpace (Θ i)] [∀ i, Nonempty (Θ i)]
  [∀ i, StandardBorelSpace (A i)]
  (G : BayesianGame I Θ A ℝ) (μ : Measure (∀ i, Θ i)) [IsProbabilityMeasure μ]
  (B : ConditionalBeliefs μ)
  (hmeas : ∀ i, Measurable (fun p : (∀ j, A j) × (∀ j, Θ j) => G.payoff i p.1 p.2))

include hmeas

/-- An ex-ante equilibrium best responds at almost every type, against every action simultaneously,
provided conditional deviation payoffs are integrable on one conull set of own types. -/
theorem ae_interim_of_isBNE (s : G.Strategy) (hbne : G.IsBNE μ s)
    (hdev : G.HasIntegrableInterimDeviations μ B s) : G.IsAEInterimBestResponse μ B s := by
  have hint := hbne.integrable
  intro i
  haveI : Nonempty (A i) := ⟨(s i).1 (Classical.arbitrary (Θ i))⟩
  by_contra hviol
  rw [ae_iff] at hviol
  have hpos : 0 < marginalType μ i
      {θᵢ | ∃ aᵢ, G.interimPayoff μ B i θᵢ s < G.interimPayoffAction μ B i θᵢ aᵢ s} := by
    have hVeq : {θᵢ | ¬ ∀ aᵢ : A i,
        G.interimPayoffAction μ B i θᵢ aᵢ s ≤ G.interimPayoff μ B i θᵢ s} =
        {θᵢ | ∃ aᵢ, G.interimPayoff μ B i θᵢ s < G.interimPayoffAction μ B i θᵢ aᵢ s} := by
      ext θᵢ
      simp [not_forall, not_le]
    rw [hVeq] at hviol
    exact pos_iff_ne_zero.mpr hviol
  obtain ⟨d₀, hd₀_meas, hT_pos⟩ := exists_measurable_improving_selection
    (f := fun θᵢ aᵢ => G.interimPayoffAction μ B i θᵢ aᵢ s)
    (G.measurable_interimPayoffAction μ B hmeas i s)
    (G.measurable_interimPayoff μ B hmeas i s) (marginalType μ i) hpos
  set T : Set (Θ i) :=
    {θᵢ | G.interimPayoff μ B i θᵢ s < G.interimPayoffAction μ B i θᵢ (d₀ θᵢ) s}
  have hT_meas : MeasurableSet T := measurableSet_lt
    (G.measurable_interimPayoff μ B hmeas i s)
    ((G.measurable_interimPayoffAction μ B hmeas i s).comp (measurable_id.prodMk hd₀_meas))
  set hMass : Θ i → ℝ≥0∞ := fun θᵢ =>
    ∫⁻ θo, ‖G.interimPayoffActionIntegrand i θᵢ (d₀ θᵢ) s θo‖ₑ ∂(B.opponents i θᵢ)
  have hMass_meas : Measurable hMass :=
    (G.measurable_lintegral_enorm_deviation μ B hmeas i s).comp (measurable_id.prodMk hd₀_meas)
  have hMass_fin_ae : ∀ᵐ θᵢ ∂(marginalType μ i), hMass θᵢ < ∞ := by
    filter_upwards [hdev i] with θᵢ hθ
    exact hasFiniteIntegral_iff_enorm.mp (hθ (d₀ θᵢ)).2
  -- A bounded conditional-mass slice retains a positive measure of improving types.
  have hSM_ex : ∃ M : ℕ, 0 < marginalType μ i (T ∩ {θᵢ | hMass θᵢ ≤ M}) := by
    by_contra hall
    push Not at hall
    have hnull : ∀ M : ℕ, marginalType μ i (T ∩ {θᵢ | hMass θᵢ ≤ M}) = 0 :=
      fun M => le_antisymm (hall M) (zero_le _)
    have hcover : T ≤ᵐ[marginalType μ i] ⋃ M : ℕ, T ∩ {θᵢ | hMass θᵢ ≤ M} := by
      filter_upwards [hMass_fin_ae] with θᵢ hfin hT
      obtain ⟨M, hM⟩ := ENNReal.exists_nat_gt hfin.ne
      exact Set.mem_iUnion.mpr ⟨M, hT, hM.le⟩
    have hTnull : marginalType μ i T = 0 :=
      le_antisymm ((measure_mono_ae hcover).trans (measure_iUnion_null hnull).le) (zero_le _)
    exact absurd hTnull hT_pos.ne'
  obtain ⟨M, hSM_pos⟩ := hSM_ex
  set SM : Set (Θ i) := T ∩ {θᵢ | hMass θᵢ ≤ M}
  have hSM_meas : MeasurableSet SM := hT_meas.inter (hMass_meas measurableSet_Iic)
  classical
  let d : Θ i → A i := SM.piecewise d₀ ((s i).1)
  have hd_meas : Measurable d := Measurable.piecewise hSM_meas hd₀_meas (s i).2
  let s' : G.Strategy := G.replace s i ⟨d, hd_meas⟩
  have hs'i : s' i = ⟨d, hd_meas⟩ := G.replace_self s i _
  have hagree : ∀ j, j ≠ i → s' j = s j := fun j hj => G.replace_of_ne s i _ hj
  have hpayoff (θᵢ : Θ i) (θo : OpponentProfile Θ i) :
      G.payoff i (G.measurableActionProfile s' (insert i θᵢ θo)) (insert i θᵢ θo) =
        G.interimPayoffActionIntegrand i θᵢ (d θᵢ) s θo := by
    rw [G.payoff_insert_eq_interimPayoffActionIntegrand i θᵢ s s' hagree, hs'i]
  have hself (θᵢ : Θ i) (θo : OpponentProfile Θ i) :
      G.interimPayoffActionIntegrand i θᵢ ((s i).1 θᵢ) s θo =
        G.payoff i (G.measurableActionProfile s (insert i θᵢ θo)) (insert i θᵢ θo) :=
    (G.payoff_insert_eq_interimPayoffActionIntegrand i θᵢ s s (fun _ _ => rfl) θo).symm
  have hbound : ∀ θᵢ,
      (∫⁻ θo, ‖G.payoff i (G.measurableActionProfile s' (insert i θᵢ θo))
        (insert i θᵢ θo)‖ₑ ∂(B.opponents i θᵢ)) ≤
      M + ∫⁻ θo, ‖G.payoff i (G.measurableActionProfile s (insert i θᵢ θo))
        (insert i θᵢ θo)‖ₑ ∂(B.opponents i θᵢ) := by
    intro θᵢ
    simp_rw [hpayoff]
    by_cases hmem : θᵢ ∈ SM
    · have hdv : d θᵢ = d₀ θᵢ := Set.piecewise_eq_of_mem _ _ _ hmem
      rw [hdv]
      exact le_add_right hmem.2
    · have hdv : d θᵢ = (s i).1 θᵢ := Set.piecewise_eq_of_notMem _ _ _ hmem
      simp_rw [hdv, hself]
      exact le_add_self
  have hs'_int : Integrable (fun θ => G.payoff i (G.measurableActionProfile s' θ) θ) μ := by
    refine ⟨(G.measurable_payoff_comp hmeas i s').aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm,
      ← B.lintegral_insert i (G.measurable_payoff_comp hmeas i s').enorm]
    have hequil_fin :
        ∫⁻ θᵢ, ∫⁻ θo, ‖G.payoff i (G.measurableActionProfile s (insert i θᵢ θo))
          (insert i θᵢ θo)‖ₑ ∂(B.opponents i θᵢ) ∂(marginalType μ i) < ∞ := by
      rw [B.lintegral_insert i (G.measurable_payoff_comp hmeas i s).enorm]
      exact hasFiniteIntegral_iff_enorm.mp (hint i).2
    calc
      _ ≤ ∫⁻ θᵢ, (M + ∫⁻ θo, ‖G.payoff i (G.measurableActionProfile s (insert i θᵢ θo))
          (insert i θᵢ θo)‖ₑ ∂(B.opponents i θᵢ)) ∂(marginalType μ i) := lintegral_mono hbound
      _ = M + ∫⁻ θᵢ, ∫⁻ θo, ‖G.payoff i (G.measurableActionProfile s (insert i θᵢ θo))
          (insert i θᵢ θo)‖ₑ ∂(B.opponents i θᵢ) ∂(marginalType μ i) := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
      _ < ∞ := ENNReal.add_lt_top.mpr ⟨ENNReal.natCast_lt_top M, hequil_fin⟩
  have hinterim (θᵢ : Θ i) :
      G.interimPayoff μ B i θᵢ s' = G.interimPayoffAction μ B i θᵢ (d θᵢ) s := by
    rw [G.interimPayoff_eq_interimPayoffAction μ B i θᵢ s s' hagree, hs'i]
  have hge (θᵢ : Θ i) : G.interimPayoff μ B i θᵢ s ≤ G.interimPayoff μ B i θᵢ s' := by
    rw [hinterim]
    by_cases hmem : θᵢ ∈ SM
    · have hdv : d θᵢ = d₀ θᵢ := Set.piecewise_eq_of_mem _ _ _ hmem
      rw [hdv]
      exact le_of_lt hmem.1
    · have hdv : d θᵢ = (s i).1 θᵢ := Set.piecewise_eq_of_notMem _ _ _ hmem
      rw [hdv]
      exact le_rfl
  have hstrict (θᵢ : Θ i) (hmem : θᵢ ∈ SM) :
      G.interimPayoff μ B i θᵢ s < G.interimPayoff μ B i θᵢ s' := by
    have hdv : d θᵢ = d₀ θᵢ := Set.piecewise_eq_of_mem _ _ _ hmem
    rw [hinterim, hdv]
    exact hmem.1
  have hint_s' := G.integrable_interimPayoff μ B hmeas i s' hs'_int
  have hint_s := G.integrable_interimPayoff μ B hmeas i s (hint i)
  have hdiff_nonneg : 0 ≤ᵐ[marginalType μ i]
      fun θᵢ => G.interimPayoff μ B i θᵢ s' - G.interimPayoff μ B i θᵢ s :=
    Filter.Eventually.of_forall fun θᵢ => sub_nonneg.mpr (hge θᵢ)
  have hsupp_pos : 0 < marginalType μ i
      (Function.support fun θᵢ => G.interimPayoff μ B i θᵢ s' - G.interimPayoff μ B i θᵢ s) :=
    hSM_pos.trans_le (measure_mono fun θᵢ hmem => (sub_pos.mpr (hstrict θᵢ hmem)).ne')
  have hint_pos : 0 < ∫ θᵢ, (G.interimPayoff μ B i θᵢ s' - G.interimPayoff μ B i θᵢ s)
      ∂(marginalType μ i) :=
    (integral_pos_iff_support_of_nonneg_ae hdiff_nonneg (hint_s'.sub hint_s)).mpr hsupp_pos
  rw [integral_sub hint_s' hint_s, sub_pos] at hint_pos
  have hexa : G.exAntePayoff μ i s < G.exAntePayoff μ i s' := by
    rw [G.exAntePayoff_eq_integral_interimPayoff μ B hmeas i s (hint i),
      G.exAntePayoff_eq_integral_interimPayoff μ B hmeas i s' hs'_int]
    exact hint_pos
  exact absurd (((G.isBNE_iff μ s).mp hbne).1 i s' hagree hs'_int) (not_le.mpr hexa)

/-- Bayesian Nash equilibrium is integrable incumbent utility and almost-everywhere interim best
response, under the simultaneous conditional integrability guard for deviations. -/
theorem isBNE_iff_ae_interim (s : G.Strategy)
    (hdev : G.HasIntegrableInterimDeviations μ B s) :
    G.IsBNE μ s ↔ G.IncumbentPayoffsIntegrable μ s ∧ G.IsAEInterimBestResponse μ B s :=
  ⟨fun h => ⟨h.integrable, G.ae_interim_of_isBNE μ B hmeas s h hdev⟩,
    fun h => G.isBNE_of_ae_interim μ B hmeas s h.1 h.2⟩

end MathEconLib.GameTheory.BayesianGame

end
