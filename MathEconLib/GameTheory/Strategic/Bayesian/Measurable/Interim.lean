/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import MathEconLib.GameTheory.Strategic.Bayesian.Measurable.Beliefs
public import MathEconLib.GameTheory.Strategic.Bayesian.Measurable.PureBNE

/-!
# Interim payoffs and sufficient conditions for Bayesian Nash equilibrium

Conditional beliefs over opponents' types determine a player's expected payoff at each own type.
The player's own type is inserted into the full type profile. Interim payoffs satisfy the law of
total expectation when the ex-ante payoff is integrable, and conditional-payoff versions agree
almost everywhere under the marginal type law. Conditional integrability of all actions uses one
conull set per player, common to every action. For real-valued utility, interim best response on
such a set for each player implies ex-ante Bayesian Nash equilibrium when incumbent payoffs are
integrable.

## Main definitions

* `BayesianGame.interimPayoffAction`: Conditional payoff from a chosen action.
* `BayesianGame.interimPayoff`: Conditional payoff from the prescribed strategy.
* `BayesianGame.IsAEInterimBestResponse`: One conull set of best-responding types per player.
* `BayesianGame.HasIntegrableInterimDeviations`: Simultaneous conditional integrability of actions.

## Main statements

* `BayesianGame.interimPayoffAction_ae_eq`: Agreement across conditional-belief versions.
* `BayesianGame.exAntePayoff_eq_integral_interimPayoff`: The law of total expectation.
* `BayesianGame.isBNE_of_ae_interim`: Interim optimality implies ex-ante equilibrium.

## Tags

bayesian nash equilibrium, interim payoff, conditional beliefs, integrability
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace MathEconLib.GameTheory.BayesianGame

open BayesianPrior

section General

variable {I : Type*} {Θ : I → Type*} {A : I → Type*} {V : Type*} [DecidableEq I]
  [∀ i, MeasurableSpace (Θ i)] [∀ i, MeasurableSpace (A i)]
  (G : BayesianGame I Θ A V) (μ : Measure (∀ i, Θ i))
  (B : ConditionalBeliefs μ)

/-- Realized utility from an action when own type is fixed and opponents' types vary. -/
def interimPayoffActionIntegrand (i : I) (θᵢ : Θ i) (aᵢ : A i) (s : G.Strategy)
    (θo : OpponentProfile Θ i) : V :=
  let θ := insert i θᵢ θo
  G.payoff i (Function.update (G.measurableActionProfile s θ) i aᵢ) θ

/-- A unilateral strategy change coincides pointwise with the corresponding own-type action. -/
lemma payoff_insert_eq_interimPayoffActionIntegrand (i : I) (θᵢ : Θ i)
    (s s' : G.Strategy) (hagree : ∀ j, j ≠ i → s' j = s j) (θo : OpponentProfile Θ i) :
    G.payoff i (G.measurableActionProfile s' (insert i θᵢ θo)) (insert i θᵢ θo) =
      G.interimPayoffActionIntegrand i θᵢ ((s' i).1 θᵢ) s θo := by
  unfold interimPayoffActionIntegrand
  congr 1
  funext j
  by_cases hj : j = i
  · subst j
    simp
  · simp [Function.update_of_ne hj, measurableActionProfile, hagree j hj]

/-- The conditional deviation integrand is jointly measurable in own type, action, and opponents. -/
lemma measurable_interimPayoffActionIntegrand [MeasurableSpace V]
    (hmeas : ∀ i, Measurable (fun p : (∀ j, A j) × (∀ j, Θ j) => G.payoff i p.1 p.2))
    (i : I) (s : G.Strategy) :
    Measurable (fun q : (Θ i × A i) × OpponentProfile Θ i =>
      G.interimPayoffActionIntegrand i q.1.1 q.1.2 s q.2) := by
  have hθ : Measurable (fun q : (Θ i × A i) × OpponentProfile Θ i =>
      insert i q.1.1 q.2) :=
    (measurable_insert i).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  exact (hmeas i).comp ((measurable_update'.comp
    ((G.measurable_actionProfile s |>.comp hθ).prodMk
      (measurable_snd.comp measurable_fst))).prodMk hθ)

variable [NormedAddCommGroup V]

/-- For each player, all action payoffs are conditionally integrable on a common conull set of own
types. -/
def HasIntegrableInterimDeviations (s : G.Strategy) : Prop :=
  ∀ i, ∀ᵐ θᵢ ∂(marginalType μ i), ∀ aᵢ : A i,
    Integrable (G.interimPayoffActionIntegrand i θᵢ aᵢ s) (B.opponents i θᵢ)

section Integrability

variable [MeasurableSpace V] [BorelSpace V]
  (hmeas : ∀ i, Measurable (fun p : (∀ j, A j) × (∀ j, Θ j) => G.payoff i p.1 p.2))

include hmeas

/-- The conditional integral of the norm of realized utility is jointly measurable in own type and
action. -/
theorem measurable_lintegral_enorm_deviation (i : I) (s : G.Strategy) :
    Measurable (fun p : Θ i × A i =>
      ∫⁻ θo, ‖G.interimPayoffActionIntegrand i p.1 p.2 s θo‖ₑ ∂(B.opponents i p.1)) := by
  let κ : Kernel (Θ i × A i) (OpponentProfile Θ i) :=
    (B.opponents i).comap Prod.fst measurable_fst
  exact Measurable.lintegral_kernel_prod_right' (κ := κ)
    (G.measurable_interimPayoffActionIntegrand hmeas i s).enorm

/-- Globally bounded measurable payoffs are conditionally integrable for all actions on a common
conull set of own types. -/
lemma hasIntegrableInterimDeviations_of_bdd [SecondCountableTopology V] (s : G.Strategy)
    (hbdd : ∀ i, ∃ C : ℝ, ∀ a θ, ‖G.payoff i a θ‖ ≤ C) :
    G.HasIntegrableInterimDeviations μ B s := by
  intro i
  obtain ⟨C, hC⟩ := hbdd i
  apply Filter.Eventually.of_forall
  intro θᵢ aᵢ
  have hf : Measurable (G.interimPayoffActionIntegrand i θᵢ aᵢ s) :=
    (G.measurable_interimPayoffActionIntegrand hmeas i s).comp
      ((measurable_const (a := (θᵢ, aᵢ))).prodMk measurable_id)
  apply Integrable.of_bound hf.aestronglyMeasurable C
  apply Filter.Eventually.of_forall
  intro θo
  simpa only [interimPayoffActionIntegrand] using
    hC (Function.update (G.measurableActionProfile s (insert i θᵢ θo)) i aᵢ) (insert i θᵢ θo)

end Integrability

variable [NormedSpace ℝ V]

/-- Expected payoff from a chosen action conditional on own type and selected opponent beliefs. -/
def interimPayoffAction [CompleteSpace V] (i : I) (θᵢ : Θ i) (aᵢ : A i) (s : G.Strategy) : V :=
  ∫ θo, G.interimPayoffActionIntegrand i θᵢ aᵢ s θo ∂(B.opponents i θᵢ)

variable [CompleteSpace V]

/-- Conditional expected payoff when following the prescribed strategy. -/
def interimPayoff (i : I) (θᵢ : Θ i) (s : G.Strategy) : V :=
  G.interimPayoffAction μ B i θᵢ ((s i).1 θᵢ) s

/-- Each player best responds against all actions simultaneously at almost every own type. -/
def IsAEInterimBestResponse [LE V] (s : G.Strategy) : Prop :=
  ∀ i, ∀ᵐ θᵢ ∂(marginalType μ i), ∀ aᵢ : A i,
    G.interimPayoffAction μ B i θᵢ aᵢ s ≤ G.interimPayoff μ B i θᵢ s

/-- Following the prescribed action gives the conditional integral of realized utility. -/
lemma interimPayoff_eq_integral (i : I) (θᵢ : Θ i) (s : G.Strategy) :
    G.interimPayoff μ B i θᵢ s =
      ∫ θo, G.payoff i (G.measurableActionProfile s (insert i θᵢ θo))
        (insert i θᵢ θo) ∂(B.opponents i θᵢ) := by
  unfold interimPayoff interimPayoffAction
  congr 1
  funext θo
  exact (G.payoff_insert_eq_interimPayoffActionIntegrand i θᵢ s s (fun _ _ => rfl) θo).symm

/-- A unilateral deviation's interim payoff equals its chosen-action payoff at every type. -/
lemma interimPayoff_eq_interimPayoffAction (i : I) (θᵢ : Θ i) (s s' : G.Strategy)
    (hagree : ∀ j, j ≠ i → s' j = s j) :
    G.interimPayoff μ B i θᵢ s' = G.interimPayoffAction μ B i θᵢ ((s' i).1 θᵢ) s := by
  rw [G.interimPayoff_eq_integral]
  unfold interimPayoffAction
  congr 1
  funext θo
  exact G.payoff_insert_eq_interimPayoffActionIntegrand i θᵢ s s' hagree θo

section Versions

variable [Countable I] [∀ i, StandardBorelSpace (Θ i)] [∀ i, Nonempty (Θ i)]
  [IsProbabilityMeasure μ] (B' : ConditionalBeliefs μ)

/-- For a fixed player, every action's interim payoff agrees across conditional-belief versions
simultaneously outside one null set under the marginal type law. -/
theorem interimPayoffAction_ae_eq (i : I) (s : G.Strategy) :
    ∀ᵐ θᵢ ∂(marginalType μ i), ∀ aᵢ : A i,
      G.interimPayoffAction μ B i θᵢ aᵢ s = G.interimPayoffAction μ B' i θᵢ aᵢ s := by
  filter_upwards [B.ae_eq B' i] with θᵢ hθ aᵢ
  simp only [interimPayoffAction, hθ]

/-- Almost-everywhere interim best response does not depend on the selected belief version. -/
theorem isAEInterimBestResponse_iff_of_conditionalBeliefs [LE V] (s : G.Strategy) :
    G.IsAEInterimBestResponse μ B s ↔ G.IsAEInterimBestResponse μ B' s := by
  constructor
  · intro h i
    filter_upwards [h i, B.ae_eq B' i] with θᵢ hθ heq aᵢ
    simpa only [interimPayoff, interimPayoffAction, heq] using hθ aᵢ
  · intro h i
    filter_upwards [h i, B.ae_eq B' i] with θᵢ hθ heq aᵢ
    simpa only [interimPayoff, interimPayoffAction, ← heq] using hθ aᵢ

omit [NormedSpace ℝ V] [CompleteSpace V] in
/-- Conditional integrability of all actions on a common conull set is independent of the selected
conditional-belief version. -/
theorem hasIntegrableInterimDeviations_iff_of_conditionalBeliefs (s : G.Strategy) :
    G.HasIntegrableInterimDeviations μ B s ↔ G.HasIntegrableInterimDeviations μ B' s := by
  constructor
  · intro h i
    filter_upwards [h i, B.ae_eq B' i] with θᵢ hθ heq aᵢ
    simpa only [heq] using hθ aᵢ
  · intro h i
    filter_upwards [h i, B.ae_eq B' i] with θᵢ hθ heq aᵢ
    simpa only [← heq] using hθ aᵢ

end Versions

variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (hmeas : ∀ i, Measurable (fun p : (∀ j, A j) × (∀ j, Θ j) => G.payoff i p.1 p.2))

include hmeas

/-- Conditional deviation payoffs are jointly measurable in own type and chosen action. -/
theorem measurable_interimPayoffAction (i : I) (s : G.Strategy) :
    Measurable (fun p : Θ i × A i => G.interimPayoffAction μ B i p.1 p.2 s) := by
  let κ : Kernel (Θ i × A i) (OpponentProfile Θ i) :=
    (B.opponents i).comap Prod.fst measurable_fst
  exact (StronglyMeasurable.integral_kernel_prod_right'
    (κ := κ) (G.measurable_interimPayoffActionIntegrand hmeas i s).stronglyMeasurable).measurable

/-- Incumbent interim payoff is measurable in own type. -/
theorem measurable_interimPayoff (i : I) (s : G.Strategy) :
    Measurable (fun θᵢ => G.interimPayoff μ B i θᵢ s) :=
  (G.measurable_interimPayoffAction μ B hmeas i s).comp (measurable_id.prodMk (s i).2)

variable [IsProbabilityMeasure μ]

/-- **Law of total expectation:** an integrable payoff under the prior has ex-ante expectation
equal to the integral of its interim expectation. -/
theorem exAntePayoff_eq_integral_interimPayoff (i : I) (s : G.Strategy)
    (hint : Integrable (fun θ => G.payoff i (G.measurableActionProfile s θ) θ) μ) :
    G.exAntePayoff μ i s = ∫ θᵢ, G.interimPayoff μ B i θᵢ s ∂(marginalType μ i) := by
  simp_rw [G.interimPayoff_eq_integral]
  exact (B.integral_insert i (G.measurable_payoff_comp hmeas i s) hint).symm

/-- Utility integrable under the prior has an integrable interim expectation. -/
theorem integrable_interimPayoff (i : I) (s : G.Strategy)
    (hint : Integrable (fun θ => G.payoff i (G.measurableActionProfile s θ) θ) μ) :
    Integrable (fun θᵢ => G.interimPayoff μ B i θᵢ s) (marginalType μ i) := by
  have hjoint := B.integrable_insert i (G.measurable_payoff_comp hmeas i s) hint
  have hnorm := (Measure.integrable_compProd_iff hjoint.aestronglyMeasurable).mp hjoint |>.2
  refine hnorm.mono (G.measurable_interimPayoff μ B hmeas i s).aestronglyMeasurable ?_
  filter_upwards [] with θᵢ
  rw [G.interimPayoff_eq_integral]
  exact (norm_integral_le_integral_norm _).trans (le_abs_self _)

end General

section Real

variable {I : Type*} {Θ : I → Type*} {A : I → Type*} [DecidableEq I]
  [∀ i, MeasurableSpace (Θ i)] [∀ i, MeasurableSpace (A i)]
  (G : BayesianGame I Θ A ℝ) (μ : Measure (∀ i, Θ i)) [IsProbabilityMeasure μ]
  (B : ConditionalBeliefs μ)
  (hmeas : ∀ i, Measurable (fun p : (∀ j, A j) × (∀ j, Θ j) => G.payoff i p.1 p.2))

include hmeas

/-- Interim optimality against all actions on a common conull set for each player implies ex-ante
Bayesian Nash equilibrium when incumbent payoffs are integrable. -/
theorem isBNE_of_ae_interim (s : G.Strategy)
    (hint : G.IncumbentPayoffsIntegrable μ s) (hbr : G.IsAEInterimBestResponse μ B s) :
    G.IsBNE μ s := by
  rw [G.isBNE_iff]
  refine ⟨fun i s' hagree hs'int => ?_, hint⟩
  rw [G.exAntePayoff_eq_integral_interimPayoff μ B hmeas i s' hs'int,
    G.exAntePayoff_eq_integral_interimPayoff μ B hmeas i s (hint i)]
  refine integral_mono_ae (G.integrable_interimPayoff μ B hmeas i s' hs'int)
    (G.integrable_interimPayoff μ B hmeas i s (hint i)) ?_
  filter_upwards [hbr i] with θᵢ hθ
  rw [G.interimPayoff_eq_interimPayoffAction μ B i θᵢ s s' hagree]
  exact hθ ((s' i).1 θᵢ)

/-- Best response against all actions on each player's specified conull type set implies Bayesian
Nash equilibrium when incumbent payoffs are integrable. -/
theorem isBNE_of_best_response_on_ae_set (s : G.Strategy)
    (hint : G.IncumbentPayoffsIntegrable μ s) (T : ∀ i, Set (Θ i))
    (hT : ∀ i, marginalType μ i (T i)ᶜ = 0)
    (hbr : ∀ i, ∀ θᵢ ∈ T i, ∀ aᵢ : A i,
      G.interimPayoffAction μ B i θᵢ aᵢ s ≤ G.interimPayoff μ B i θᵢ s) :
    G.IsBNE μ s := by
  apply G.isBNE_of_ae_interim μ B hmeas s hint
  intro i
  filter_upwards [mem_ae_iff.mpr (hT i)] with θᵢ hθ
  exact hbr i θᵢ hθ

end Real

end MathEconLib.GameTheory.BayesianGame

end
