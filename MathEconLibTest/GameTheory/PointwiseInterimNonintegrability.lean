/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.GameTheory.Strategic.Bayesian.Measurable.Interim
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# A nonintegrable alternative at a positive-probability type

Player `false` has a singleton type and chooses a Boolean action. Player `true` observes a
uniform type in `(0, 1]` and has only one action. Choosing `false` gives the first player zero;
choosing `true` gives the reciprocal of the other player's type. Incumbent payoffs are integrable,
but the alternative is not conditionally integrable. Its totalized Bochner integral is zero, so
the legacy inequality-only interim predicate accepts the incumbent.

The singleton type has probability one. No modification of beliefs on a null type is involved.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set MathEconLib.GameTheory
open MathEconLib.GameTheory.BayesianPrior

namespace MathEconLibTest.GameTheory.PointwiseInterimNonintegrability

local instance : MeasurableSpace Bool := ⊤

/-- Player zero has no private information; player one observes a real type. -/
abbrev TypeSpace : Bool → Type
  | false => Unit
  | true => ℝ

/-- Only player zero can choose between actions. -/
abbrev ActionSpace : Bool → Type
  | false => Bool
  | true => Unit

instance (i : Bool) : MeasurableSpace (TypeSpace i) := by
  cases i <;> dsimp [TypeSpace] <;> infer_instance

instance (i : Bool) : MeasurableSpace (ActionSpace i) := by
  cases i <;> dsimp [ActionSpace] <;> infer_instance

/-- The real random variable is uniform on the unit interval. -/
def uniform : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)

instance : IsProbabilityMeasure uniform where
  measure_univ := by simp [uniform]

/-- Embed the real observation in the two-player type profile. -/
def profile (x : ℝ) : ∀ i, TypeSpace i
  | false => ()
  | true => x

lemma measurable_profile : Measurable profile := by
  apply Measurable.of_eval
  intro i
  cases i
  · exact measurable_const
  · exact measurable_id

/-- The common prior is a normalized probability law. -/
def prior : Measure (∀ i, TypeSpace i) := uniform.map profile

instance : IsProbabilityMeasure prior :=
  inferInstanceAs (IsProbabilityMeasure (uniform.map profile))

/-- The informative coordinate is independent of the other player's constant coordinate. -/
lemma independent_types : IsIndependentOfOpponents prior := by
  intro i
  cases i
  · have hown : (fun θ : ∀ j, TypeSpace j ↦ θ false) = fun _ ↦ () := by
      funext θ
      exact Subsingleton.elim (α := Unit) _ _
    rw [hown]
    exact indepFun_const_left () _
  · have hdrop : drop (Θ := TypeSpace) true = fun _ ↦ drop true (profile 0) := by
      funext θ j
      rcases j with ⟨j, hj⟩
      cases j
      · exact Subsingleton.elim (α := Unit) _ _
      · exact (hj rfl).elim
    rw [hdrop]
    exact indepFun_const_right _ _

/-- Constant opponent kernels disintegrate this independent common prior. -/
def beliefs : ConditionalBeliefs prior := independentBeliefs independent_types

/-- The uninformed player's opponent law is the uniform observation law in profile form. -/
lemma beliefs_false (t : TypeSpace false) :
    beliefs.opponents false t = uniform.map (fun x ↦ drop false (profile x)) := by
  change (uniform.map profile).map (drop false) = _
  exact Measure.map_map (measurable_drop false) measurable_profile

/-- The uninformed player's only type has probability one. -/
lemma singleton_type_probability : marginalType prior false {()} = 1 := by
  change (uniform.map profile).map (fun θ ↦ θ false) {()} = 1
  rw [Measure.map_map (measurable_pi_apply false) measurable_profile]
  simp only [Function.comp_def, profile]
  rw [Measure.map_apply measurable_const (measurableSet_singleton ())]
  simp

/-- A Boolean action switches the reciprocal payoff on; the other player always receives zero. -/
def game : BayesianGame Bool TypeSpace ActionSpace ℝ where
  payoff i a θ := match i with
    | false => if a false = true then (θ true)⁻¹ else 0
    | true => 0

/-- The incumbent chooses the safe zero-payoff action. -/
def incumbent : game.Strategy
  | false => ⟨fun _ ↦ false, measurable_const⟩
  | true => ⟨fun _ ↦ (), measurable_const⟩

/-- Every incumbent realized payoff is zero and hence integrable. -/
theorem incumbent_integrable : game.IncumbentPayoffsIntegrable prior incumbent := by
  intro i
  cases i <;> simp [game, BayesianGame.measurableActionProfile, incumbent]

/-- Reciprocal utility is not integrable on the uniform interval. -/
lemma reciprocal_not_integrable : ¬ Integrable (fun x : ℝ ↦ x⁻¹) uniform := by
  intro hint
  have hinterval : IntervalIntegrable (fun x : ℝ ↦ x⁻¹) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr hint
  norm_num at hinterval

/-- The chosen alternative has the reciprocal opponent-type integrand. -/
lemma alternative_integrand (θo : OpponentProfile TypeSpace false) :
    game.interimPayoffActionIntegrand false () true incumbent θo =
      (θo ⟨true, by decide⟩)⁻¹ := by
  simp [BayesianGame.interimPayoffActionIntegrand, game]

/-- The alternative is strictly positive almost surely, although its raw integral is zero. -/
theorem alternative_positive :
    ∀ᵐ θo ∂(beliefs.opponents false ()),
      0 < game.interimPayoffActionIntegrand false () true incumbent θo := by
  rw [beliefs_false]
  have hmap : Measurable (fun x ↦ drop false (profile x)) :=
    (measurable_drop false).comp measurable_profile
  have hcoord : Measurable (fun θo : OpponentProfile TypeSpace false ↦
      θo ⟨true, by decide⟩) := measurable_pi_apply _
  simp only [alternative_integrand]
  apply (ae_map_iff hmap.aemeasurable
    (p := fun θo : OpponentProfile TypeSpace false ↦
      (0 : ℝ) < (θo ⟨true, by decide⟩)⁻¹)
    (measurableSet_lt measurable_const hcoord.inv)).2
  change ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), 0 < x⁻¹
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact inv_pos.mpr hx.1

/-- The alternative's conditional payoff is not integrable at the only own type. -/
theorem alternative_not_integrable :
    ¬ Integrable (game.interimPayoffActionIntegrand false () true incumbent)
      (beliefs.opponents false ()) := by
  rw [beliefs_false]
  have hcoord : Measurable (fun θo : OpponentProfile TypeSpace false ↦
      θo ⟨true, by decide⟩) := measurable_pi_apply _
  have hpay : Measurable (game.interimPayoffActionIntegrand false () true incumbent) := by
    change Measurable (fun θo : OpponentProfile TypeSpace false ↦
      (θo ⟨true, by decide⟩)⁻¹)
    exact hcoord.inv
  have hmap : Measurable (fun x ↦ drop false (profile x)) :=
    (measurable_drop false).comp measurable_profile
  intro hint
  apply reciprocal_not_integrable
  simpa [Function.comp_def, alternative_integrand, drop, profile] using
    (integrable_map_measure hpay.aestronglyMeasurable hmap.aemeasurable).mp hint

/-- Every prescribed conditional payoff is integrable; the defect is an unused alternative. -/
theorem incumbent_conditional_integrable (i : Bool) (t : TypeSpace i) :
    Integrable (game.interimPayoffActionIntegrand i t ((incumbent i).1 t) incumbent)
      (beliefs.opponents i t) := by
  cases i <;> change Integrable (fun _ ↦ (0 : ℝ)) _
  all_goals exact integrable_const _

/-- Both Boolean choices have raw interim integral zero, including the nonintegrable choice. -/
theorem interimPayoffAction_eq_zero (i : Bool) (t : TypeSpace i) (a : ActionSpace i) :
    game.interimPayoffAction prior beliefs i t a incumbent = 0 := by
  cases i
  · cases t
    cases a
    · simp [BayesianGame.interimPayoffAction, BayesianGame.interimPayoffActionIntegrand, game]
    · exact integral_undef alternative_not_integrable
  · simp [BayesianGame.interimPayoffAction, BayesianGame.interimPayoffActionIntegrand, game]

/-- Prescribed play has the genuine conditional expectation zero. -/
theorem interimPayoff_eq_zero (i : Bool) (t : TypeSpace i) :
    game.interimPayoff prior beliefs i t incumbent = 0 :=
  interimPayoffAction_eq_zero i t _

/-- The inequality-only legacy interim predicate accepts the zero-payoff incumbent. -/
theorem raw_interim_best_response : game.IsAEInterimBestResponse prior beliefs incumbent := by
  intro i
  exact Filter.Eventually.of_forall fun t a ↦ by
    rw [interimPayoffAction_eq_zero, interimPayoff_eq_zero]

/-- The existing simultaneous conditional-integrability guard detects the alternative. -/
theorem not_hasIntegrableInterimDeviations :
    ¬ game.HasIntegrableInterimDeviations prior beliefs incumbent := by
  intro h
  obtain ⟨t, ht⟩ := (h false).exists
  cases t
  exact alternative_not_integrable (ht true)

/-- Restricting comparisons to conditionally integrable actions silently accepts the incumbent. -/
theorem integrability_filtered_comparisons (i : Bool) (t : TypeSpace i) (a : ActionSpace i)
    (_ha : Integrable (game.interimPayoffActionIntegrand i t a incumbent)
      (beliefs.opponents i t)) :
    game.interimPayoffAction prior beliefs i t a incumbent ≤
      game.interimPayoff prior beliefs i t incumbent := by
  rw [interimPayoffAction_eq_zero, interimPayoff_eq_zero]

/-- The guarded contract rejects the nonintegrable alternative even though prescribed payoffs
are globally and conditionally integrable and the raw comparisons all hold. -/
theorem not_isPointwiseInterimBestResponse :
    ¬ game.IsPointwiseInterimBestResponse prior beliefs incumbent :=
  fun h ↦ alternative_not_integrable (h.integrable false () true)

end MathEconLibTest.GameTheory.PointwiseInterimNonintegrability

end
