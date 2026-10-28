/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import MathEconLib.GameTheory.Strategic.Outcome

/-!
# Independent mixed strategies

Independent randomization assigns each player a probability measure on their action space. The
mixed extension integrates strategic payoffs against the product of those measures in a complete
real normed space. These integrals represent expected payoffs when the payoff functions are
integrable; a nonintegrable function has Bochner integral zero. Mixed Nash equilibrium requires
integrable incumbent payoffs and compares unilateral deviations with integrable deviator payoffs.
The bare `mixedNashProblem.IsEquilibrium` supplies only the deviation inequalities and can admit
nonintegrable incumbents; `IsMixedNash` expresses the economic equilibrium concept.

## Main definitions

* `StrategicGame.Bounded` requires bounded payoff ranges for every player.
* `StrategicGame.MixedStrategy` gives profiles of independent action laws.
* `StrategicGame.mixedExtension` integrates payoffs against independent action laws.
* `StrategicGame.MixedPayoffsIntegrable` requires integrable incumbent payoffs.
* `StrategicGame.mixedNashProblem` admits unilateral deviations with integrable deviator payoffs.
* `StrategicGame.IsMixedNash` is mixed equilibrium with integrable incumbent payoffs.

## Main statements

* `StrategicGame.isMixedNash_iff` gives integrability and the admissible payoff inequalities.
* `StrategicGame.isMixedNash_iff_isNash_of_integrable` identifies mixed equilibrium with Nash
  equilibrium of the integral extension when all unilateral payoffs are integrable.
* `StrategicGame.isMixedNash_iff_isNash` identifies mixed and integral-extension Nash equilibria
  for bounded measurable games in second countable payoff spaces.
* `StrategicGame.mixedExtension_eq_ofOutcome` identifies the mixed extension with expected
  utilities on distributions over action profiles.

## Tags

mixed strategies, expected payoffs, nash equilibrium, probability measures
-/

@[expose] public noncomputable section

open MeasureTheory

namespace MathEconLib.GameTheory.StrategicGame

variable {I : Type*} {A : I → Type*} {V : Type*}

-- The game parameter identifies the strategic game whose action profiles serve as outcomes.
set_option linter.unusedVariables false in
/-- The action profile itself as the outcome of a game. -/
def outcomeGame (G : StrategicGame I A V) : OutcomeGame I A (∀ i, A i) where
  outcome := id

/-- Utilities on action-profile outcomes are the game's strategic payoffs. -/
def payoffStructure (G : StrategicGame I A V) : PayoffStructure I (∀ i, A i) V where
  payoff := G.payoff

/-- A strategic game is bounded when every player's payoff has bounded range. -/
protected class Bounded [Bornology V] (G : StrategicGame I A V) : Prop where
  /-- Boundedness of each player's payoffs over all action profiles. -/
  isBounded_payoff_range : ∀ i, Bornology.IsBounded (Set.range (G.payoff i))

export Bounded (isBounded_payoff_range)

/-- Bounded strategic payoffs give bounded utilities on action-profile outcomes. -/
instance [Bornology V] (G : StrategicGame I A V) [G.Bounded] : G.payoffStructure.Bounded :=
  ⟨G.isBounded_payoff_range⟩

section Measurable

variable [∀ i, MeasurableSpace (A i)]

/-- Each player chooses a probability measure on their action space. -/
abbrev MixedStrategy (A : I → Type*) [∀ i, MeasurableSpace (A i)] :=
  ∀ i, ProbabilityMeasure (A i)

/-- Every player's payoff is measurable on the action-profile space. -/
protected class Measurable [MeasurableSpace V] (G : StrategicGame I A V) : Prop where
  /-- Each payoff function is measurable. -/
  measurable_payoff : ∀ i, Measurable (G.payoff i)

/-- The action-profile outcome map is measurable. -/
instance (G : StrategicGame I A V) : G.outcomeGame.Measurable := ⟨measurable_id⟩

/-- Measurable strategic payoffs give measurable utilities on action-profile outcomes. -/
instance [MeasurableSpace V] (G : StrategicGame I A V) [G.Measurable] :
    G.payoffStructure.Measurable :=
  ⟨Measurable.measurable_payoff⟩

/-- Independent mixed actions yield the Bochner integral of each strategic payoff.

The integral is an expected payoff when the payoff function is integrable against the independent
product law; a nonintegrable function has integral zero.

For real-valued payoffs, the economic interpretation uses the expected-utility modeling assumption
described in `PayoffStructure.expected`. -/
def mixedExtension [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [Fintype I] (G : StrategicGame I A V) :
    StrategicGame I (fun i ↦ ProbabilityMeasure (A i)) V where
  payoff i σ := ∫ a, G.payoff i a ∂Measure.pi (fun j ↦ (σ j : Measure (A j)))

/-- Integrating strategic payoffs agrees with the outcome-distribution construction. -/
lemma mixedExtension_eq_ofOutcome [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] [Fintype I] (G : StrategicGame I A V) :
    G.mixedExtension = ofOutcome G.outcomeGame.mixed G.payoffStructure.expected := by
  unfold mixedExtension ofOutcome
  congr 1
  funext i σ
  simp [OutcomeGame.mixed, outcomeGame, payoffStructure, PayoffStructure.expected]

/-- Every player's payoff is integrable under the independent incumbent action laws. -/
def MixedPayoffsIntegrable [NormedAddCommGroup V] [Fintype I]
    (G : StrategicGame I A V) (σ : MixedStrategy A) : Prop :=
  ∀ i, Integrable (G.payoff i) (Measure.pi (fun j ↦ (σ j : Measure (A j))))

/-- In a second countable payoff space, bounded measurable payoffs are integrable under every
independent action law. -/
lemma integrable_payoff_of_bdd [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V] [Fintype I] (G : StrategicGame I A V) [G.Measurable]
    (i : I) (σ : MixedStrategy A) (C : ℝ) (hbound : ∀ a, ‖G.payoff i a‖ ≤ C) :
    Integrable (G.payoff i) (Measure.pi (fun j ↦ (σ j : Measure (A j)))) :=
  Integrable.of_bound (Measurable.measurable_payoff (G := G) i).aestronglyMeasurable C
    (Filter.Eventually.of_forall hbound)

/-- In a second countable payoff space, bounded measurable games have integrable payoffs under all
independent action laws. -/
lemma integrable_payoff_of_bounded [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V] [Fintype I] (G : StrategicGame I A V) [G.Measurable] [G.Bounded]
    (i : I) (σ : MixedStrategy A) :
    Integrable (G.payoff i) (Measure.pi (fun j ↦ (σ j : Measure (A j)))) := by
  obtain ⟨C, hC⟩ := (isBounded_iff_forall_norm_le.mp (G.isBounded_payoff_range i))
  exact G.integrable_payoff_of_bdd i σ C (fun a ↦ hC _ (Set.mem_range_self a))

/-- Players may replace their own probability law when their resulting payoff is integrable; each
player's value is the payoff integral against the independent action laws.

Its `IsEquilibrium` predicate supplies only the deviation inequalities and can hold for
nonintegrable incumbent payoffs, whose Bochner integrals are zero. Mixed Nash equilibrium is
`IsMixedNash`, which additionally requires integrability of every incumbent payoff. -/
def mixedNashProblem [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [Fintype I] [DecidableEq I] (G : StrategicGame I A V) :
    EquilibriumProblem (MixedStrategy A) I V where
  deviation i σ σ' := (∃ τ, σ' = Function.update σ i τ) ∧
    Integrable (G.payoff i) (Measure.pi (fun j ↦ (σ' j : Measure (A j))))
  value := G.mixedExtension.payoff

/-- Admissible mixed deviations change one player's law and give that player an integrable
payoff. -/
@[simp] lemma mixedNashProblem_deviation_iff [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] [Fintype I] [DecidableEq I] (G : StrategicGame I A V)
    (i : I) (σ σ' : MixedStrategy A) :
    G.mixedNashProblem.deviation i σ σ' ↔ (∃ τ, σ' = Function.update σ i τ) ∧
      Integrable (G.payoff i) (Measure.pi (fun j ↦ (σ' j : Measure (A j)))) :=
  Iff.rfl

/-- The mixed equilibrium problem evaluates each player by their payoff integral. -/
@[simp] lemma mixedNashProblem_value_eq [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] [Fintype I] [DecidableEq I] (G : StrategicGame I A V)
    (i : I) (σ : MixedStrategy A) :
    G.mixedNashProblem.value i σ = G.mixedExtension.payoff i σ :=
  rfl

/-- The economic mixed Nash equilibrium has integrable incumbent payoffs, and every unilateral
deviation with integrable deviator payoff gives at most the incumbent expected payoff. -/
structure IsMixedNash [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [Fintype I] [DecidableEq I] [LE V] (G : StrategicGame I A V)
    (σ : MixedStrategy A) : Prop where
  /-- Every admissible unilateral deviation weakly lowers the deviator's expected payoff. -/
  isEquilibrium : G.mixedNashProblem.IsEquilibrium σ
  /-- Every incumbent payoff is integrable under the independent action laws. -/
  integrable : G.MixedPayoffsIntegrable σ

/-- Mixed equilibrium requires integrable incumbent payoffs and the payoff inequalities for all
unilateral deviations with integrable deviator payoffs. -/
@[simp] lemma isMixedNash_iff [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [Fintype I] [DecidableEq I] [LE V] (G : StrategicGame I A V) (σ : MixedStrategy A) :
    G.IsMixedNash σ ↔ G.MixedPayoffsIntegrable σ ∧
      ∀ i τ, Integrable (G.payoff i)
        (Measure.pi (fun j ↦ (Function.update σ i τ j : Measure (A j)))) →
        G.mixedExtension.payoff i (Function.update σ i τ) ≤ G.mixedExtension.payoff i σ := by
  constructor
  · intro h
    exact ⟨h.integrable, fun i τ hint ↦ h.isEquilibrium i _ ⟨⟨τ, rfl⟩, hint⟩⟩
  · rintro ⟨hint, h⟩
    refine ⟨?_, hint⟩
    rintro i σ' ⟨⟨τ, rfl⟩, hτ⟩
    exact h i τ hτ

/-- Nash equilibrium of the integral extension gives mixed equilibrium when incumbent payoffs are
integrable. -/
lemma IsMixedNash.of_isNash [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [Fintype I] [DecidableEq I] [LE V] {G : StrategicGame I A V} {σ : MixedStrategy A}
    (hσ : G.mixedExtension.IsNash σ) (hint : G.MixedPayoffsIntegrable σ) : G.IsMixedNash σ :=
  ⟨fun i σ' hdev ↦ hσ i σ' hdev.1, hint⟩

/-- When every unilateral payoff is integrable, mixed Nash equilibrium is Nash equilibrium of the
integral extension. -/
lemma isMixedNash_iff_isNash_of_integrable [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] [Fintype I] [DecidableEq I] [LE V] (G : StrategicGame I A V)
    (σ : MixedStrategy A)
    (hint : ∀ i τ, Integrable (G.payoff i)
      (Measure.pi (fun j ↦ (Function.update σ i τ j : Measure (A j))))) :
    G.IsMixedNash σ ↔ G.mixedExtension.IsNash σ := by
  constructor
  · intro h
    rw [isNash_iff]
    exact fun i τ ↦ ((isMixedNash_iff G σ).1 h).2 i τ (hint i τ)
  · intro h
    apply IsMixedNash.of_isNash h
    intro i
    simpa only [Function.update_eq_self] using hint i (σ i)

/-- In a second countable payoff space, bounded measurable payoffs make mixed Nash equilibrium
equivalent to Nash equilibrium of the integral extension. -/
lemma isMixedNash_iff_isNash_of_bdd [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    [Fintype I] [DecidableEq I] [LE V] (G : StrategicGame I A V) [G.Measurable]
    (σ : MixedStrategy A) (hbound : ∀ i, ∃ C, ∀ a, ‖G.payoff i a‖ ≤ C) :
    G.IsMixedNash σ ↔ G.mixedExtension.IsNash σ := by
  apply isMixedNash_iff_isNash_of_integrable
  intro i τ
  obtain ⟨C, hC⟩ := hbound i
  exact G.integrable_payoff_of_bdd i (Function.update σ i τ) C hC

/-- In a second countable payoff space, bounded measurable games have the same mixed Nash
equilibria as Nash equilibria of their integral extension. -/
lemma isMixedNash_iff_isNash [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    [Fintype I] [DecidableEq I] [LE V] (G : StrategicGame I A V) [G.Measurable] [G.Bounded]
    (σ : MixedStrategy A) : G.IsMixedNash σ ↔ G.mixedExtension.IsNash σ :=
  G.isMixedNash_iff_isNash_of_integrable σ
    (fun i τ ↦ G.integrable_payoff_of_bounded i (Function.update σ i τ))

end Measurable

section Continuous

variable [∀ i, TopologicalSpace (A i)]

/-- Every player's payoff varies continuously with the full action profile. -/
protected class Continuous [TopologicalSpace V] (G : StrategicGame I A V) : Prop where
  /-- Each payoff function is continuous. -/
  continuous_payoff : ∀ i, Continuous (G.payoff i)

/-- The action-profile outcome map is continuous. -/
instance (G : StrategicGame I A V) : G.outcomeGame.Continuous := ⟨continuous_id⟩

/-- Continuous strategic payoffs give continuous utilities on action-profile outcomes. -/
instance [TopologicalSpace V] (G : StrategicGame I A V) [G.Continuous] :
    G.payoffStructure.Continuous :=
  ⟨Continuous.continuous_payoff⟩

end Continuous

end MathEconLib.GameTheory.StrategicGame
