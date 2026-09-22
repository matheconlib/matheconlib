/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import MathEconLib.GameTheory.Strategic.Bayesian.Game
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Measurable strategies and ex-ante payoffs

Each player's pure strategy is a measurable function of their own type. A common prior over type
profiles determines ex-ante expected utility and may correlate the players' types. Measurable
strategies induce measurable realized payoffs when utility is jointly measurable. Bounded realized
payoffs are integrable under a finite type-profile measure.

## Main definitions

* `BayesianGame.Strategy`: Measurable pure strategy profiles.
* `BayesianGame.measurableActionProfile`: Realized actions as a function of the type profile.
* `BayesianGame.exAntePayoff`: Payoff integrated against the type-profile measure.
* `BayesianGame.IncumbentPayoffsIntegrable`: Integrability of every player's realized payoff.
* `BayesianGame.replace`: Unilateral replacement of a measurable strategy.

## Main statements

* `BayesianGame.measurable_payoff_comp`: Measurability of realized payoffs.
* `BayesianGame.integrable_payoff_comp_of_bdd`: Bounded measurable realized payoffs are integrable
  under finite type-profile measures.

## Tags

bayesian game, measurable strategy, ex-ante payoff, integrability
-/

@[expose] public noncomputable section

open MeasureTheory

namespace MathEconLib.GameTheory.BayesianGame

universe uI uT uA uV

variable {I : Type uI} {Θ : I → Type uT} {A : I → Type uA} {V : Type uV}
  [∀ i, MeasurableSpace (Θ i)] [∀ i, MeasurableSpace (A i)]

/-- A measurable pure strategy profile depends only on each player's own type. -/
-- The game argument identifies the type and action carriers of the strategy.
def Strategy (_G : BayesianGame I Θ A V) := ∀ i, {f : Θ i → A i // Measurable f}

/-- Coerce a measurable strategy profile to its underlying profile of functions. -/
instance (G : BayesianGame I Θ A V) : CoeFun G.Strategy (fun _ => ∀ i, Θ i → A i) where
  coe s i := (s i).1

/-- The realized action profile under measurable strategies. -/
def measurableActionProfile (G : BayesianGame I Θ A V) (s : G.Strategy) (θ : ∀ i, Θ i) :
    ∀ i, A i := fun i => (s i).1 (θ i)

/-- Evaluation of a realized action. -/
@[simp] lemma measurableActionProfile_apply (G : BayesianGame I Θ A V) (s : G.Strategy)
    (θ : ∀ i, Θ i) (i : I) : G.measurableActionProfile s θ i = (s i).1 (θ i) := rfl

/-- The realized action profile is measurable in the full type profile. -/
lemma measurable_actionProfile (G : BayesianGame I Θ A V) (s : G.Strategy) :
    Measurable (G.measurableActionProfile s) :=
  measurable_pi_lambda _ fun i => (s i).2.comp (measurable_pi_apply i)

/-- Jointly measurable payoffs remain measurable after players use measurable strategies. -/
lemma measurable_payoff_comp [MeasurableSpace V] (G : BayesianGame I Θ A V)
    (hmeas : ∀ i, Measurable (fun p : (∀ j, A j) × (∀ j, Θ j) => G.payoff i p.1 p.2))
    (i : I) (s : G.Strategy) :
    Measurable (fun θ => G.payoff i (G.measurableActionProfile s θ) θ) :=
  (hmeas i).comp ((G.measurable_actionProfile s).prodMk measurable_id)

/-- The integral of player `i`'s realized payoff under the type-profile measure `μ`. For integrable
realized payoffs and a probability prior, this is the player's ex-ante expected utility. -/
def exAntePayoff [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (G : BayesianGame I Θ A V) (μ : Measure (∀ i, Θ i)) (i : I)
    (s : G.Strategy) : V :=
  ∫ θ, G.payoff i (G.measurableActionProfile s θ) θ ∂μ

/-- Every player's realized payoff is integrable under the type-profile measure. -/
def IncumbentPayoffsIntegrable [NormedAddCommGroup V] (G : BayesianGame I Θ A V)
    (μ : Measure (∀ i, Θ i))
    (s : G.Strategy) : Prop :=
  ∀ i, Integrable (fun θ => G.payoff i (G.measurableActionProfile s θ) θ) μ

/-- Replace one player's entire measurable strategy. -/
def replace [DecidableEq I] (G : BayesianGame I Θ A V) (s : G.Strategy) (i : I)
    (f : {f : Θ i → A i // Measurable f}) : G.Strategy := Function.update s i f

/-- The deviating player uses the replacement strategy. -/
@[simp] lemma replace_self [DecidableEq I] (G : BayesianGame I Θ A V) (s : G.Strategy)
    (i : I) (f : {f : Θ i → A i // Measurable f}) : G.replace s i f i = f :=
  Function.update_self ..

/-- A unilateral strategy replacement preserves every opponent's strategy. -/
lemma replace_of_ne [DecidableEq I] (G : BayesianGame I Θ A V) (s : G.Strategy)
    (i : I) (f : {f : Θ i → A i // Measurable f}) {j : I} (h : j ≠ i) :
    G.replace s i f j = s j := Function.update_of_ne h ..

/-- Bounded measurable realized payoffs are integrable under a finite type-profile measure. -/
lemma integrable_payoff_comp_of_bdd [NormedAddCommGroup V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] (G : BayesianGame I Θ A V)
    (μ : Measure (∀ i, Θ i)) [IsFiniteMeasure μ]
    (hmeas : ∀ i, Measurable (fun p : (∀ j, A j) × (∀ j, Θ j) => G.payoff i p.1 p.2))
    (i : I) (s : G.Strategy) {C : ℝ}
    (hC : ∀ θ, ‖G.payoff i (G.measurableActionProfile s θ) θ‖ ≤ C) :
    Integrable (fun θ => G.payoff i (G.measurableActionProfile s θ) θ) μ :=
  Integrable.of_bound (G.measurable_payoff_comp hmeas i s).aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)

end MathEconLib.GameTheory.BayesianGame

end
