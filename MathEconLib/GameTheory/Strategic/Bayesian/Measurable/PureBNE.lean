/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import MathEconLib.GameTheory.Equilibrium.Problem
public import MathEconLib.GameTheory.Strategic.Bayesian.Measurable.Game

/-!
# Pure Bayesian Nash equilibrium under a common prior

A measurable pure strategy profile is a Bayesian Nash equilibrium when every player's realized
payoff is integrable and every integrable unilateral strategy deviation weakly lowers their ex-ante
payoff. Deviations may change the action prescribed at every type of the deviating player.

## Main definitions

* `BayesianGame.bneProblem`: The equilibrium problem of integrable unilateral strategy deviations.
* `BayesianGame.IsBNE`: Equilibrium together with incumbent payoff integrability.

## Main statements

* `BayesianGame.isBNE_iff`: The unilateral deviation inequalities and integrability requirement.

## Tags

bayesian nash equilibrium, pure strategy, ex-ante payoff, integrability
-/

@[expose] public noncomputable section

open MeasureTheory

namespace MathEconLib.GameTheory.BayesianGame

universe uI uT uA uV

variable {I : Type uI} {Θ : I → Type uT} {A : I → Type uA} {V : Type uV}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [∀ i, MeasurableSpace (Θ i)] [∀ i, MeasurableSpace (A i)]

/-- The equilibrium problem in which admissible deviations preserve opponents' strategies and give
the deviator an integrable realized payoff. Each player's value is their ex-ante payoff integral. -/
def bneProblem (G : BayesianGame I Θ A V) (μ : Measure (∀ i, Θ i)) :
    EquilibriumProblem G.Strategy I V where
  deviation i s s' := (∀ j, j ≠ i → s' j = s j) ∧
    Integrable (fun θ => G.payoff i (G.measurableActionProfile s' θ) θ) μ
  value i s := G.exAntePayoff μ i s

/-- An admissible deviation preserves opponents' strategies and gives the deviator an integrable
realized payoff. -/
@[simp] lemma bneProblem_deviation_iff (G : BayesianGame I Θ A V) (μ : Measure (∀ i, Θ i))
    (i : I) (s s' : G.Strategy) :
    (G.bneProblem μ).deviation i s s' ↔
      (∀ j, j ≠ i → s' j = s j) ∧
        Integrable (fun θ => G.payoff i (G.measurableActionProfile s' θ) θ) μ := Iff.rfl

/-- The equilibrium problem evaluates each player by their ex-ante payoff integral. -/
@[simp] lemma bneProblem_value_eq (G : BayesianGame I Θ A V) (μ : Measure (∀ i, Θ i))
    (i : I) (s : G.Strategy) : (G.bneProblem μ).value i s = G.exAntePayoff μ i s := rfl

/-- Pure Bayesian Nash equilibrium: Every integrable unilateral strategy deviation weakly lowers
ex-ante payoff, and incumbent payoffs are integrable under the common probability prior. -/
structure IsBNE [LE V] (G : BayesianGame I Θ A V) (μ : Measure (∀ i, Θ i)) [IsProbabilityMeasure μ]
    (s : G.Strategy) : Prop where
  /-- Every admissible unilateral deviation weakly lowers the deviator's expected payoff. -/
  isEquilibrium : (G.bneProblem μ).IsEquilibrium s
  /-- Every incumbent realized payoff is integrable under the common prior. -/
  integrable : G.IncumbentPayoffsIntegrable μ s

/-- Bayesian Nash equilibrium is equivalent to its unilateral deviation inequalities together with
integrability of all incumbent payoffs. -/
theorem isBNE_iff [LE V] (G : BayesianGame I Θ A V) (μ : Measure (∀ i, Θ i))
    [IsProbabilityMeasure μ]
    (s : G.Strategy) :
    G.IsBNE μ s ↔
      (∀ (i : I) (s' : G.Strategy), (∀ j, j ≠ i → s' j = s j) →
        Integrable (fun θ => G.payoff i (G.measurableActionProfile s' θ) θ) μ →
          G.exAntePayoff μ i s' ≤ G.exAntePayoff μ i s) ∧
      G.IncumbentPayoffsIntegrable μ s := by
  constructor
  · intro h
    exact ⟨fun i s' hagree hint => h.isEquilibrium i s' ⟨hagree, hint⟩, h.integrable⟩
  · rintro ⟨h, hint⟩
    exact ⟨fun i s' hs' => h i s' hs'.1 hs'.2, hint⟩

end MathEconLib.GameTheory.BayesianGame

end
