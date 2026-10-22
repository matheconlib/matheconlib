/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import MathEconLib.GameTheory.Strategic.Basic
public import MathEconLib.Mechanism.Core.SolutionConcepts

/-!
# Strategic games induced by mechanisms

With the agents' valuations evaluated at a fixed profile of true types, a mechanism induces a
strategic game. Each agent chooses an action and receives the quasilinear utility of the resulting
outcome and signed transfer, evaluated at the true type profile. Only the actions vary across the
game; the true types do not, so valuations that depend on other agents' types are evaluated at
their true values, whatever those agents choose.

In a direct mechanism the actions are type reports, so dominant-strategy incentive compatibility is
equivalent to every agent's truthful report being weakly dominant in every such game. The truthful
profile is then a Nash equilibrium at every true type profile.

## Main definitions

* `QuasilinearEnvironment.utilityGame`: The strategic game in which agents choose mechanism actions
  and receive their utilities at a fixed true type profile.

## Main statements

* `DirectMechanism.IsDSIC.isDominant`: Incentive compatibility makes every truthful report dominant.
* `DirectMechanism.isDSIC_iff_isDominant`: Truthful reporting is dominant in every utility game
  when the direct mechanism is dominant-strategy incentive compatible.
* `DirectMechanism.IsDSIC.isNash`: Truthful reporting is a Nash equilibrium of every utility game
  of a dominant-strategy incentive-compatible mechanism.

## Tags

mechanism design, strategic games, incentive compatibility, dominant strategies, nash equilibrium
-/

@[expose] public section

open MathEconLib.GameTheory

universe uI uT uA uO

namespace MathEconLib.Mechanism

variable {I : Type uI} {T : I → Type uT} {A : I → Type uA} {O : Type uO}

namespace QuasilinearEnvironment

variable (E : QuasilinearEnvironment I T O)

/-- The strategic game of agents' actions in mechanism `M` at the fixed true type profile `θ`. Each
agent receives the utility of the chosen outcome and signed transfer evaluated at `θ`. -/
@[simps] def utilityGame (M : Mechanism I A O) (θ : Profile T) : StrategicGame I A ℝ where
  payoff i a := E.utility M i θ a

end QuasilinearEnvironment

namespace DirectMechanism

variable [DecidableEq I] (E : QuasilinearEnvironment I T O) (M : DirectMechanism I T O)

/-- In a dominant-strategy incentive-compatible direct mechanism, each agent's truthful report is
weakly dominant in the utility game at every true type profile. -/
lemma IsDSIC.isDominant (h : IsDSIC E M) (θ : Profile T) (i : I) :
    StrategicGame.Strategy.IsDominant (G := E.utilityGame M θ) (θ i) := by
  intro s
  rw [StrategicGame.Strategy.le_iff']
  intro r
  simpa only [QuasilinearEnvironment.utilityGame_payoff, Function.update_idem] using
    h i θ (Function.update r i s)

/-- A direct mechanism is dominant-strategy incentive compatible when every agent's truthful report
is weakly dominant in the utility game at every true type profile. -/
theorem isDSIC_iff_isDominant :
    IsDSIC E M ↔ ∀ θ i,
      StrategicGame.Strategy.IsDominant (G := E.utilityGame M θ) (θ i) := by
  constructor
  · exact IsDSIC.isDominant E M
  · intro h i θ r
    have hdominant := StrategicGame.Strategy.le_iff'.1 (h θ i (r i)) r
    simpa only [QuasilinearEnvironment.utilityGame_payoff, Function.update_eq_self] using
      hdominant

/-- In a dominant-strategy incentive-compatible direct mechanism, truthful reporting is a Nash
equilibrium of the utility game at every true type profile. -/
theorem IsDSIC.isNash (h : IsDSIC E M) (θ : Profile T) :
    (E.utilityGame M θ).IsNash θ :=
  StrategicGame.isNash_of_isDominant (h.isDominant E M θ)

end DirectMechanism

end MathEconLib.Mechanism

end
