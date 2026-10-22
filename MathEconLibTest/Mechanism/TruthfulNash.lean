/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import MathEconLib.Mechanism

/-!
# Truthful Nash equilibrium without dominant-strategy incentives

Two agents, indexed by `Bool`, have Boolean types and reports. The outcome is the reported profile,
and both agents receive zero transfers. Agent `false` values an outcome at zero when its own report
equals its type, at minus one when only its own report differs from its type, and at one when each
agent's report differs from that agent's type. Agent `true` always has value zero. Thus agent
`false`'s valuation depends on the other agent's true type.

Truthful reporting is a Nash equilibrium at every true type profile. Nevertheless, if both agents
have type `false` and the other agent reports `true`, the first agent profits by also reporting
`true`. Truthful Nash equilibrium therefore does not imply dominant-strategy incentive
compatibility when values are interdependent.

## Main definitions

* `environment`: The interdependent valuation environment.
* `mechanism`: The direct mechanism choosing the reported profile with zero transfers.

## Main statements

* `environment_not_isPrivateValues`: The environment does not have private values.
* `truthful_isNash`: Every truthful profile is a Nash equilibrium of its utility game.
* `lie_profitable`: A lie strictly improves utility when the other agent lies.
* `mechanism_not_isDSIC`: The mechanism is not dominant-strategy incentive compatible.

## Tags

mechanism design, interdependent values, nash equilibrium, incentive compatibility
-/

@[expose] public section

open MathEconLib.Mechanism

namespace MathEconLib.Tests.MechanismTruthfulNash

/-- The Boolean environment where agent `false` gets zero when its own report equals its type,
minus one when only its own report differs from its type, and one when each agent's report differs
from that agent's type. Agent `true` gets zero. -/
def environment : QuasilinearEnvironment Bool (fun _ => Bool) (Bool → Bool) where
  value i θ o := if i then 0 else
    if o false = θ false then 0 else if o true = θ true then -1 else 1

/-- Each agent reports a Boolean type; the mechanism chooses that profile and pays no transfers. -/
def mechanism : DirectMechanism Bool (fun _ => Bool) (Bool → Bool) where
  outcome r := r
  transfer _ _ := 0

/-- Changing only the other agent's true type can change agent `false`'s value of a fixed
outcome. -/
lemma environment_not_isPrivateValues : ¬ environment.IsPrivateValues := by
  intro hprivate
  have hvalue := congrFun (hprivate false (fun _ => false) (fun i => i) rfl) (fun _ => true)
  norm_num [environment] at hvalue

/-- Every agent's utility is zero when everyone reports truthfully. -/
@[simp] lemma utility_truthful (i : Bool) (θ : Bool → Bool) :
    environment.utility mechanism i θ θ = 0 := by
  cases i <;> simp [QuasilinearEnvironment.utility, environment, mechanism]

/-- Every truthful profile is a Nash equilibrium, for every true type profile. -/
lemma truthful_isNash (θ : Bool → Bool) :
    (environment.utilityGame mechanism θ).IsNash θ := by
  rw [GameTheory.StrategicGame.isNash_iff]
  intro i s
  cases i
  · by_cases hs : s = θ false
    · simp [QuasilinearEnvironment.utilityGame, QuasilinearEnvironment.utility,
        environment, mechanism, hs]
    · simp [QuasilinearEnvironment.utilityGame, QuasilinearEnvironment.utility,
        environment, mechanism, hs]
  · simp [QuasilinearEnvironment.utilityGame, QuasilinearEnvironment.utility,
      environment, mechanism]

/-- When both true types are `false` and the other agent reports `true`, agent `false` strictly
prefers reporting `true` to reporting `false`: The utilities are one and zero, respectively. -/
lemma lie_profitable :
    environment.utility mechanism false (fun _ => false)
        (Function.update (fun _ => true) false false) <
      environment.utility mechanism false (fun _ => false) (fun _ => true) := by
  norm_num [QuasilinearEnvironment.utility, environment, mechanism]

/-- The mechanism is not dominant-strategy incentive compatible in the interdependent valuation
environment. -/
lemma mechanism_not_isDSIC : ¬ DirectMechanism.IsDSIC environment mechanism := by
  intro hdsic
  exact (not_le_of_gt lie_profitable) (hdsic false (fun _ => false) (fun _ => true))

end MathEconLib.Tests.MechanismTruthfulNash

end
