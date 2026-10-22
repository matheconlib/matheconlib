/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import MathEconLib.Mechanism
public import MathEconLibTest.Mechanism.Core

/-!
# Posted-price strategic and Bayesian games

At a posted price of one, a buyer with value two earns one by reporting high, while a buyer with
value zero loses one by reporting high. Dominant-strategy incentives make the truthful report
weakly dominant and give truthful Nash equilibrium at either type. The strategic and Bayesian
utility games agree at each fixed type.

## Main statements

* `postedPrice_truthful_isDominant`: Truthful reports are weakly dominant at every buyer type.
* `postedPrice_truthful_isNash`: Truthful reporting is Nash at every buyer type.
* `postedPrice_induced_payoff_high` and `postedPrice_induced_payoff_low_misreport`: Purchasing
  gives a high-value buyer utility one and a low-value buyer utility minus one.
* `postedPrice_fixedType_agreement`: Fixing types in the Bayesian game gives the utility game.
* `postedPrice_fixedType_truthful_isNash`: Truth is Nash in the fixed-type Bayesian view.

## Tags

posted price, mechanism design, dominance, nash equilibrium, bayesian games
-/

@[expose] public section

open MathEconLib.GameTheory MathEconLib.Mechanism

namespace MathEconLib.Tests.Mechanism

/-! ## Posted-price incentives and induced games -/

/-- The posted-price buyer's truthful report is weakly dominant at every true type. -/
lemma postedPrice_truthful_isDominant (θ : Unit → Bool) (i : Unit) :
    StrategicGame.Strategy.IsDominant
      (G := postedPriceEnvironment.utilityGame postedPriceMechanism θ) (i := i) (θ i) :=
  DirectMechanism.IsDSIC.isDominant
    postedPriceEnvironment postedPriceMechanism postedPrice_isDSIC θ i

/-- The posted-price buyer reports truthfully in Nash equilibrium at every true type. -/
lemma postedPrice_truthful_isNash (θ : Unit → Bool) :
    (postedPriceEnvironment.utilityGame postedPriceMechanism θ).IsNash θ :=
  DirectMechanism.IsDSIC.isNash postedPriceEnvironment postedPriceMechanism postedPrice_isDSIC θ

/-- A truthful buyer with value two earns one after paying the posted price. -/
lemma postedPrice_induced_payoff_high :
    (postedPriceMechanism.inducedBayesianGame postedPriceEnvironment).payoff
      () (fun _ ↦ true) (fun _ ↦ true) = 1 := by
  rw [Mechanism.inducedBayesianGame_payoff]
  norm_num [QuasilinearEnvironment.utility, postedPriceEnvironment, postedPriceMechanism,
    QuasilinearEnvironment.ofPrivate]

/-- A buyer with value zero loses one by reporting high and purchasing the good. -/
lemma postedPrice_induced_payoff_low_misreport :
    (postedPriceMechanism.inducedBayesianGame postedPriceEnvironment).payoff
      () (fun _ ↦ true) (fun _ ↦ false) = -1 := by
  rw [Mechanism.inducedBayesianGame_payoff]
  norm_num [QuasilinearEnvironment.utility, postedPriceEnvironment, postedPriceMechanism,
    QuasilinearEnvironment.ofPrivate]

/-- Fixing the buyer's true type in the Bayesian game recovers the posted-price utility game. -/
lemma postedPrice_fixedType_agreement (θ : Unit → Bool) :
    (postedPriceMechanism.inducedBayesianGame postedPriceEnvironment).strategicGameAt θ =
      postedPriceEnvironment.utilityGame postedPriceMechanism θ :=
  Mechanism.inducedBayesianGame_strategicGameAt postedPriceMechanism postedPriceEnvironment θ

/-- Truthful reporting is Nash in the fixed-type view of the posted-price Bayesian game. -/
lemma postedPrice_fixedType_truthful_isNash (θ : Unit → Bool) :
    ((postedPriceMechanism.inducedBayesianGame postedPriceEnvironment).strategicGameAt θ).IsNash
      θ := by
  rw [postedPrice_fixedType_agreement]
  exact postedPrice_truthful_isNash θ

end MathEconLib.Tests.Mechanism

end
