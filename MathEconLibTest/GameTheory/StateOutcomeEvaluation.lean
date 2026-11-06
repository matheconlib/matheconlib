/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib
public import MathEconLibTest.Mechanism.PostedPriceGames

/-!
# Shared outcome evaluation through the public API

The generic contracts preserve independent universes and require neither an order on utilities
nor probability data. The existing price-one mechanism recovers its two induced-game views and
its true-type payoff controls through shared outcome evaluation.

The pointwise Cournot regressions use the quantity domain and profit formula of the canonical
client in PR #176, tracked by #193. They check the one-third profile, feasible shutdown, and the
price change caused by a deviation. Competition and equilibrium results remain in that client.
-/

@[expose] public noncomputable section

open MathEconLib.GameTheory MathEconLib.Mechanism
open MathEconLib.Tests.Mechanism

namespace MathEconLibTest.GameTheory.StateOutcomeEvaluation

universe uI uS uT uA uX uV

variable {I : Type uI} {S : Type uS} {T : I → Type uT} {A : I → Type uA}
  {X : Type uX} {V : Type uV}

example (P : PayoffStructure I (S × X) V) (s : S) (i : I) (x : X) :
    (P.atState s).payoff i x = P.payoff i (s, x) :=
  P.atState_payoff s i (x := x)

example (g : OutcomeGame I A X) (P : PayoffStructure I (S × X) V)
    (s : S) (i : I) (a : (i : I) → A i) :
    (StrategicGame.ofOutcome g (P.atState s)).payoff i a = P.payoff i (s, g.outcome a) :=
  rfl

example (g : OutcomeGame I A X) (P : PayoffStructure I (((i : I) → T i) × X) V)
    (i : I) (a : (i : I) → A i) (θ : (i : I) → T i) :
    (g.toBayesianGame P).payoff i a θ = P.payoff i (θ, g.outcome a) :=
  g.toBayesianGame_payoff P i a θ

example (g : OutcomeGame I A X) (P : PayoffStructure I (((i : I) → T i) × X) V)
    (θ : (i : I) → T i) :
    (g.toBayesianGame P).strategicGameAt θ = StrategicGame.ofOutcome g (P.atState θ) :=
  g.toBayesianGame_strategicGameAt P θ

/-- Use the existing mechanism's outcome and entire signed transfer vector. -/
def postedPriceOutcome : OutcomeGame Unit (fun _ ↦ Bool) (Bool × (Unit → ℝ)) where
  outcome a := (postedPriceMechanism.outcome a, fun i ↦ postedPriceMechanism.transfer i a)

/-- Evaluate the existing buyer's value at its true type before adding the received transfer. -/
def postedPricePayoffs : PayoffStructure Unit ((Unit → Bool) × (Bool × (Unit → ℝ))) ℝ where
  payoff i x := postedPriceEnvironment.value i x.1 x.2.1 + x.2.2 i

/-- Shared outcome evaluation recovers the existing Bayesian game exactly. -/
theorem postedPrice_shared_eq_induced :
    postedPriceOutcome.toBayesianGame postedPricePayoffs =
      postedPriceMechanism.inducedBayesianGame postedPriceEnvironment :=
  rfl

/-- Apply the shared fixed-state law to recover the existing strategic utility game. -/
theorem postedPrice_shared_fixedType (θ : Unit → Bool) :
    (postedPriceOutcome.toBayesianGame postedPricePayoffs).strategicGameAt θ =
      postedPriceEnvironment.utilityGame postedPriceMechanism θ :=
  postedPriceOutcome.toBayesianGame_strategicGameAt postedPricePayoffs θ

/-- The existing high-type purchase control is preserved by shared evaluation. -/
theorem postedPrice_shared_payoff_high :
    (postedPriceOutcome.toBayesianGame postedPricePayoffs).payoff
      () (fun _ ↦ true) (fun _ ↦ true) = 1 := by
  simpa only [postedPrice_shared_eq_induced] using postedPrice_induced_payoff_high

/-- Misreporting changes the outcome, while the low true type remains fixed in evaluation. -/
theorem postedPrice_shared_payoff_low_misreport :
    (postedPriceOutcome.toBayesianGame postedPricePayoffs).payoff
      () (fun _ ↦ true) (fun _ ↦ false) = -1 := by
  simpa only [postedPrice_shared_eq_induced] using postedPrice_induced_payoff_low_misreport

/-- Quantities include zero and every real quantity up to capacity one, as in the #176 client. -/
abbrev Quantity := Set.Icc (0 : ℝ) 1

/-- Quantity choices themselves are the consequences evaluated by firms. -/
def cournotOutcome : OutcomeGame (Fin 2) (fun _ ↦ Quantity) (Fin 2 → Quantity) where
  outcome q := q

/-- True types supply unit costs; inverse demand is `2 - q₀ - q₁`. At costs one this is the
canonical deterministic client's profit formula, without a probability or information model. -/
def cournotPayoffs : PayoffStructure (Fin 2) ((Fin 2 → ℝ) × (Fin 2 → Quantity)) ℝ where
  payoff i x := (x.2 i : ℝ) * (2 - (x.2 0 : ℝ) - (x.2 1 : ℝ) - x.1 i)

/-- Fixing costs in the Bayesian adapter recovers direct strategic outcome evaluation. -/
theorem cournot_fixedType (costs : Fin 2 → ℝ) :
    (cournotOutcome.toBayesianGame cournotPayoffs).strategicGameAt costs =
      StrategicGame.ofOutcome cournotOutcome (cournotPayoffs.atState costs) :=
  cournotOutcome.toBayesianGame_strategicGameAt cournotPayoffs costs

/-- The benchmark feasible quantity is one third. -/
def oneThird : Quantity := ⟨1 / 3, by norm_num⟩

/-- The tested deviation increases production to two thirds. -/
def twoThirds : Quantity := ⟨2 / 3, by norm_num⟩

/-- Zero production is a feasible action. -/
def zeroQuantity : Quantity := ⟨0, by norm_num⟩

/-- Each firm earns one ninth at the benchmark profile and unit costs one. -/
theorem cournot_benchmark_payoff (i : Fin 2) :
    (cournotOutcome.toBayesianGame cournotPayoffs).payoff
      i (fun _ ↦ oneThird) (fun _ ↦ 1) = 1 / 9 := by
  norm_num [cournotOutcome, cournotPayoffs, oneThird]

/-- The quantity increase changes the price, leaving the deviator with zero profit. -/
theorem cournot_deviation_payoff :
    (cournotOutcome.toBayesianGame cournotPayoffs).payoff
      0 (Function.update (fun _ ↦ oneThird) 0 twoThirds) (fun _ ↦ 1) = 0 := by
  norm_num [cournotOutcome, cournotPayoffs, oneThird, twoThirds]

/-- Holding the old price fixed would incorrectly assign a strictly positive deviation payoff. -/
theorem cournot_deviation_not_priceTaking :
    (cournotOutcome.toBayesianGame cournotPayoffs).payoff
      0 (Function.update (fun _ ↦ oneThird) 0 twoThirds) (fun _ ↦ 1) <
        (2 / 3 : ℝ) * (2 - 1 / 3 - 1 / 3 - 1) := by
  rw [cournot_deviation_payoff]
  norm_num

/-- Shutdown gives zero profit for every cost state and every opponents' quantity profile. -/
theorem cournot_shutdown_payoff (i : Fin 2) (q : Fin 2 → Quantity) (costs : Fin 2 → ℝ) :
    (cournotOutcome.toBayesianGame cournotPayoffs).payoff
      i (Function.update q i zeroQuantity) costs = 0 := by
  simp [cournotOutcome, cournotPayoffs, zeroQuantity]

end MathEconLibTest.GameTheory.StateOutcomeEvaluation

end
