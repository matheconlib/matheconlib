/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Mechanism

/-!
# Public mechanism utility contracts

The mechanism umbrella exposes the general constructors with independent player, state, action,
outcome, and value universes. Exact quasilinear recovery retains the old games and evaluators.
Action translation needs no injectivity or surjectivity for these evaluation equalities.
-/

@[expose] public noncomputable section

open MeasureTheory MathEconLib.GameTheory MathEconLib.Mechanism
open MathEconLib.GameTheory.BayesianPrior

namespace MathEconLibTest.Mechanism.Utility

universe uI uT uA uB uO uS uV

variable {I : Type uI} {T : I → Type uT} {A : I → Type uA} {B : I → Type uB}
  {O : Type uO} {S : Type uS} {V : Type uV}

example (M : MathEconLib.Mechanism I A O) (a : Profile A) :
    M.toOutcomeGame.outcome a = (M.outcome a, fun i ↦ M.transfer i a) :=
  M.toOutcomeGame_outcome a

example (u : I → S → O → ℝ → V) (i : I) (s : S) (c : O × (I → ℝ)) :
    utilityFromOwnTransfer u i s c = u i s c.1 (c.2 i) :=
  utilityFromOwnTransfer_apply u i s c

example (M : MathEconLib.Mechanism I A O) (u : I → S → (O × (I → ℝ)) → V)
    (s : S) (i : I) (a : Profile A) :
    (M.toStrategicGame u s).payoff i a = u i s (M.outcome a, fun j ↦ M.transfer j a) :=
  M.toStrategicGame_payoff u s i a

example (M : MathEconLib.Mechanism I A O) (u : I → Profile T → (O × (I → ℝ)) → V)
    (i : I) (a : Profile A) (θ : Profile T) :
    (M.toBayesianGame u).payoff i a θ = u i θ (M.outcome a, fun j ↦ M.transfer j a) :=
  M.toBayesianGame_payoff u i a θ

example (M : MathEconLib.Mechanism I A O) (u : I → Profile T → (O × (I → ℝ)) → V)
    (θ : Profile T) :
    (M.toBayesianGame u).strategicGameAt θ = M.toStrategicGame u θ :=
  M.toBayesianGame_strategicGameAt u θ

example (M : MathEconLib.Mechanism I A O) (κ : (i : I) → B i → A i)
    (u : I → S → (O × (I → ℝ)) → V) (s : S) :
    (M.comap κ).toStrategicGame u s = (M.toStrategicGame u s).comapActions κ :=
  M.toStrategicGame_comap κ u s

example (M : MathEconLib.Mechanism I A O) (κ : (i : I) → B i → A i)
    (u : I → Profile T → (O × (I → ℝ)) → V) :
    (M.comap κ).toBayesianGame u = (M.toBayesianGame u).comapActions κ :=
  M.toBayesianGame_comap κ u

example (M : MathEconLib.Mechanism I A O) (κ : (i : I) → B i → A i)
    (u : I → Profile T → (O × (I → ℝ)) → V) (θ : Profile T) :
    ((M.comap κ).toBayesianGame u).strategicGameAt θ =
      (M.toStrategicGame u θ).comapActions κ :=
  ((M.comap κ).toBayesianGame_strategicGameAt u θ).trans (M.toStrategicGame_comap κ u θ)

example (M : MathEconLib.Mechanism I A O) (E : QuasilinearEnvironment I T O)
    (θ : Profile T) :
    M.toStrategicGame E.consequenceUtility θ = E.utilityGame M θ :=
  M.toStrategicGame_quasilinear E θ

example (M : MathEconLib.Mechanism I A O) (E : QuasilinearEnvironment I T O) :
    M.toBayesianGame E.consequenceUtility = M.inducedBayesianGame E :=
  M.toBayesianGame_quasilinear E

section Measurable

variable [∀ i, MeasurableSpace (T i)]

example (E : QuasilinearEnvironment I T O) (M : DirectMechanism I T O) :
    DirectMechanism.Quasilinear.truthfulStrategy E M =
      (fun _ ↦ ⟨id, measurable_id⟩ : (M.toBayesianGame E.consequenceUtility).Strategy) :=
  DirectMechanism.Quasilinear.truthfulStrategy_eq_toBayesianGame E M

example [DecidableEq I] (E : QuasilinearEnvironment I T O) (M : DirectMechanism I T O)
    (μ : Measure (Profile T)) (B : ConditionalBeliefs μ) (i : I) (s r : T i) :
    DirectMechanism.Quasilinear.interimUtility E M μ B i s r =
      (M.toBayesianGame E.consequenceUtility).interimPayoffAction μ B i s r
        (DirectMechanism.Quasilinear.truthfulStrategy E M) :=
  DirectMechanism.Quasilinear.interimUtility_eq_toBayesianGame_interimPayoffAction E M μ B i s r

end Measurable

end MathEconLibTest.Mechanism.Utility

end
