/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Mechanism.Core.BayesianIC
public import MathEconLib.Mechanism.Core.BayesianUtility

/-!
# Exact quasilinear recovery from supplied utility

The general constructors recover the existing quasilinear strategic and Bayesian games exactly.
The existing truthful measurable strategy and conditional interim evaluator are retained and
agree with the supplied-utility route under the same prior and selected conditional beliefs.
-/

@[expose] public noncomputable section

open MeasureTheory MathEconLib.GameTheory MathEconLib.GameTheory.BayesianPrior

namespace MathEconLib.Mechanism

universe uI uT uA uO

variable {I : Type uI} {T : I → Type uT} {A : I → Type uA} {O : Type uO}

/-- Quasilinear utility on physical outcomes and signed transfer vectors. -/
def QuasilinearEnvironment.consequenceUtility (E : QuasilinearEnvironment I T O) :
    I → Profile T → (O × (I → ℝ)) → ℝ :=
  fun i θ c ↦ E.value i θ c.1 + c.2 i

/-- Consequence utility adds the agent's received transfer to its true-state valuation. -/
@[simp] theorem QuasilinearEnvironment.consequenceUtility_apply
    (E : QuasilinearEnvironment I T O) (i : I) (θ : Profile T) (c : O × (I → ℝ)) :
    E.consequenceUtility i θ c = E.value i θ c.1 + c.2 i :=
  rfl

/-- Supplying quasilinear utility recovers the existing fixed-type utility game exactly. -/
@[simp] theorem toStrategicGame_quasilinear (M : Mechanism I A O)
    (E : QuasilinearEnvironment I T O) (θ : Profile T) :
    M.toStrategicGame E.consequenceUtility θ = E.utilityGame M θ :=
  rfl

/-- Supplying quasilinear utility recovers the existing induced Bayesian game exactly. -/
@[simp] theorem toBayesianGame_quasilinear (M : Mechanism I A O)
    (E : QuasilinearEnvironment I T O) :
    M.toBayesianGame E.consequenceUtility = M.inducedBayesianGame E :=
  rfl

namespace DirectMechanism.Quasilinear

variable [∀ i, MeasurableSpace (T i)]
  (E : QuasilinearEnvironment I T O) (M : DirectMechanism I T O)

/-- The retained truthful strategy is the same measurable identity in the general game view. -/
theorem truthfulStrategy_eq_toBayesianGame :
    truthfulStrategy E M =
      (fun _ ↦ ⟨id, measurable_id⟩ : (M.toBayesianGame E.consequenceUtility).Strategy) :=
  rfl

variable [DecidableEq I]

/-- The retained interim evaluator agrees with the general game's chosen-action evaluator. -/
theorem interimUtility_eq_toBayesianGame_interimPayoffAction
    (μ : Measure (Profile T)) (B : ConditionalBeliefs μ) (i : I) (s r : T i) :
    interimUtility E M μ B i s r =
      (M.toBayesianGame E.consequenceUtility).interimPayoffAction μ B i s r
        (truthfulStrategy E M) :=
  rfl

end DirectMechanism.Quasilinear

end MathEconLib.Mechanism

end
