/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Mechanism

/-!
# Conditional quasilinear BIC contract

This pin fixes the mathematical content of the named characterization through the public
mechanism umbrella. An alias between two names for the same predicate cannot detect changes to
that predicate. This contract separately spells out finite conditional utilities, the deviation
direction, the true profile, and the true-type belief argument on both sides.
-/

@[expose] public noncomputable section

open MeasureTheory MathEconLib.Mechanism MathEconLib.GameTheory.BayesianPrior

namespace MathEconLibTest.BayesianICContract

variable {I : Type*} {T : I → Type*} {O : Type*} [DecidableEq I]
  [∀ i, MeasurableSpace (T i)]

example (E : QuasilinearEnvironment I T O) (M : DirectMechanism I T O)
    (μ : Measure (Profile T)) [IsProbabilityMeasure μ] (B : ConditionalBeliefs μ)
    (D : ∀ i, Set (T i)) :
    DirectMechanism.Quasilinear.IsBICOn E M μ B D ↔
      (∀ i, ∀ s ∈ D i, ∀ r ∈ D i,
        Integrable (fun θo ↦
          E.utility M i (insert i s θo) (Function.update (insert i s θo) i r))
          (B.opponents i s)) ∧
      (∀ i, ∀ s ∈ D i, ∀ r ∈ D i,
        (∫ θo, E.utility M i (insert i s θo) (Function.update (insert i s θo) i r)
          ∂(B.opponents i s)) ≤
        ∫ θo, E.utility M i (insert i s θo) (Function.update (insert i s θo) i s)
          ∂(B.opponents i s)) :=
  DirectMechanism.Quasilinear.isBICOn_iff E M μ B D

end MathEconLibTest.BayesianICContract
