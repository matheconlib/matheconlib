/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib
public import MathEconLibTest.GameTheory.MeasurableBayesian
public import MathEconLibTest.GameTheory.Integrability

/-!
# Guarded pointwise interim contracts

The bounded Gaussian model applies the named conditional comparison and BNE adapter through the
public library import. The independent contract pins spell out all action guards and the common
conull-set order. The existing reciprocal-own-type model separately shows that pointwise
conditional finiteness does not supply the global incumbent guard.
-/

@[expose] public noncomputable section

open MeasureTheory MathEconLib.GameTheory
open MathEconLib.GameTheory.BayesianPrior

namespace MathEconLibTest.GameTheory.ContinuousBayesianExample

/-- Every Gaussian-model conditional action payoff is a finite constant in opponents' types. -/
lemma action_integrable (i : Unit) (t a : ℝ) :
    Integrable (game.interimPayoffActionIntegrand i t a truthful) (beliefs.opponents i t) := by
  change Integrable (fun _ ↦ -min 1 ((a - t) ^ 2)) (beliefs.opponents i t)
  exact integrable_const _

/-- The named comparison result certifies truthful play against every real action at every type. -/
theorem truthful_pointwise : game.IsPointwiseInterimBestResponse prior beliefs truthful :=
  ⟨action_integrable, fun i t a ↦
    game.interimPayoffAction_le_of_ae_payoff_le prior beliefs i t a truthful
      (action_integrable i t a) (action_integrable i t ((truthful i).1 t))
      (Filter.Eventually.of_forall fun _ ↦ by
        simpa [BayesianGame.interimPayoffActionIntegrand, game, truthful] using
          (neg_nonpos.mpr (le_min zero_le_one (sq_nonneg (a - t)))))⟩

/-- The guarded pointwise adapter gives the actual measurable-strategy BNE conclusion. -/
theorem truthful_isBNE_of_pointwise : game.IsBNE prior truthful :=
  truthful_pointwise.isBNE game prior beliefs measurable_payoff truthful_integrable

end MathEconLibTest.GameTheory.ContinuousBayesianExample

namespace MathEconLibTest.PointwiseInterimContract

variable {I : Type*} {Θ A : I → Type*} [DecidableEq I]
  [∀ i, MeasurableSpace (Θ i)] [∀ i, MeasurableSpace (A i)]
  (G : BayesianGame I Θ A ℝ) (μ : Measure (∀ i, Θ i)) [IsProbabilityMeasure μ]
  (B : ConditionalBeliefs μ) (s : G.Strategy)

-- Guarded meaning is independently expanded, rather than compared to another alias.
example : G.IsPointwiseInterimBestResponse μ B s ↔
    (∀ i t a, Integrable
      (fun θo ↦ G.payoff i
        (Function.update (G.measurableActionProfile s (insert i t θo)) i a) (insert i t θo))
      (B.opponents i t)) ∧
    (∀ i t a,
      (∫ θo, G.payoff i
        (Function.update (G.measurableActionProfile s (insert i t θo)) i a) (insert i t θo)
        ∂(B.opponents i t)) ≤
      ∫ θo, G.payoff i (G.measurableActionProfile s (insert i t θo)) (insert i t θo)
        ∂(B.opponents i t)) := by
  rw [G.isPointwiseInterimBestResponse_iff μ B s]
  simp only [BayesianGame.interimPayoff_eq_integral, BayesianGame.interimPayoffAction]
  rfl

-- One common conull set protects every action, including the prescribed action.
example (h : G.IsPointwiseInterimBestResponse μ B s) :
    ∀ i, ∀ᵐ t ∂(marginalType μ i), ∀ a,
      Integrable (G.interimPayoffActionIntegrand i t a s) (B.opponents i t) :=
  h.hasIntegrableInterimDeviations G μ B

-- Simultaneous a.e. optimality is a consequence, not pointwise recovery from BNE.
example (h : G.IsPointwiseInterimBestResponse μ B s) :
    ∀ i, ∀ᵐ t ∂(marginalType μ i), ∀ a,
      G.interimPayoffAction μ B i t a s ≤ G.interimPayoff μ B i t s :=
  h.isAEInterimBestResponse G μ B

-- Each side of the local comparison has its own integrability hypothesis.
example (i : I) (t : Θ i) (a : A i)
    (ha : Integrable (G.interimPayoffActionIntegrand i t a s) (B.opponents i t))
    (hs : Integrable (G.interimPayoffActionIntegrand i t ((s i).1 t) s) (B.opponents i t))
    (hle : G.interimPayoffActionIntegrand i t a s ≤ᵐ[B.opponents i t]
      G.interimPayoffActionIntegrand i t ((s i).1 t) s) :
    G.interimPayoffAction μ B i t a s ≤ G.interimPayoff μ B i t s :=
  G.interimPayoffAction_le_of_ae_payoff_le μ B i t a s ha hs hle

-- The global incumbent guard remains independent of every conditional action guard.
example (h : G.IsPointwiseInterimBestResponse μ B s)
    (hmeas : ∀ i, Measurable (fun p : (∀ j, A j) × (∀ j, Θ j) ↦ G.payoff i p.1 p.2))
    (hinc : G.IncumbentPayoffsIntegrable μ s) : G.IsBNE μ s :=
  h.isBNE G μ B hmeas hinc

end MathEconLibTest.PointwiseInterimContract

namespace MathEconLibTest.PointwiseInterimGlobalGuard

open MathEconLibTest.GameTheory.Integrability

/-- Selected beliefs for the existing one-player reciprocal-own-type model. -/
def beliefs : ConditionalBeliefs prior := canonicalBeliefs prior

/-- Each fixed type has constant conditional utility, even though global utility is
nonintegrable. -/
theorem pointwise : game.IsPointwiseInterimBestResponse prior beliefs strategy :=
  ⟨fun i t _ ↦ by
    change Integrable (fun _ ↦ t⁻¹) (beliefs.opponents i t)
    exact integrable_const _,
    fun _ _ _ ↦ le_rfl⟩

/-- Pointwise finite comparisons do not discharge the adapter's global incumbent guard. -/
theorem pointwise_without_global_integrability :
    game.IsPointwiseInterimBestResponse prior beliefs strategy ∧
      ¬ game.IncumbentPayoffsIntegrable prior strategy ∧ ¬ game.IsBNE prior strategy :=
  ⟨pointwise, fun h ↦ not_integrable_payoff (h ()), not_isBNE⟩

end MathEconLibTest.PointwiseInterimGlobalGuard

end
