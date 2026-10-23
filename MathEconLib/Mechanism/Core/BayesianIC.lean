/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Mechanism.Core.Bayesian
public import MathEconLib.GameTheory.Strategic.Bayesian.Measurable.Interim

/-!
# Bayesian incentive compatibility with conditional beliefs

Bayesian incentive compatibility compares truthful reporting with alternative reports while
holding the full true type profile and the bidder's true-type conditional beliefs fixed. The
environment may have interdependent values and the prior may correlate types.

`IsBICOn` is pointwise on declared type/report sets relative to a selected conditional-belief
version. At marginally null types this is additional belief data, not information determined by
the prior. Conditional utilities must be integrable; totalized integrals cannot certify BIC.
On the full type spaces, pointwise BIC implies truthful Bayesian Nash equilibrium when the
realized truthful payoffs are integrable and the game payoffs are jointly measurable.

## References

Matthew O. Jackson (2003), *Mechanism Theory*, §§4.1–4.7.
<https://web.stanford.edu/~jacksonm/mechtheo.pdf>
-/

@[expose] public noncomputable section

open MeasureTheory MathEconLib.GameTheory
open MathEconLib.GameTheory.BayesianPrior

namespace MathEconLib.Mechanism.DirectMechanism

variable {I : Type*} {T : I → Type*} {O : Type*} [DecidableEq I]
  [∀ i, MeasurableSpace (T i)]
  (E : QuasilinearEnvironment I T O) (M : DirectMechanism I T O)
  (μ : Measure (Profile T)) (B : ConditionalBeliefs μ)

/-- The measurable strategy in which each agent reports its own true type. -/
def truthfulStrategy : (M.inducedBayesianGame E).Strategy := fun _ ↦ ⟨id, measurable_id⟩

/-- Conditional expected utility from report `r` at true type `s`, with truthful opponents. -/
def interimUtility (i : I) (s r : T i) : ℝ :=
  (M.inducedBayesianGame E).interimPayoffAction μ B i s r (truthfulStrategy E M)

/-- The report-deviation integrand keeps true types fixed when the report changes. -/
lemma interimUtility_eq_integral (i : I) (s r : T i) :
    interimUtility E M μ B i s r =
      ∫ θo, E.utility M i (insert i s θo) (Function.update (insert i s θo) i r)
        ∂(B.opponents i s) := rfl

/-- Pointwise Bayesian IC on the declared sets of true types and reports, relative to selected
conditional beliefs. Every permitted report has integrable conditional utility. Independence and
private values are not required. -/
structure IsBICOn [IsProbabilityMeasure μ] (D : ∀ i, Set (T i)) : Prop where
  /-- All conditional utility comparisons are between finite expectations. -/
  integrable : ∀ i, ∀ s ∈ D i, ∀ r ∈ D i,
    Integrable (fun θo ↦
      E.utility M i (insert i s θo) (Function.update (insert i s θo) i r))
      (B.opponents i s)
  /-- Truthful reporting weakly maximizes expected utility at the same true-type beliefs. -/
  bic : ∀ i, ∀ s ∈ D i, ∀ r ∈ D i,
    interimUtility E M μ B i s r ≤ interimUtility E M μ B i s s

/-- Pointwise BIC on the full type spaces, relative to the selected conditional-belief version. -/
abbrev IsBIC [IsProbabilityMeasure μ] : Prop := IsBICOn E M μ B (fun _ ↦ Set.univ)

/-- Full-space pointwise BIC implies that truth is a Bayesian Nash equilibrium. This implication
does not identify pointwise beliefs at null types with the weaker a.e. equilibrium condition. -/
theorem IsBIC.isBNE [IsProbabilityMeasure μ] (h : IsBIC E M μ B)
    (hmeas : ∀ i, Measurable (fun p : Profile T × Profile T ↦
      (M.inducedBayesianGame E).payoff i p.1 p.2))
    (hint : (M.inducedBayesianGame E).IncumbentPayoffsIntegrable μ (truthfulStrategy E M)) :
    (M.inducedBayesianGame E).IsBNE μ (truthfulStrategy E M) := by
  apply BayesianGame.isBNE_of_ae_interim _ μ B hmeas _ hint
  intro i
  exact Filter.Eventually.of_forall fun s r ↦ h.bic i s (Set.mem_univ _) r (Set.mem_univ _)

end MathEconLib.Mechanism.DirectMechanism
