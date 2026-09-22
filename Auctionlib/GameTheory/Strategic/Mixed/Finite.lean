/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Auctionlib.GameTheory.Strategic.Mixed

/-!
# Finite independent mixed strategies

On finite action spaces, each player's mixed action is a finite probability distribution, or
equivalently a point of the standard simplex. Independent action laws give finite expected payoffs
as finite sums. With discrete measurable actions, these expectations agree with integration against
independent probability measures.

## Main definitions

* `StrategicGame.FiniteMixedStrategy` gives profiles of finite action distributions.
* `StrategicGame.finiteExpectedPayoff` averages payoffs under the independent product law.
* `StrategicGame.finiteMixedExtension` is the strategic game on finite distributions.
* `StrategicGame.IsFiniteMixedNash` is Nash equilibrium in the finite mixed extension.

## Main statements

* `StrategicGame.finiteExpectedPayoff_eq_sum` gives the finite independent expected-payoff formula.
* `StrategicGame.isFiniteMixedNash_iff_isMixedNash` identifies finite and measure equilibria.
* `StrategicGame.isFiniteMixedNash_iff_ofOutcome_mixed_isNash` identifies finite equilibria with
  equilibria for expected utilities over induced outcome distributions.

## Tags

mixed strategies, expected payoffs, nash equilibrium, finite games, probability simplex
-/

@[expose] public noncomputable section

open MeasureTheory

namespace Auctionlib.GameTheory.StrategicGame

variable {I : Type*} {A : I → Type*}

section Finite

variable [Fintype I] [DecidableEq I] [∀ i, Fintype (A i)]

/-- Each player chooses nonnegative weights summing to one on their finite action space. -/
abbrev FiniteMixedStrategy (A : I → Type*) [∀ i, Fintype (A i)] := ∀ i, stdSimplex ℝ (A i)

/-- Expected payoff under independent finite action weights. -/
def finiteExpectedPayoff (G : StrategicGame I A) (i : I) (σ : FiniteMixedStrategy A) : ℝ :=
  ∑ a : ∀ j, A j, (∏ j, σ j (a j)) * G.payoff i a

/-- Finite independent expected payoff is the sum of payoffs weighted by the product of each
player's action probabilities. -/
lemma finiteExpectedPayoff_eq_sum (G : StrategicGame I A) (i : I) (σ : FiniteMixedStrategy A) :
    G.finiteExpectedPayoff i σ = ∑ a : ∀ j, A j, (∏ j, σ j (a j)) * G.payoff i a := rfl

/-- A finite game's strategic extension to simplex-valued actions. -/
def finiteMixedExtension (G : StrategicGame I A) :
    StrategicGame I (fun i ↦ stdSimplex ℝ (A i)) where
  payoff := G.finiteExpectedPayoff

/-- A mixed Nash equilibrium admits no profitable change of a player's probability weights. -/
def IsFiniteMixedNash (G : StrategicGame I A) (σ : FiniteMixedStrategy A) : Prop :=
  G.finiteMixedExtension.IsNash σ

/-- A mixed Nash equilibrium rules out profitable unilateral changes in simplex weights. -/
@[simp] lemma isFiniteMixedNash_iff (G : StrategicGame I A) (σ : FiniteMixedStrategy A) :
    G.IsFiniteMixedNash σ ↔ ∀ i τ, G.finiteExpectedPayoff i (Function.update σ i τ) ≤
      G.finiteExpectedPayoff i σ := isNash_iff _ _

variable [∀ i, MeasurableSpace (A i)] [∀ i, DiscreteMeasurableSpace (A i)]

/-- The simplex profile corresponding to a profile of probability measures. -/
def toSimplex (σ : ∀ i, ProbabilityMeasure (A i)) : FiniteMixedStrategy A :=
  fun i ↦ ProbabilityMeasure.equivStdSimplex (σ i)

/-- The independent action laws represented by a profile of simplex weights. -/
def toProbability (σ : FiniteMixedStrategy A) : ∀ i, ProbabilityMeasure (A i) :=
  fun i ↦ ProbabilityMeasure.equivStdSimplex.symm (σ i)

omit [Fintype I] [DecidableEq I] in
/-- Converting simplex weights to probability measures and back preserves the profile. -/
@[simp] lemma toSimplex_toProbability (σ : FiniteMixedStrategy A) :
    toSimplex (toProbability σ) = σ := by
  funext i
  exact Equiv.apply_symm_apply _ _

omit [Fintype I] [DecidableEq I] in
/-- Converting probability measures to simplex weights and back preserves the profile. -/
@[simp] lemma toProbability_toSimplex (σ : ∀ i, ProbabilityMeasure (A i)) :
    toProbability (toSimplex σ) = σ := by
  funext i
  exact Equiv.symm_apply_apply _ _

omit [Fintype I] in
/-- Converting to simplex weights commutes with replacing one player's mixed action. -/
@[simp] lemma toSimplex_update (σ : ∀ i, ProbabilityMeasure (A i)) (i : I)
    (τ : ProbabilityMeasure (A i)) :
    toSimplex (Function.update σ i τ) =
      Function.update (toSimplex σ) i (ProbabilityMeasure.equivStdSimplex τ) := by
  ext j
  by_cases h : j = i
  · subst j
    simp [toSimplex]
  · simp [toSimplex, Function.update_of_ne h]

omit [Fintype I] in
/-- Converting to probability measures commutes with replacing one player's mixed action. -/
@[simp] lemma toProbability_update (σ : FiniteMixedStrategy A) (i : I)
    (τ : stdSimplex ℝ (A i)) :
    toProbability (Function.update σ i τ) =
      Function.update (toProbability σ) i (ProbabilityMeasure.equivStdSimplex.symm τ) := by
  ext j
  by_cases h : j = i
  · subst j
    simp [toProbability]
  · simp [toProbability, Function.update_of_ne h]

/-- Finite expected utility is a sum of payoffs weighted by the product of action probabilities. -/
lemma mixedExtension_payoff_eq_finiteExpectedPayoff (G : StrategicGame I A) (i : I)
    (σ : ∀ i, ProbabilityMeasure (A i)) :
    G.mixedExtension.payoff i σ = G.finiteExpectedPayoff i (toSimplex σ) := by
  classical
  change (∫ a, G.payoff i a ∂Measure.pi (fun j ↦ (σ j : Measure (A j)))) = _
  rw [integral_fintype _ (by
    obtain ⟨C, hC⟩ := (Set.finite_range (G.payoff i)).isBounded.exists_norm_le
    exact Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun a ↦ hC _ ⟨a, rfl⟩))]
  unfold finiteExpectedPayoff
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  change (Measure.pi (fun j ↦ (σ j : Measure (A j)))).real {a} =
    ∏ j, (ProbabilityMeasure.equivStdSimplex (σ j)) (a j)
  simp only [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro j _
  exact (σ j).measureReal_eq_coe_coeFn {a j}

/-- The probability-measure and simplex extensions assign equal payoffs to corresponding
profiles. -/
lemma finiteMixedExtension_payoff_eq_mixedExtension (G : StrategicGame I A) (i : I)
    (σ : FiniteMixedStrategy A) :
    G.finiteMixedExtension.payoff i σ = G.mixedExtension.payoff i (toProbability σ) := by
  rw [mixedExtension_payoff_eq_finiteExpectedPayoff, toSimplex_toProbability]
  rfl

/-- A simplex profile is a mixed Nash equilibrium exactly when its probability-measure profile is a
Nash equilibrium in the mixed extension. -/
theorem isFiniteMixedNash_iff_isMixedNash (G : StrategicGame I A) (σ : FiniteMixedStrategy A) :
    G.IsFiniteMixedNash σ ↔ G.IsMixedNash (toProbability σ) := by
  exact isNash_iff_of_actionEquiv G.finiteMixedExtension G.mixedExtension
    (fun _ ↦ ProbabilityMeasure.equivStdSimplex.symm)
    (finiteMixedExtension_payoff_eq_mixedExtension G) σ

variable {O : Type*} [MeasurableSpace O]

/-- Finite simplex expected utility agrees with the induced distribution over arbitrary outcomes. -/
lemma finiteExpectedPayoff_eq_ofOutcome_mixed_payoff (H : OutcomeGame I A O)
    (P : PayoffStructure I O)
    [H.Measurable] [P.Measurable] (i : I) (σ : FiniteMixedStrategy A) :
    (ofOutcome H P).finiteExpectedPayoff i σ =
      (ofOutcome H.mixed P.expected).payoff i (toProbability σ) := by
  change (ofOutcome H P).finiteMixedExtension.payoff i σ = _
  rw [finiteMixedExtension_payoff_eq_mixedExtension]
  change (∫ a, P.payoff i (H.outcome a) ∂Measure.pi (fun j ↦
    (toProbability σ j : Measure (A j)))) =
    ∫ o, P.payoff i o ∂((ProbabilityMeasure.pi (toProbability σ)).map
      H.measurable_outcome.aemeasurable : ProbabilityMeasure O)
  rw [ProbabilityMeasure.toMeasure_map, integral_map H.measurable_outcome.aemeasurable
    (P.measurable_payoff i).aestronglyMeasurable]
  rfl

/-- Mixed Nash equilibrium agrees between the simplex and outcome-distribution representations. -/
theorem isFiniteMixedNash_iff_ofOutcome_mixed_isNash (H : OutcomeGame I A O)
    (P : PayoffStructure I O) [H.Measurable] [P.Measurable] (σ : FiniteMixedStrategy A) :
    (ofOutcome H P).IsFiniteMixedNash σ ↔
      (ofOutcome H.mixed P.expected).IsNash (toProbability σ) := by
  exact isNash_iff_of_actionEquiv (ofOutcome H P).finiteMixedExtension
    (ofOutcome H.mixed P.expected) (fun _ ↦ ProbabilityMeasure.equivStdSimplex.symm)
    (finiteExpectedPayoff_eq_ofOutcome_mixed_payoff H P) σ

end Finite

end Auctionlib.GameTheory.StrategicGame
