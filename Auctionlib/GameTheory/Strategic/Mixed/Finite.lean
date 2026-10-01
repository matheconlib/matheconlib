/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Auctionlib.GameTheory.Strategic.Mixed
public import Auctionlib.Probability.FinDist.Expect
public import Auctionlib.Probability.FinDist.Simplex

/-!
# Finite independent mixed strategies

On finite action spaces, each player's mixed action is a finite probability distribution, or
equivalently a point of the standard simplex. Independent action laws give finite expected payoffs
in a real module. With complete normed real vector payoffs and discrete measurable actions, these
expectations agree with integration against independent probability measures.

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

open MeasureTheory Auctionlib.Probability

namespace Auctionlib.GameTheory.StrategicGame

variable {I : Type*} {A : I → Type*} {V : Type*}

/-- Finite discrete action spaces give every player's payoff a finite expectation under each
independent mixed strategy profile. -/
lemma integrable_payoff [Fintype I] [∀ i, Finite (A i)] [∀ i, MeasurableSpace (A i)]
    [∀ i, DiscreteMeasurableSpace (A i)] [NormedAddCommGroup V]
    (G : StrategicGame I A V) (i : I) (σ : MixedStrategy A) :
    Integrable (G.payoff i) (Measure.pi (fun j ↦ (σ j : Measure (A j)))) :=
  .of_finite

variable [∀ i, Fintype (A i)]

/-- Each player chooses nonnegative weights summing to one on their finite action space. -/
abbrev FiniteMixedStrategy (A : I → Type*) [∀ i, Fintype (A i)] := ∀ i, FinDist (A i)

section Payoff

variable [Fintype I] [DecidableEq I]

/-- Expected payoff under independent finite action weights. -/
def finiteExpectedPayoff [AddCommMonoid V] [Module ℝ V] (G : StrategicGame I A V) (i : I)
    (σ : FiniteMixedStrategy A) : V := by
  classical
  exact FinDist.expect (FinDist.productD σ) (G.payoff i)

/-- Finite independent expected payoff is the sum of payoffs weighted by the product of each
player's action probabilities. -/
lemma finiteExpectedPayoff_eq_sum [AddCommMonoid V] [Module ℝ V]
    (G : StrategicGame I A V) (i : I) (σ : FiniteMixedStrategy A) :
    G.finiteExpectedPayoff i σ = ∑ a : ∀ j, A j, (∏ j, σ j (a j)) • G.payoff i a := by
  classical
  rfl

/-- A finite game's strategic extension to simplex-valued actions. -/
def finiteMixedExtension [AddCommMonoid V] [Module ℝ V] (G : StrategicGame I A V) :
    StrategicGame I (fun i ↦ FinDist (A i)) V where
  payoff := G.finiteExpectedPayoff

/-- Every unilateral change of probability weights has payoff at most the incumbent payoff. -/
def IsFiniteMixedNash [AddCommMonoid V] [Module ℝ V] [LE V] (G : StrategicGame I A V)
    (σ : FiniteMixedStrategy A) : Prop :=
  G.finiteMixedExtension.IsNash σ

/-- Mixed Nash compares every unilateral change of simplex weights with the incumbent payoff. -/
@[simp] lemma isFiniteMixedNash_iff [AddCommMonoid V] [Module ℝ V] [LE V]
    (G : StrategicGame I A V) (σ : FiniteMixedStrategy A) :
    G.IsFiniteMixedNash σ ↔ ∀ i τ, G.finiteExpectedPayoff i (Function.update σ i τ) ≤
      G.finiteExpectedPayoff i σ := isNash_iff _ _

end Payoff

section Measurable

variable [∀ i, MeasurableSpace (A i)] [∀ i, DiscreteMeasurableSpace (A i)]

/-- The simplex profile corresponding to a profile of probability measures. -/
def toSimplex (σ : MixedStrategy A) : FiniteMixedStrategy A :=
  fun i ↦ ProbabilityMeasure.equivStdSimplex (σ i)

/-- The independent action laws represented by a profile of simplex weights. -/
def toProbability (σ : FiniteMixedStrategy A) : MixedStrategy A :=
  fun i ↦ ProbabilityMeasure.equivStdSimplex.symm (σ i)

/-- Converting simplex weights to probability measures and back preserves the profile. -/
@[simp] lemma toSimplex_toProbability (σ : FiniteMixedStrategy A) :
    toSimplex (toProbability σ) = σ := by
  funext i
  exact Equiv.apply_symm_apply _ _

/-- Converting probability measures to simplex weights and back preserves the profile. -/
@[simp] lemma toProbability_toSimplex (σ : MixedStrategy A) :
    toProbability (toSimplex σ) = σ := by
  funext i
  exact Equiv.symm_apply_apply _ _

variable [DecidableEq I]

/-- Converting to simplex weights commutes with replacing one player's mixed action. -/
@[simp] lemma toSimplex_update (σ : MixedStrategy A) (i : I)
    (τ : ProbabilityMeasure (A i)) :
    toSimplex (Function.update σ i τ) =
      Function.update (toSimplex σ) i (ProbabilityMeasure.equivStdSimplex τ) := by
  ext j
  by_cases h : j = i
  · subst j
    simp [toSimplex]
  · simp [toSimplex, Function.update_of_ne h]

/-- Converting to probability measures commutes with replacing one player's mixed action. -/
@[simp] lemma toProbability_update (σ : FiniteMixedStrategy A) (i : I) (τ : FinDist (A i)) :
    toProbability (Function.update σ i τ) =
      Function.update (toProbability σ) i (ProbabilityMeasure.equivStdSimplex.symm τ) := by
  ext j
  by_cases h : j = i
  · subst j
    simp [toProbability]
  · simp [toProbability, Function.update_of_ne h]

variable [Fintype I] [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Finite expected utility is a sum of payoffs weighted by the product of action probabilities. -/
lemma mixedExtension_payoff_eq_finiteExpectedPayoff (G : StrategicGame I A V) (i : I)
    (σ : MixedStrategy A) :
    G.mixedExtension.payoff i σ = G.finiteExpectedPayoff i (toSimplex σ) := by
  classical
  change (∫ a, G.payoff i a ∂Measure.pi (fun j ↦ (σ j : Measure (A j)))) = _
  rw [integral_fintype _ (G.integrable_payoff i σ)]
  rw [finiteExpectedPayoff_eq_sum]
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
lemma finiteMixedExtension_payoff_eq_mixedExtension (G : StrategicGame I A V) (i : I)
    (σ : FiniteMixedStrategy A) :
    G.finiteMixedExtension.payoff i σ = G.mixedExtension.payoff i (toProbability σ) := by
  rw [mixedExtension_payoff_eq_finiteExpectedPayoff, toSimplex_toProbability]
  rfl

/-- A simplex profile is a mixed Nash equilibrium exactly when its probability-measure profile has
integrable payoffs and withstands every integrable unilateral deviation. -/
theorem isFiniteMixedNash_iff_isMixedNash [LE V] (G : StrategicGame I A V)
    (σ : FiniteMixedStrategy A) :
    G.IsFiniteMixedNash σ ↔ G.IsMixedNash (toProbability σ) := by
  rw [G.isMixedNash_iff_isNash_of_integrable (toProbability σ)
    (fun i τ ↦ G.integrable_payoff i (Function.update (toProbability σ) i τ))]
  exact isNash_iff_of_actionEquiv G.finiteMixedExtension G.mixedExtension
    (fun _ ↦ ProbabilityMeasure.equivStdSimplex.symm)
    (finiteMixedExtension_payoff_eq_mixedExtension G) σ

variable {O : Type*} [MeasurableSpace O] [MeasurableSpace V] [BorelSpace V]

/-- Finite simplex expected utility agrees with the induced distribution over arbitrary outcomes. -/
lemma finiteExpectedPayoff_eq_ofOutcome_mixed_payoff (H : OutcomeGame I A O)
    (P : PayoffStructure I O V) [H.Measurable] [P.Measurable] (i : I) (σ : FiniteMixedStrategy A) :
    (ofOutcome H P).finiteExpectedPayoff i σ =
      (ofOutcome H.mixed P.expected).payoff i (toProbability σ) := by
  change (ofOutcome H P).finiteMixedExtension.payoff i σ = _
  rw [finiteMixedExtension_payoff_eq_mixedExtension]
  change (∫ a, P.payoff i (H.outcome a) ∂Measure.pi (fun j ↦
    (toProbability σ j : Measure (A j)))) =
    ∫ o, P.payoff i o ∂((ProbabilityMeasure.pi (toProbability σ)).map
      H.measurable_outcome.aemeasurable : ProbabilityMeasure O)
  rw [ProbabilityMeasure.toMeasure_map]
  have hmeas : AEStronglyMeasurable (P.payoff i)
      (Measure.map H.outcome (ProbabilityMeasure.pi (toProbability σ))) := by
    refine aestronglyMeasurable_iff_aemeasurable_separable.mpr
      ⟨(P.measurable_payoff i).aemeasurable,
        Set.range (fun a ↦ P.payoff i (H.outcome a)), (Set.finite_range _).isSeparable, ?_⟩
    exact (ae_map_iff H.measurable_outcome.aemeasurable
      ((Set.finite_range _).measurableSet.preimage (P.measurable_payoff i))).mpr
      (Filter.Eventually.of_forall fun a ↦ Set.mem_range_self a)
  rw [integral_map H.measurable_outcome.aemeasurable hmeas]
  rfl

/-- Mixed Nash equilibrium agrees between the simplex and outcome-distribution representations. -/
theorem isFiniteMixedNash_iff_ofOutcome_mixed_isNash [LE V] (H : OutcomeGame I A O)
    (P : PayoffStructure I O V) [H.Measurable] [P.Measurable] (σ : FiniteMixedStrategy A) :
    (ofOutcome H P).IsFiniteMixedNash σ ↔
      (ofOutcome H.mixed P.expected).IsNash (toProbability σ) := by
  exact isNash_iff_of_actionEquiv (ofOutcome H P).finiteMixedExtension
    (ofOutcome H.mixed P.expected) (fun _ ↦ ProbabilityMeasure.equivStdSimplex.symm)
    (finiteExpectedPayoff_eq_ofOutcome_mixed_payoff H P) σ

end Measurable

end Auctionlib.GameTheory.StrategicGame
