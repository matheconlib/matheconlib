/-
Copyright (c) 2026 Ben Eltschig, Daniel Lyng. All rights reserved.
Released under license as described in the file LICENSE.
Authors: Ben Eltschig, Daniel Lyng
-/
module

public import Auctionlib.ForMathlib.ProbabilityMeasure
public import Auctionlib.GameTheory.Strategic.Basic

/-!
# Outcomes and expected payoffs

An outcome game assigns an outcome to each action profile, and a payoff structure assigns utility
to outcomes in a value type. Independent randomized actions induce a probability distribution over
outcomes. For utilities in a complete real normed space, expected utility defines payoffs on
outcome distributions, and boundedness of utilities implies boundedness of expected utilities. The
measurability and continuity results here apply to real-valued utilities. Stochastic outcomes can
be flattened by integration.

## Main definitions

* `OutcomeGame`: Outcomes determined by action profiles.
* `PayoffStructure`: Players' utilities over outcomes.
* `StrategicGame.ofOutcome`: Strategic payoffs obtained by evaluating outcomes.
* `OutcomeGame.mixed`: Outcome distributions induced by independent mixed actions.
* `OutcomeGame.mixedFlattened`: Mixed actions with stochastic outcomes.
* `PayoffStructure.expected`: Expected utilities over outcome distributions.

## Main statements

* Independent mixing preserves measurability and, under the stated topological hypotheses,
  continuity of outcomes.
* Expected utility is bounded in a complete real normed value space when utilities are bounded.
* For real-valued utilities, expected utility is measurable for bounded measurable utilities and
  continuous on a compact outcome space when utilities are continuous and open sets are measurable.

## Tags

outcomes, expected utility, mixed strategies
-/

@[expose] public section

namespace Auctionlib.GameTheory

/-- An outcome game assigns an outcome to every profile of player actions. -/
structure OutcomeGame (I : Type*) (A : I → Type*) (O : Type*) where
  /-- The outcome determined by an action profile. -/
  outcome : (∀ i, A i) → O

/-- Each player evaluates outcomes by a utility function taking values in `V`. -/
structure PayoffStructure (I : Type*) (O : Type*) (V : Type*) where
  /-- Each player's utility for an outcome. -/
  payoff : I → O → V

variable {ι : Type*} {A : ι → Type*} {O : Type*} {V : Type*}

/-- The strategic payoffs of an outcome game evaluated by the players' utilities. -/
def StrategicGame.ofOutcome (G : OutcomeGame ι A O) (P : PayoffStructure ι O V) :
    StrategicGame ι A V where
  payoff i a := P.payoff i (G.outcome a)

/-- A player's strategic payoff is the utility of the resulting outcome. -/
@[simp] lemma StrategicGame.ofOutcome_payoff (G : OutcomeGame ι A O) (P : PayoffStructure ι O V)
    (i : ι) (a : ∀ i, A i) : (StrategicGame.ofOutcome G P).payoff i a =
      P.payoff i (G.outcome a) := rfl

section Measurable

open MeasureTheory

open scoped ProbabilityTheory

variable [∀ i, MeasurableSpace (A i)] [MeasurableSpace O]

namespace OutcomeGame

/-- An outcome game is measurable when its outcome function is measurable. -/
protected class Measurable (G : OutcomeGame ι A O) where
  /-- Measurability of the outcome as a function of the action profile. -/
  measurable_outcome : Measurable G.outcome

export Measurable (measurable_outcome)

/-- The outcome distribution induced by independent mixed actions.

For a game with stochastic outcomes, this gives a distribution over outcome distributions;
`mixedFlattened` gives the corresponding distribution over outcomes. -/
@[simps] noncomputable def mixed (G : OutcomeGame ι A O) [G.Measurable] [Fintype ι] :
    OutcomeGame ι (fun i ↦ ProbabilityMeasure (A i)) (ProbabilityMeasure O) where
  outcome a := (ProbabilityMeasure.pi a).map G.measurable_outcome.aemeasurable

/-- The outcome distribution induced by independent mixed actions in a game with stochastic
outcomes, integrating the conditional outcome distributions over the action profile. -/
@[simps] noncomputable def mixedFlattened (G : OutcomeGame ι A (ProbabilityMeasure O))
    [G.Measurable] [Fintype ι] :
    OutcomeGame ι (fun i ↦ ProbabilityMeasure (A i)) (ProbabilityMeasure O) where
  outcome := ProbabilityMeasure.join ∘ G.mixed.outcome

/-- Independent mixing preserves measurability of the outcome game. -/
instance (G : OutcomeGame ι A O) [G.Measurable] [Fintype ι] : G.mixed.Measurable where
  measurable_outcome := (ProbabilityMeasure.measurable_map G.measurable_outcome).comp
    ProbabilityMeasure.measurable_pi

/-- Mixing and integrating stochastic outcomes preserves measurability. -/
instance (G : OutcomeGame ι A (ProbabilityMeasure O)) [G.Measurable] [Fintype ι] :
    G.mixedFlattened.Measurable where
  measurable_outcome :=
    (ProbabilityMeasure.measurable_join (α := O)).comp G.mixed.measurable_outcome

end OutcomeGame

namespace PayoffStructure

/-- A payoff structure is measurable when every player's utility is measurable. -/
protected class Measurable [MeasurableSpace V] (P : PayoffStructure ι O V) where
  /-- Measurability of each player's utility over outcomes. -/
  measurable_payoff i : Measurable (P.payoff i)

/-- A payoff structure is bounded when every player's utility has bounded range. -/
protected class Bounded [Bornology V] (P : PayoffStructure ι O V) where
  /-- Boundedness of each player's range of utilities. -/
  isBounded_payoff_range i : Bornology.IsBounded (Set.range (P.payoff i))

export PayoffStructure.Measurable (measurable_payoff)

export PayoffStructure.Bounded (isBounded_payoff_range)

/-- Players evaluate outcome distributions by expected utility in a complete real normed space.

Measurability and continuity instances for expected utility are provided for real-valued
utilities. -/
noncomputable def expected [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (P : PayoffStructure ι O V) : PayoffStructure ι (ProbabilityMeasure O) V where
  payoff i μ := μ[P.payoff i]

/-- Real expected utility is measurable for bounded measurable utilities. -/
instance (P : PayoffStructure ι O ℝ) [P.Measurable] [P.Bounded] : P.expected.Measurable where
  measurable_payoff i :=
    ProbabilityMeasure.measurable_integral (P.measurable_payoff i) (P.isBounded_payoff_range i)

/-- Expected utility is bounded whenever utility over outcomes is bounded. -/
instance [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (P : PayoffStructure ι O V) [P.Bounded] : P.expected.Bounded where
  isBounded_payoff_range i := by
    have hbounded := P.isBounded_payoff_range i
    simp_rw [isBounded_iff_forall_norm_le, Set.forall_mem_range] at hbounded ⊢
    refine hbounded.imp fun C hC μ ↦ ?_
    simpa using norm_integral_le_of_norm_le_const (μ := μ) <| .of_forall hC

end PayoffStructure

end Measurable

section Continuous

variable [∀ i, TopologicalSpace (A i)] [TopologicalSpace O]

namespace OutcomeGame

/-- An outcome game is continuous when its outcome function is continuous. -/
protected class Continuous (G : OutcomeGame ι A O) where
  /-- Continuity of the outcome as a function of the action profile. -/
  continuous_outcome : Continuous G.outcome

export Continuous (continuous_outcome)

/-- A continuous outcome game is measurable for a countable product of second-countable action
spaces with measurable open sets and a Borel outcome space. -/
instance Continuous.instMeasurable [∀ i, MeasurableSpace (A i)] [MeasurableSpace O] [Countable ι]
    [∀ i, OpensMeasurableSpace (A i)] [∀ i, SecondCountableTopology (A i)] [BorelSpace O]
    (G : OutcomeGame ι A O) [G.Continuous] : G.Measurable where
  measurable_outcome := continuous_outcome.measurable

/-- Independent mixing preserves continuity for finitely many second-countable pseudometrizable
action spaces with measurable open sets and a Borel outcome space. -/
instance [∀ i, MeasurableSpace (A i)] [MeasurableSpace O] [∀ i, OpensMeasurableSpace (A i)]
    [BorelSpace O] [∀ i, SecondCountableTopology (A i)]
    [∀ i, TopologicalSpace.PseudoMetrizableSpace (A i)] [Fintype ι] (G : OutcomeGame ι A O)
    [G.Continuous] : G.mixed.Continuous where
  continuous_outcome := (MeasureTheory.ProbabilityMeasure.continuous_map G.continuous_outcome).comp
    MeasureTheory.ProbabilityMeasure.continuous_pi

end OutcomeGame

namespace PayoffStructure

/-- A payoff structure is continuous when every player's utility is continuous. -/
protected class Continuous [TopologicalSpace V] (P : PayoffStructure ι O V) where
  /-- Continuity of each player's utility over outcomes. -/
  continuous_payoff i : Continuous (P.payoff i)

export Continuous (continuous_payoff)

/-- Continuous utilities into a Borel value space are measurable when open sets in the outcome
space are measurable. -/
instance Continuous.instMeasurable [MeasurableSpace O] [OpensMeasurableSpace O]
    [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] (P : PayoffStructure ι O V)
    [P.Continuous] : P.Measurable where
  measurable_payoff i := (continuous_payoff i).measurable

/-- Real expected utility is continuous for continuous utilities on a compact outcome space with
measurable open sets. -/
instance (P : PayoffStructure ι O ℝ) [MeasurableSpace O] [OpensMeasurableSpace O] [CompactSpace O]
    [P.Continuous] : P.expected.Continuous where
  continuous_payoff i := MeasureTheory.ProbabilityMeasure.continuous_integral_continuousMap <|
    ContinuousMap.mk _ <| P.continuous_payoff i

end PayoffStructure

end Continuous

end Auctionlib.GameTheory
