/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import MathEconLib.SingleParameter.PostedPrice
public import MathEconLibExamples

/-!
# Dominance, matching pennies, the prisoners' dilemma, and posted pricing

The uniform equilibrium of matching pennies also holds for independent probability measures. In the
prisoners' dilemma, mutual defection is strict Nash while mutual cooperation is not Nash. The
outcome-distribution representation gives the same expected utilities and mixed equilibria.
Additional games compare strict dominance at every opponent profile with the strict part of the
weak-dominance preorder. An empty opponent action space leaves no profiles, so pointwise strict
dominance holds vacuously without a strict payoff comparison. A buyer's posted-price choice is a
one-player Nash equilibrium by universal incentive compatibility over both purchase decisions.

## Main definitions

* `prisonersDilemma`: A two-player game in which defection is strictly dominant.
* `tiedDominanceGame`: A game with ties at some opponent profiles.
* `emptyOpponentGame`: A game in which one player has no available action.
* `outcomeExample`: Matching pennies represented by a scalar agreement outcome.
* `utilities`: Opposite utilities for the scalar agreement outcome.
* `postedPriceGame`: A buyer's payoff from either purchase decision at a fixed price and type.

## Main statements

* `prisonersDilemma_isStrictlyDominant_defect`, `prisonersDilemma_isStrictNash_defect`, and
  `prisonersDilemma_not_isNash_cooperate`.
* `tiedDominanceGame_isStrictOrderDominant` and `tiedDominanceGame_not_isStrictlyDominant`.
* `tiedDominanceGame_not_isStrictNash`: Dominance in the strict preorder permits payoff ties.
* `outcomeExample_ofOutcome`: Evaluating the scalar outcome recovers matching pennies.
* `postedPriceGame_isNash`: The posted-price threshold strategy is Nash for every type in the
  stated interval.

## Tags

dominance, matching pennies, prisoners dilemma, posted price, nash equilibrium
-/

@[expose] public noncomputable section

open MathEconLib MathEconLib.GameTheory MathEconLib.Probability MeasureTheory

open MathEconLibExamples.GameTheory.MatchingPennies

namespace MathEconLibTest.GameTheory

/-- Every matching-pennies payoff is measurable on the finite profile space. -/
instance : matchingPennies.Measurable := ⟨fun _ ↦ measurable_of_countable _⟩

/-- Each matching-pennies player has a finite, hence bounded, payoff range. -/
instance : matchingPennies.Bounded where
  isBounded_payoff_range i := (Set.finite_range (matchingPennies.payoff i)).isBounded

/-- Matching-pennies utilities are bounded on action-profile outcomes. -/
example : matchingPennies.payoffStructure.Bounded := inferInstance

/-- Matching-pennies payoffs are integrable under every independent action law. -/
example (i : Fin 2) (σ : StrategicGame.MixedStrategy (fun _ : Fin 2 ↦ Fin 2)) :
    Integrable (matchingPennies.payoff i) (Measure.pi (fun j ↦ (σ j : Measure (Fin 2)))) :=
  matchingPennies.integrable_payoff_of_bounded i σ

/-- Matching pennies has the same mixed Nash equilibria as its integral extension. -/
example (σ : StrategicGame.MixedStrategy (fun _ : Fin 2 ↦ Fin 2)) :
    matchingPennies.IsMixedNash σ ↔ matchingPennies.mixedExtension.IsNash σ :=
  matchingPennies.isMixedNash_iff_isNash σ

/-- Defection is `true`; mutual defection pays one, mutual cooperation pays two, and unilateral
defection pays three to the defector and zero to the cooperator. -/
def prisonersDilemma : StrategicGame Bool (fun _ ↦ Bool) ℝ where
  payoff i a := if a i then (if a (!i) then 1 else 3) else (if a (!i) then 0 else 2)

/-- Defection strictly improves payoff against either action of the opponent. -/
theorem prisonersDilemma_isStrictlyDominant_defect (i : Bool) :
    StrategicGame.Strategy.IsStrictlyDominant (G := prisonersDilemma) (i := i) true := by
  intro b hb a
  cases b
  · cases i <;> (simp [prisonersDilemma, Function.update]; split <;> norm_num)
  · exact (hb rfl).elim

/-- Mutual defection is a strict Nash equilibrium of the prisoners' dilemma. -/
theorem prisonersDilemma_isStrictNash_defect : prisonersDilemma.IsStrictNash (fun _ ↦ true) :=
  StrategicGame.isStrictNash_of_isStrictlyDominant prisonersDilemma_isStrictlyDominant_defect

/-- Strict dominance implies dominance in the strict part of the weak-dominance preorder. -/
example (i : Bool) :
    StrategicGame.Strategy.IsStrictOrderDominant (G := prisonersDilemma) (i := i) true :=
  (prisonersDilemma_isStrictlyDominant_defect i).isStrictOrderDominant

/-- Mutual defection is a Nash equilibrium. -/
example : prisonersDilemma.IsNash (fun _ ↦ true) := prisonersDilemma_isStrictNash_defect.isNash

/-- A cooperator facing cooperation gains by defecting. -/
theorem prisonersDilemma_not_isNash_cooperate : ¬ prisonersDilemma.IsNash (fun _ ↦ false) := by
  rw [StrategicGame.isNash_iff]
  intro h
  have := h false true
  norm_num [prisonersDilemma, Function.update] at this

/-- Choosing `true` pays one against `false`; all other choices give zero. -/
def tiedDominanceGame : StrategicGame Bool (fun _ ↦ Bool) ℕ where
  payoff i a := if a i && !(a (!i)) then 1 else 0

/-- Choosing `true` weakly improves payoff everywhere and strictly improves it against `false`. -/
theorem tiedDominanceGame_isStrictOrderDominant (i : Bool) :
    StrategicGame.Strategy.IsStrictOrderDominant (G := tiedDominanceGame) (i := i) true := by
  intro b hb
  cases b
  · apply (StrategicGame.Strategy.lt_iff (G := tiedDominanceGame)
      (s := false) (s' := true) i).2
    constructor
    · apply (StrategicGame.Strategy.le_iff' (G := tiedDominanceGame)
        (i := i) (s := false) (s' := true)).2
      intro a
      cases i <;> simp [tiedDominanceGame, Function.update]
    · exact ⟨fun _ ↦ false, by cases i <;> norm_num [tiedDominanceGame, Function.update]⟩
  · exact (hb rfl).elim

/-- The payoff tie against `true` prevents pointwise strict dominance. -/
theorem tiedDominanceGame_not_isStrictlyDominant (i : Bool) :
    ¬ StrategicGame.Strategy.IsStrictlyDominant (G := tiedDominanceGame) (i := i) true := by
  intro h
  have hlt := h false Bool.false_ne_true (fun _ ↦ true)
  cases i <;> norm_num [tiedDominanceGame, Function.update] at hlt

/-- A profile dominant in the strict preorder is Nash even when payoff ties remain. -/
example : tiedDominanceGame.IsNash (fun _ ↦ true) :=
  StrategicGame.isNash_of_isDominant fun i ↦ (tiedDominanceGame_isStrictOrderDominant i).isDominant

/-- Dominance in the strict preorder does not force the resulting profile to be strict Nash. -/
theorem tiedDominanceGame_not_isStrictNash :
    ¬ tiedDominanceGame.IsStrictNash (fun _ ↦ true) := by
  intro h
  have hlt := h false false (by decide)
  norm_num [tiedDominanceGame, Function.update] at hlt

/-- Player `true` has no available action, so there are no action profiles. -/
def emptyOpponentGame : StrategicGame Bool (fun i ↦ if i then Empty else Bool) ℕ where
  payoff _ _ := 0

/-- Pointwise strict dominance is vacuous when an opponent has no available action. -/
example :
    StrategicGame.Strategy.IsStrictlyDominant (G := emptyOpponentGame) (i := false) true := by
  intro b hb a
  exact (a true).elim

/-- With no action profiles, distinct actions are equivalent in the weak-dominance preorder. -/
example :
    ¬ StrategicGame.Strategy.IsStrictOrderDominant (G := emptyOpponentGame) (i := false) true := by
  intro h
  obtain ⟨a, ha⟩ := ((StrategicGame.Strategy.lt_iff (G := emptyOpponentGame)
    (s := false) (s' := true) false).1 (h false Bool.false_ne_true)).2
  exact (a true).elim

/-- The prisoners' dilemma admits a finite mixed Nash equilibrium. -/
example : ∃ σ, prisonersDilemma.IsFiniteMixedNash σ := prisonersDilemma.exists_isFiniteMixedNash

/-- Fair independent probability measures form a mixed Nash equilibrium of matching pennies. -/
example : matchingPennies.IsMixedNash
    (StrategicGame.toProbability uniformProfile) :=
  (StrategicGame.isFiniteMixedNash_iff_isMixedNash _ _).1
    matchingPennies_uniform_is_mixed_nash

/-- The outcome is one when the actions agree and negative one otherwise, valued in `ℝ`. -/
def outcomeExample : OutcomeGame (Fin 2) (fun _ ↦ Fin 2) ℝ where
  outcome a := if a p0 = a p1 then 1 else -1

/-- The outcome map is measurable on the finite action-profile space. -/
instance : outcomeExample.Measurable := ⟨measurable_of_countable _⟩

/-- The two players assign opposite utility to the scalar outcome. -/
def utilities : PayoffStructure (Fin 2) ℝ ℝ where
  payoff i x := if i = p0 then x else -x

/-- Both players' utilities are measurable in the scalar outcome. -/
instance : utilities.Measurable := ⟨fun i ↦ by dsimp [utilities]; split_ifs <;> fun_prop⟩

/-- Evaluating the scalar agreement outcome gives the matching-pennies game. -/
lemma outcomeExample_ofOutcome :
    StrategicGame.ofOutcome outcomeExample utilities = matchingPennies := by
  unfold StrategicGame.ofOutcome matchingPennies
  congr 1
  funext i a
  dsimp [outcomeExample, utilities]
  split_ifs <;> norm_num

/-- Finite weights and outcome distributions give the same expected payoff in matching pennies. -/
example (i : Fin 2) (σ : Fin 2 → FinDist (Fin 2)) :
    matchingPennies.finiteExpectedPayoff i σ =
      (StrategicGame.ofOutcome outcomeExample.mixed utilities.expected).payoff i
        (StrategicGame.toProbability σ) := by
  simpa only [outcomeExample_ofOutcome] using
    StrategicGame.finiteExpectedPayoff_eq_ofOutcome_mixed_payoff outcomeExample utilities i σ

/-- Finite weights and outcome distributions give the same equilibria in matching pennies. -/
example (σ : Fin 2 → FinDist (Fin 2)) :
    matchingPennies.IsFiniteMixedNash σ ↔
      (StrategicGame.ofOutcome outcomeExample.mixed utilities.expected).IsNash
        (StrategicGame.toProbability σ) := by
  simpa only [outcomeExample_ofOutcome] using
    StrategicGame.isFiniteMixedNash_iff_ofOutcome_mixed_isNash outcomeExample utilities σ

/-- Finite weights and probability measures give the same equilibria in matching pennies. -/
example (σ : Fin 2 → FinDist (Fin 2)) :
    matchingPennies.IsFiniteMixedNash σ ↔
      matchingPennies.IsMixedNash (StrategicGame.toProbability σ) :=
  StrategicGame.isFiniteMixedNash_iff_isMixedNash _ _

/-- Converting finite weights to probability measures and back preserves the profile. -/
example (σ : Fin 2 → FinDist (Fin 2)) :
    StrategicGame.toSimplex (StrategicGame.toProbability σ) = σ :=
  StrategicGame.toSimplex_toProbability σ

/-- Converting probability measures to finite weights and back preserves the profile. -/
example (σ : StrategicGame.MixedStrategy (fun _ : Fin 2 ↦ Fin 2)) :
    StrategicGame.toProbability (StrategicGame.toSimplex σ) = σ :=
  StrategicGame.toProbability_toSimplex σ

/-! ## Posted-price choice -/

/-- The buyer chooses whether to purchase at a fixed price, with utility given by the posted-price
problem at type `v`. -/
def postedPriceGame (lowestType highestType price v : ℝ) :
    StrategicGame Unit (fun _ ↦ SingleParameterProblem.PurchaseDecision) ℝ where
  payoff _ a := (SingleParameterProblem.postedPriceProblem lowestType highestType price).payoff v
    (a ())

/-- Universal incentive compatibility makes the posted-price threshold choice Nash against both
purchase decisions for every type in the stated interval. -/
theorem postedPriceGame_isNash (lowestType highestType price v : ℝ)
    (hv : v ∈
      (SingleParameterProblem.postedPriceProblem lowestType highestType price).typeInterval) :
    (postedPriceGame lowestType highestType price v).IsNash
      (fun _ ↦
        (SingleParameterProblem.postedPriceProblem lowestType highestType price).strategy v) := by
  rw [StrategicGame.isNash_iff]
  intro i decision
  cases i
  simpa only [postedPriceGame, Function.update_self] using
    SingleParameterProblem.HasUniversalIC.universalIC
      (P := SingleParameterProblem.postedPriceProblem lowestType highestType price)
      (S := Set.univ) v hv decision (Set.mem_univ decision)

end MathEconLibTest.GameTheory

end
