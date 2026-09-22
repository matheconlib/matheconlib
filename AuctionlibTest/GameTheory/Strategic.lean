/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Auctionlib.GameTheory.Strategic.Existence
import Mathlib.Logic.Equiv.Prod

/-!
# Matching pennies and the prisoners' dilemma

Matching pennies has no pure Nash equilibrium and has a fair-coin mixed equilibrium. In the
prisoners' dilemma, mutual defection is strict Nash while mutual cooperation is not Nash. The
outcome-distribution representation gives the same expected utilities and mixed equilibria.

## Main definitions

* `matchingPennies`: A two-player zero-sum game of matching or opposing actions.
* `prisonersDilemma`: A two-player game in which defection is strictly dominant.
* `fairCoin`: Uniform randomization over Boolean actions.

## Main statements

* `matchingPennies_not_isNash` and `matchingPennies_isFiniteMixedNash_fairCoin`.
* `prisonersDilemma_isStrictNash_defect` and `prisonersDilemma_not_isNash_cooperate`.

## Tags

matching pennies, prisoners dilemma, nash equilibrium
-/

@[expose] public noncomputable section

open Auctionlib.GameTheory Auctionlib.Probability MeasureTheory

namespace AuctionlibTest.GameTheory

/-- Player `true` receives one when actions agree and negative one otherwise; player `false`
receives the opposite payoff. -/
def matchingPennies : StrategicGame Bool (fun _ ↦ Bool) ℝ where
  payoff i a := if (a false = a true) = (i = true) then 1 else -1

/-- Matching pennies has no pure Nash equilibrium. -/
theorem matchingPennies_not_isNash (a : Bool → Bool) : ¬ matchingPennies.IsNash a := by
  rw [StrategicGame.isNash_iff]
  intro h
  have hfalse := h false (!(a false))
  have htrue := h true (!(a true))
  cases hf : a false <;> cases ht : a true <;>
    simp [matchingPennies, hf, ht, Function.update] at hfalse htrue <;> linarith

/-- Defection is `true`; mutual defection pays one, mutual cooperation pays two, and unilateral
defection pays three to the defector and zero to the cooperator. -/
def prisonersDilemma : StrategicGame Bool (fun _ ↦ Bool) ℝ where
  payoff i a := if a i then (if a (!i) then 1 else 3) else (if a (!i) then 0 else 2)

/-- Mutual defection is a strict Nash equilibrium of the prisoners' dilemma. -/
theorem prisonersDilemma_isStrictNash_defect : prisonersDilemma.IsStrictNash (fun _ ↦ true) := by
  intro i b hb
  cases i <;> cases b
  all_goals first | exact (hb rfl).elim | norm_num [prisonersDilemma, Function.update]

/-- Mutual defection is a Nash equilibrium. -/
example : prisonersDilemma.IsNash (fun _ ↦ true) := prisonersDilemma_isStrictNash_defect.isNash

/-- A cooperator facing cooperation gains by defecting. -/
theorem prisonersDilemma_not_isNash_cooperate : ¬ prisonersDilemma.IsNash (fun _ ↦ false) := by
  rw [StrategicGame.isNash_iff]
  intro h
  have := h false true
  norm_num [prisonersDilemma, Function.update] at this

/-- Uniform randomization over two actions. -/
def fairCoin : FinDist Bool := ⟨fun _ ↦ 1 / 2, by constructor <;> norm_num⟩

/-- Each Boolean action has probability one half under the fair coin. -/
@[simp] lemma fairCoin_apply (b : Bool) : fairCoin b = 1 / 2 := rfl

/-- A sum over Boolean action profiles has four terms, one for each pair of actions. -/
private lemma sum_bool_profiles (f : (Bool → Bool) → ℝ) :
    ∑ a, f a = f (fun _ ↦ false) + f (fun b ↦ b) +
      f (fun b ↦ !b) + f (fun _ ↦ true) := by
  rw [← (Equiv.boolArrowEquivProd Bool).symm.sum_comp]
  simp [Fintype.sum_prod_type, Equiv.boolArrowEquivProd]
  ring

/-- Expected matching-pennies payoff is the probability of agreement minus disagreement for player
`true`, and its negative for player `false`. -/
private lemma matchingPennies_payoff (i : Bool) (σ : Bool → stdSimplex ℝ Bool) :
    matchingPennies.finiteExpectedPayoff i σ =
      (if i then 1 else -1) *
      (σ false false * σ true false + σ false true * σ true true -
        σ false false * σ true true - σ false true * σ true false) := by
  rw [StrategicGame.finiteExpectedPayoff_eq_sum]
  rw [sum_bool_profiles]
  cases i <;> simp [matchingPennies] <;> ring

/-- Fair randomization is a mixed Nash equilibrium against all simplex deviations. -/
theorem matchingPennies_isFiniteMixedNash_fairCoin :
    matchingPennies.IsFiniteMixedNash (fun _ ↦ fairCoin) := by
  rw [StrategicGame.isFiniteMixedNash_iff]
  intro i τ
  rw [matchingPennies_payoff, matchingPennies_payoff]
  cases i <;> simp [Function.update]

/-- The prisoners' dilemma admits a finite mixed Nash equilibrium. -/
example : ∃ σ, prisonersDilemma.IsFiniteMixedNash σ := prisonersDilemma.exists_isFiniteMixedNash

/-- Fair independent probability measures form a mixed Nash equilibrium of matching pennies. -/
example : matchingPennies.IsMixedNash
    (StrategicGame.toProbability (fun _ ↦ fairCoin)) :=
  (StrategicGame.isFiniteMixedNash_iff_isMixedNash _ _).1
    matchingPennies_isFiniteMixedNash_fairCoin

/-- The outcome is one when the actions agree and negative one otherwise, valued in `ℝ`. -/
def outcomeExample : OutcomeGame Bool (fun _ ↦ Bool) ℝ where
  outcome a := if a false = a true then 1 else -1

/-- The outcome map is measurable on the finite action-profile space. -/
instance : outcomeExample.Measurable := ⟨measurable_of_countable _⟩

/-- The two players assign opposite utility to the scalar outcome. -/
def utilities : PayoffStructure Bool ℝ ℝ where
  payoff i x := if i then x else -x

/-- Both players' utilities are measurable in the scalar outcome. -/
instance : utilities.Measurable := ⟨fun i ↦ by cases i <;> dsimp [utilities] <;> fun_prop⟩

/-- Simplex and outcome-distribution representations give the same expected utility. -/
example (i : Bool) (σ : Bool → stdSimplex ℝ Bool) :
    (StrategicGame.ofOutcome outcomeExample utilities).finiteExpectedPayoff i σ =
      (StrategicGame.ofOutcome outcomeExample.mixed utilities.expected).payoff i
        (StrategicGame.toProbability σ) :=
  StrategicGame.finiteExpectedPayoff_eq_ofOutcome_mixed_payoff _ _ _ _

/-- Simplex and outcome-distribution representations give the same mixed Nash equilibria. -/
example (σ : Bool → stdSimplex ℝ Bool) :
    (StrategicGame.ofOutcome outcomeExample utilities).IsFiniteMixedNash σ ↔
      (StrategicGame.ofOutcome outcomeExample.mixed utilities.expected).IsNash
        (StrategicGame.toProbability σ) :=
  StrategicGame.isFiniteMixedNash_iff_ofOutcome_mixed_isNash _ _ _

end AuctionlibTest.GameTheory

end
