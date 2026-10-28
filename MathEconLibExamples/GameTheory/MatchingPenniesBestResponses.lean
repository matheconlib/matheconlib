/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.GameTheory.Choice
public import MathEconLibExamples.GameTheory.MatchingPennies

/-!
# Every mixed action responds optimally to a uniform matching-pennies opponent

Apply the shared best-response correspondence to the canonical matching-pennies game's finite
mixed extension. Against a uniform opponent, every independent mixed action gives expected payoff
zero. The correspondence therefore retains every mixed action, including the explicit action
assigning probability three quarters to heads and one quarter to tails.

This is a one-player best-response statement. A biased action against a uniform opponent need not
form a Nash equilibrium: the opponent must also respond optimally to that biased action.

## Main statements

* `bestResponses_uniform_eq_univ`: every mixed action is a best response to a uniform opponent.
* `biasedAction_mem_bestResponses`: a nonuniform mixed action belongs to that correspondence.
* `uniform_isNash_of_bestResponses`: the named Nash bridge recovers the uniform equilibrium.
-/

@[expose] public noncomputable section

open MathEconLib.GameTheory MathEconLib.Probability

namespace MathEconLibExamples.GameTheory.MatchingPennies

private lemma payoff_uniform_opponent (i : Fin 2) (τ : FinDist (Fin 2)) :
    matchingPennies.finiteMixedExtension.payoff i (Function.update uniformProfile i τ) = 0 := by
  fin_cases i <;>
    simp [StrategicGame.finiteMixedExtension, expectedPayoff_p0_closed,
      expectedPayoff_p1_closed, headsBias, uniformProfile, p0, p1]

/-- Every mixed action attains the same greatest payoff against a uniform opponent. -/
theorem bestResponses_uniform_eq_univ (i : Fin 2) :
    matchingPennies.finiteMixedExtension.bestResponses i uniformProfile = Set.univ :=
  Set.eq_univ_iff_forall.mpr fun τ ↦
    (StrategicGame.mem_bestResponses _ i uniformProfile τ).mpr fun τ' ↦
      le_of_eq ((payoff_uniform_opponent i τ').trans (payoff_uniform_opponent i τ).symm)

/-- The best-response set stays universal when the player's own incumbent action is changed. -/
theorem bestResponses_uniform_opponent_eq_univ (i : Fin 2) (σ : FinDist (Fin 2)) :
    matchingPennies.finiteMixedExtension.bestResponses i (Function.update uniformProfile i σ) =
      Set.univ := by
  simpa only [StrategicGame.bestResponses_update] using bestResponses_uniform_eq_univ i

/-- A mixed, biased action: probability three quarters on heads and one quarter on tails. -/
def biasedAction : FinDist (Fin 2) :=
  FinDist.mixture ⟨3 / 4, by norm_num⟩ (FinDist.pure heads) (FinDist.pure tails)

/-- Both action probabilities are positive and differ from uniform randomization. -/
theorem biasedAction_probabilities : biasedAction heads = 3 / 4 ∧ biasedAction tails = 1 / 4 := by
  norm_num [biasedAction, ← FinDist.pmf_eq_coe, FinDist.mixture_pmf, FinDist.pure_pmf, heads, tails]

/-- The explicit biased action is retained for either player against a uniform opponent. -/
theorem biasedAction_mem_bestResponses (i : Fin 2) :
    biasedAction ∈ matchingPennies.finiteMixedExtension.bestResponses i uniformProfile := by
  simp [bestResponses_uniform_eq_univ]

/-- The shared best-response characterization verifies the uniform mixed Nash equilibrium. -/
theorem uniform_isNash_of_bestResponses :
    matchingPennies.finiteMixedExtension.IsNash uniformProfile :=
  (StrategicGame.isNash_iff_mem_bestResponses _ _).mpr fun i ↦ by
    simp [bestResponses_uniform_eq_univ]

end MathEconLibExamples.GameTheory.MatchingPennies
