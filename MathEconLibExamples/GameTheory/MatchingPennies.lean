/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import MathEconLib.GameTheory.Strategic.Existence

/-!
# Matching pennies and its unique mixed Nash equilibrium

Two players choose heads or tails. Player 0 receives one when the coins agree and minus one
otherwise; player 1 receives the opposite payoff. No pure profile is a Nash equilibrium. The unique
mixed Nash equilibrium has both players independently choose each action with probability one half,
giving each player expected payoff zero.

## Main definitions

* `matchingPennies`: The two-player, two-action zero-sum game.
* `uniformAction`: Equal probabilities on heads and tails.
* `uniformProfile`: Uniform independent randomization by both players.
* `headsBias`: Each player's probability of heads minus their probability of tails.

## Main statements

* `matchingPennies_exists_mixedNash`: Matching pennies admits a mixed Nash equilibrium.
* `matchingPennies_uniform_is_mixed_nash`: Uniform randomization is a mixed Nash equilibrium.
* `matchingPennies_mixed_nash_unique`: Every mixed Nash equilibrium is the uniform profile.
* `matchingPennies_no_pure_nash`: No pure Nash equilibrium exists.

## Tags

matching pennies, strategic games, mixed strategies, nash equilibrium, zero-sum games
-/

@[expose] public noncomputable section

open MathEconLib.GameTheory MathEconLib.Probability

namespace MathEconLibExamples.GameTheory.MatchingPennies

/-!
## Setup

This section defines the game, introduces convenience abbreviations for each player and each
action for readability, and defines the uniform action distribution and profile.
-/

/-- Player 0. -/
abbrev p0 : Fin 2 := 0

/-- Player 1. -/
abbrev p1 : Fin 2 := 1

/-- The heads action. -/
abbrev heads : Fin 2 := 0

/-- The tails action. -/
abbrev tails : Fin 2 := 1

/-- The game: Two players choose heads or tails, where player 0 wins agreement and player 1 wins
disagreement. -/
abbrev matchingPennies : StrategicGame (Fin 2) (fun _ ↦ Fin 2) ℝ where
  payoff i s := if i = p0 then
    if s p0 = s p1 then 1 else -1
  else
    if s p0 = s p1 then -1 else 1

/-- Player 0 receives a positive payoff when the coins agree. -/
example : matchingPennies.payoff p0 ![heads, heads] = 1 := by trivial

/-- Player 1 receives a negative payoff when the coins agree. -/
example : matchingPennies.payoff p1 ![heads, heads] = -1 := by trivial

/-- Player 1 receives a positive payoff when the coins disagree. -/
example : matchingPennies.payoff p1 ![heads, tails] = 1 := by trivial

/-- The action distribution assigning probability one half to heads and tails. -/
abbrev uniformAction : FinDist (Fin 2) := FinDist.uniform

/-- The profile where both players independently randomize uniformly over their two actions. -/
def uniformProfile : Fin 2 → FinDist (Fin 2) :=
  fun _ => uniformAction

/-- A player's probability of choosing heads minus their probability of choosing tails. Positive
values favor heads, negative values favor tails, and zero means uniform randomization. -/
def headsBias (σ : Fin 2 → FinDist (Fin 2)) (player : Fin 2) : ℝ :=
  (σ player) heads - (σ player) tails

/-!
## Intermediate results

This section proves some properties of the game for use in the main results later.
-/

/-- The sum over all two-player action profiles is the sum over the four coin pairs. -/
lemma sum_action_profile (f : (Fin 2 → Fin 2) → ℝ) :
    ∑ s : Fin 2 → Fin 2, f s
      = f ![heads, heads] + f ![heads, tails] + f ![tails, heads] + f ![tails, tails] := by
  rw [← (finTwoArrowEquiv (Fin 2)).symm.sum_comp f, Fintype.sum_prod_type]
  simp [Fin.sum_univ_two, finTwoArrowEquiv, heads, tails, add_assoc]

/-- Player 0's expected payoff is the product of the players' biases toward heads. -/
lemma expectedPayoff_p0_closed (σ : Fin 2 → FinDist (Fin 2)) :
    matchingPennies.finiteExpectedPayoff p0 σ
      = headsBias σ p0 * headsBias σ p1 := by
  rw [StrategicGame.finiteExpectedPayoff_eq_sum, sum_action_profile]
  simp [Fin.prod_univ_two, headsBias, p0, p1, heads, tails]
  ring

/-- Player 1's expected payoff is the negative product of the players' biases toward heads. -/
lemma expectedPayoff_p1_closed (σ : Fin 2 → FinDist (Fin 2)) :
    matchingPennies.finiteExpectedPayoff p1 σ
      = -(headsBias σ p0 * headsBias σ p1) := by
  rw [StrategicGame.finiteExpectedPayoff_eq_sum, sum_action_profile]
  simp [Fin.prod_univ_two, headsBias, p0, p1, heads, tails]
  ring

/-- Player 0's payoff after a pure deviation is the deviating action's heads bias times player 1's
heads bias. -/
lemma dev_p0_payoff (σ : Fin 2 → FinDist (Fin 2)) (a : Fin 2) :
    matchingPennies.finiteExpectedPayoff p0 (Function.update σ p0 (FinDist.pure a))
      = ((FinDist.pure a) heads - (FinDist.pure a) tails) * headsBias σ p1 := by
  simp [expectedPayoff_p0_closed, headsBias, p0, p1]

/-- Player 1's payoff after a pure deviation is the negative product of the two heads biases. -/
lemma dev_p1_payoff (σ : Fin 2 → FinDist (Fin 2)) (a : Fin 2) :
    matchingPennies.finiteExpectedPayoff p1 (Function.update σ p1 (FinDist.pure a))
      = -(headsBias σ p0 * ((FinDist.pure a) heads - (FinDist.pure a) tails)) := by
  simp [expectedPayoff_p1_closed, headsBias, p0, p1]

/-!
## Main results

Finally, we assert the existence of a mixed Nash equilibrium, show that the uniform
profile is the unique mixed Nash equilibrium, and that no pure Nash equilibrium exists.
-/

/-- Matching pennies admits a mixed Nash equilibrium. -/
theorem matchingPennies_exists_mixedNash :
    ∃ σ : Fin 2 → FinDist (Fin 2), matchingPennies.IsFiniteMixedNash σ :=
  -- Notice that we do not need to provide any argument here: The existence argument is inherited
  -- from the `StrategicGame` and so does not need to be proved again.
  matchingPennies.exists_isFiniteMixedNash

/-- The uniform profile is a mixed Nash equilibrium against every mixed deviation. -/
theorem matchingPennies_uniform_is_mixed_nash :
    matchingPennies.IsFiniteMixedNash uniformProfile := by
  rw [StrategicGame.isFiniteMixedNash_iff]
  intro i τ
  fin_cases i <;>
    simp [expectedPayoff_p0_closed, expectedPayoff_p1_closed, headsBias, uniformProfile, p0, p1]

/-- Every mixed Nash equilibrium of matching pennies is the uniform profile. -/
theorem matchingPennies_mixed_nash_unique
    (σ : Fin 2 → FinDist (Fin 2))
    (hσ : matchingPennies.IsFiniteMixedNash σ) :
    σ = uniformProfile := by
  -- Nash equilibrium bounds every unilateral deviation by the player's current expected payoff.
  rw [StrategicGame.isFiniteMixedNash_iff] at hσ
  -- Neither player can improve their equilibrium payoff by committing to heads or tails
  -- while the opponent keeps the same mixed action.
  have h00 := hσ p0 (FinDist.pure heads)
  have h01 := hσ p0 (FinDist.pure tails)
  have h10 := hσ p1 (FinDist.pure heads)
  have h11 := hσ p1 (FinDist.pure tails)
  -- Write α = headsBias σ p0 and β = headsBias σ p1.
  -- Incumbent payoffs are α * β and -(α * β); pure heads and tails have biases 1 and -1.
  rw [expectedPayoff_p0_closed σ, dev_p0_payoff] at h00 h01
  rw [expectedPayoff_p1_closed σ, dev_p1_payoff] at h10 h11
  -- The deviation bounds become β ≤ α * β, -β ≤ α * β,
  -- -α ≤ -(α * β), and α ≤ -(α * β).
  norm_num [headsBias, p0, p1, heads, tails] at h00 h01 h10 h11
  -- Each player's heads and tails probabilities sum to one.
  have hp0_sum : (σ p0) heads + (σ p0) tails = 1 := FinDist.sum_pmf_two (σ p0)
  have hp1_sum : (σ p1) heads + (σ p1) tails = 1 := FinDist.sum_pmf_two (σ p1)
  -- The first two deviation bounds imply 0 ≤ α * β; the last two imply α * β ≤ 0.
  -- Thus α * β = 0 and the bounds force α = β = 0.
  -- After normalization, all four action probabilities must equal one half.
  have : ∀ i x, σ i x = 1 / 2 := by
    simp only [Fin.forall_fin_two]
    repeat' constructor
    all_goals linarith
  -- Agreement on every action probability identifies σ as the uniform profile.
  ext i x
  simpa [uniformProfile, uniformAction] using this i x

/-- No pure Nash equilibrium exists: At every coin pair, the losing player can switch and win. -/
theorem matchingPennies_no_pure_nash :
    ¬ ∃ s : Fin 2 → Fin 2, matchingPennies.IsNash s := by
  rw [(finTwoArrowEquiv (Fin 2)).exists_congr_left]
  norm_num [Prod.exists, Fin.exists_fin_two, StrategicGame.isNash_iff,
    Fin.forall_fin_two, finTwoArrowEquiv, p0, p1]

end MathEconLibExamples.GameTheory.MatchingPennies

end
