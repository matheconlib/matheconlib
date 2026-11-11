/-
Copyright (c) 2026 Yaron Velner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaron Velner
-/
module

public import MathEconLib.GameTheory.Strategic.Existence

/-!
# Rock paper scissors and its unique mixed Nash equilibrium

Two players choose rock, paper or scissors. Paper beats rock, rock beats scissors,
and scissors beats paper. If both players choose the same action then it is a draw.
Winner gets a payoff of 1, loser gets -1, and in case of a draw both get 0.
No pure profile is a Nash equilibrium. The unique mixed Nash equilibrium has both
players independently choosing each action with probability 1/3,
giving each player expected payoff zero.

## Main definitions

* `rockPaperScissors`: The two-player, three-action zero-sum game.
* `uniformAction`: Equal probabilities on rock, paper, and scissors.
* `uniformProfile`: Uniform independent randomization by both players.
* `expectedPayoff_p0`: The expected payoff of Player 0, given a strategy profile.
* `expectedPayoff_p1`: The expected payoff of Player 1, given a strategy profile.

## Lemmas

* `expectedPayoff_p0_add_p1_eq_zero`: The players' expected payoffs sum to zero.
* `expectedPayoff_zero_of_uniformAction`: Either player's uniform mixed action gives expected
  payoff zero against any opponent action.
* `exists_p0_pos_payoff_response`: Against a nonuniform Player 1 mixed action, Player 0 has
  a pure response with strictly positive expected payoff.
* `exists_p1_pos_payoff_response`: Against a nonuniform Player 0 mixed action, Player 1 has
  a pure response with strictly positive expected payoff.

## Main statements

* `rockPaperScissors_exists_mixedNash`: Rock paper scissors admits a mixed Nash equilibrium.
* `rockPaperScissors_uniform_is_mixed_nash`: Uniform randomization is a mixed Nash equilibrium.
* `rockPaperScissors_mixed_nash_unique`: Every mixed Nash equilibrium is the uniform profile.
* `rockPaperScissors_no_pure_nash`: No pure Nash equilibrium exists.

## Tags

rock-paper-scissors, strategic games, mixed strategies, nash equilibrium, zero-sum games
-/

@[expose] public noncomputable section

open MathEconLib.GameTheory MathEconLib.Probability

namespace MathEconLibExamples.GameTheory.RockPaperScissors

/-!
## Setup

This section defines the game, introduces convenience abbreviations for each player and each
action for readability, and defines the uniform action distribution and profile.
-/

/-- Player 0. -/
abbrev p0 : Fin 2 := 0

/-- Player 1. -/
abbrev p1 : Fin 2 := 1

/-- The rock action. -/
abbrev rock : Fin 3 := 0

/-- The paper action. -/
abbrev paper : Fin 3 := 1

/-- The scissors action. -/
abbrev scissors : Fin 3 := 2

/-- Rock-paper-scissors: ties pay zero, while a win pays `1` to the winner and `-1`
to the loser. Rock beats scissors, paper beats rock, and scissors beats paper. -/
abbrev rockPaperScissors : StrategicGame (Fin 2) (fun _ ↦ Fin 3) ℝ where
  payoff i s := if i = p0 then
    -- recall that addition over Fin 3 is % 3, hence scissors + 1 = rock.
    if (s p0) = (s p1) + 1 then 1 else if (s p0 = s p1) then 0 else -1
  else
    if (s p0) = (s p1) + 1 then -1 else if (s p0 = s p1) then 0 else 1


/- draw -/
example : rockPaperScissors.payoff p0 ![rock, rock] = 0 := by trivial
example : rockPaperScissors.payoff p0 ![paper, paper] = 0 := by trivial
example : rockPaperScissors.payoff p0 ![scissors, scissors] = 0 := by trivial

example : rockPaperScissors.payoff p1 ![rock, rock] = 0 := by trivial
example : rockPaperScissors.payoff p1 ![paper, paper] = 0 := by trivial
example : rockPaperScissors.payoff p1 ![scissors, scissors] = 0 := by trivial

/- p0 win -/
example : rockPaperScissors.payoff p0 ![paper, rock] = 1 := by trivial
example : rockPaperScissors.payoff p0 ![scissors, paper] = 1 := by trivial
example : rockPaperScissors.payoff p0 ![rock, scissors] = 1 := by trivial

example : rockPaperScissors.payoff p1 ![paper, rock] = -1 := by trivial
example : rockPaperScissors.payoff p1 ![scissors, paper] = -1 := by trivial
example : rockPaperScissors.payoff p1 ![rock, scissors] = -1 := by trivial

/- p1 win -/
example : rockPaperScissors.payoff p0 ![rock, paper] = -1 := by trivial
example : rockPaperScissors.payoff p0 ![paper, scissors] = -1 := by trivial
example : rockPaperScissors.payoff p0 ![scissors, rock] = -1 := by trivial

example : rockPaperScissors.payoff p1 ![rock, paper] = 1 := by trivial
example : rockPaperScissors.payoff p1 ![paper, scissors] = 1 := by trivial
example : rockPaperScissors.payoff p1 ![scissors, rock] = 1 := by trivial


/-- The action distribution assigning probability 1/3 to each of the actions. -/
abbrev uniformAction : FinDist (Fin 3) := FinDist.uniform

/-- The profile where both players independently randomize uniformly over their three actions. -/
def uniformProfile : Fin 2 → FinDist (Fin 3) :=
  fun _ ↦ uniformAction

/-- The expected payoff of Player 0, expressed in terms of the probabilities of each action. -/
def expectedPayoff_p0 (σ : Fin 2 → FinDist (Fin 3)) : ℝ :=
  (σ p0) rock *
    ((σ p1) scissors - (σ p1) paper) +
  (σ p0) paper *
    ((σ p1) rock - (σ p1) scissors) +
  (σ p0) scissors *
    ((σ p1) paper - (σ p1) rock)

/-- The expected payoff of Player 1, expressed in terms of the probabilities of each action. -/
def expectedPayoff_p1 (σ : Fin 2 → FinDist (Fin 3)) : ℝ :=
  (σ p1) rock *
    ((σ p0) scissors - (σ p0) paper) +
  (σ p1) paper *
    ((σ p0) rock - (σ p0) scissors) +
  (σ p1) scissors *
    ((σ p0) paper - (σ p0) rock)

/-!
## Intermediate results

This section proves some properties of the game for use in the main results later.
-/

/-- The sum over all two-player action profiles is the sum over the 9 options. -/
private lemma sum_action_profile (f : (Fin 2 → Fin 3) → ℝ) :
    ∑ s : Fin 2 → Fin 3, f s
      = f ![paper, rock] + f ![paper, paper] + f ![paper, scissors] +
        f ![rock, rock] + f ![rock, paper] + f ![rock, scissors] +
        f ![scissors, rock] + f ![scissors, paper] + f ![scissors, scissors] := by
  rw [← (finTwoArrowEquiv (Fin 3)).symm.sum_comp f, Fintype.sum_prod_type]
  simp [Fin.sum_univ_three, finTwoArrowEquiv, rock, paper, scissors]
  ring


/-- The game's finite expected payoff for Player 0 equals the explicit formula
`expectedPayoff_p0`. -/
lemma expectedPayoff_p0_closed
    (σ : Fin 2 → FinDist (Fin 3)) :
    rockPaperScissors.finiteExpectedPayoff p0 σ = expectedPayoff_p0 σ := by
  rw [StrategicGame.finiteExpectedPayoff_eq_sum,
      sum_action_profile]
  simp [Fin.prod_univ_two,
        p0, p1, rock, paper, scissors, expectedPayoff_p0]
  ring

/-- The game's finite expected payoff for Player 1 equals the explicit formula
`expectedPayoff_p1`. -/
lemma expectedPayoff_p1_closed
    (σ : Fin 2 → FinDist (Fin 3)) :
    rockPaperScissors.finiteExpectedPayoff p1 σ = expectedPayoff_p1 σ := by
  rw [StrategicGame.finiteExpectedPayoff_eq_sum,
      sum_action_profile]
  simp [Fin.prod_univ_two,
        p0, p1, rock, paper, scissors, expectedPayoff_p1]
  ring

/-- The two players' expected payoffs always sum to zero. -/
private lemma expectedPayoff_p0_add_p1_eq_zero
    (σ : Fin 2 → FinDist (Fin 3)) :
    expectedPayoff_p0 σ + expectedPayoff_p1 σ = 0 := by
  simp [expectedPayoff_p0, expectedPayoff_p1]
  ring

/-- A player choosing the uniform mixed action receives expected payoff zero against
any mixed action of the opponent. -/
lemma expectedPayoff_zero_of_uniformAction
    (p0Moves p1Moves : FinDist (Fin 3)) :
    expectedPayoff_p0 ![uniformAction, p1Moves] = 0 ∧
    expectedPayoff_p1 ![p0Moves, uniformAction] = 0 := by
  have h0 :
      expectedPayoff_p1 ![uniformAction, p1Moves] = 0 := by
    simp [uniformAction, expectedPayoff_p1]
  have h1 :
      expectedPayoff_p0 ![p0Moves, uniformAction] = 0 := by
    simp [uniformAction, expectedPayoff_p0]
  constructor
  · -- Player 0's payoff is zero when playing uniformly.
    have hz := expectedPayoff_p0_add_p1_eq_zero ![uniformAction, p1Moves]
    linarith
  · -- Player 1's payoff is zero when playing uniformly.
    have hz := expectedPayoff_p0_add_p1_eq_zero ![p0Moves, uniformAction]
    linarith


/-- Against a nonuniform mixed action of Player 0, Player 1 has a pure response with
strictly positive expected payoff. -/
lemma exists_p1_pos_payoff_response
    (opponentMoves : FinDist (Fin 3))
    (h : opponentMoves ≠ uniformAction) :
    ∃ a : Fin 3,
      expectedPayoff_p1
        ![opponentMoves, FinDist.pure a] > 0 := by
  by_cases hsp : opponentMoves scissors > opponentMoves paper
  · -- Case 1: Scissors > Paper. Play Rock.
    use rock
    simpa [expectedPayoff_p1, rock, scissors, paper] using hsp
  · by_cases hrs : opponentMoves rock > opponentMoves scissors
    · -- Case 2: Rock > Scissors. Play Paper.
      use paper
      simpa [expectedPayoff_p1, rock, scissors, paper] using hrs
    · by_cases hpr : opponentMoves paper > opponentMoves rock
      · -- Case 3: Paper > Rock. Play Scissors.
        use scissors
        simpa [expectedPayoff_p1, rock, scissors, paper] using hpr
      · -- Case 4: All three inequalities are false.
        -- Therefore all probabilities are equal.
        exfalso
        push Not at hsp hrs hpr
        have hsum :
            opponentMoves rock + opponentMoves paper +
              opponentMoves scissors = 1 := by
          simpa only [Fin.sum_univ_three,
                      FinDist.pmf_eq_coe,
                      rock, paper, scissors]
            using FinDist.sum_one opponentMoves
        have hr : opponentMoves rock = (1 / 3 : ℝ) := by
          linarith
        have hp : opponentMoves paper = (1 / 3 : ℝ) := by
          linarith
        have hs : opponentMoves scissors = (1 / 3 : ℝ) := by
          linarith
        -- This contradicts the assumption of nonuniformity.
        apply h
        ext a
        fin_cases a
        · simpa [uniformAction, rock, paper, scissors] using hr
        · simpa [uniformAction, rock, paper, scissors] using hp
        · simpa [uniformAction, rock, paper, scissors] using hs

/-- Against a nonuniform mixed action of Player 1, Player 0 has a pure response with
strictly positive expected payoff. -/
lemma exists_p0_pos_payoff_response
    (opponentMoves : FinDist (Fin 3))
    (h : opponentMoves ≠ uniformAction) :
    ∃ a : Fin 3,
      expectedPayoff_p0
        ![FinDist.pure a, opponentMoves] > 0 := by
  have h0 :
      ∀ b : Fin 3,
        expectedPayoff_p0 ![FinDist.pure b, opponentMoves] =
          expectedPayoff_p1 ![opponentMoves, FinDist.pure b] := by
    intro b
    simp [expectedPayoff_p0, expectedPayoff_p1]
  -- Obtain the profitable action for player 1.
  obtain ⟨a, ha⟩ := exists_p1_pos_payoff_response opponentMoves h
  -- Use the same action for player 0.
  use a
  -- By symmetry, the expected payoffs are equal.
  rw [h0 a]
  exact ha

/-!
## Main results

Finally, we assert the existence of a mixed Nash equilibrium, show that the uniform
profile is the unique mixed Nash equilibrium, and that no pure Nash equilibrium exists.
-/

/-- Rock paper scissors admits a mixed Nash equilibrium. -/
theorem rockPaperScissors_exists_mixedNash :
    ∃ σ : Fin 2 → FinDist (Fin 3), rockPaperScissors.IsFiniteMixedNash σ :=
  -- Notice that we do not need to provide any argument here: The existence argument is inherited
  -- from the `StrategicGame` and so does not need to be proved again.
  rockPaperScissors.exists_isFiniteMixedNash


/-- Every mixed Nash equilibrium is the uniform profile. -/
theorem rockPaperScissors_mixed_nash_unique
    (σ : Fin 2 → FinDist (Fin 3))
    (hσ : rockPaperScissors.IsFiniteMixedNash σ) :
    σ = uniformProfile := by
  rw [StrategicGame.isFiniteMixedNash_iff] at hσ
  -- First prove that player 0 must play uniformly.
  have hp0 : σ p0 = uniformAction := by
    by_contra hnon
    -- Since player 0 is nonuniform, player 1 has
    -- a pure response giving strictly positive payoff.
    obtain ⟨a, ha⟩ :=
      exists_p1_pos_payoff_response (σ p0) hnon
    -- Nash equilibrium: player 0 cannot improve
    -- by switching to the uniform strategy.
    have hdev0 := hσ p0 uniformAction
    -- Nash equilibrium: player 1 cannot improve
    -- by switching to pure action a.
    have hdev1 := hσ p1 (FinDist.pure a)
    -- Rewrite Function.update as explicit profiles.
    have hu0 :
        Function.update σ p0 uniformAction =
          ![uniformAction, σ p1] := by
      funext i
      fin_cases i <;> simp [p0, p1]
    have hu1 :
        Function.update σ p1 (FinDist.pure a) =
          ![σ p0, FinDist.pure a] := by
      funext i
      fin_cases i <;> simp [p0, p1]
    rw [hu0] at hdev0
    rw [hu1] at hdev1
    simp only [expectedPayoff_p0_closed] at hdev0
    simp only [expectedPayoff_p1_closed] at hdev1
    -- Uniform play guarantees player 0 zero payoff.
    have hz0 :=
      (expectedPayoff_zero_of_uniformAction (σ p0) (σ p1)).1
    rw [hz0] at hdev0
    -- The game is zero-sum.
    have hz := expectedPayoff_p0_add_p1_eq_zero σ
    -- Player 0's payoff >= 0.
    -- Player 1's payoff > 0.
    -- Their sum = 0. Contradiction!
    linarith
  -- We will prove player 1 is uniform.
  have hp1 : σ p1 = uniformAction := by
    by_contra hnon
    -- Against nonuniform player 1, player 0
    -- has a pure strategy with positive payoff.
    obtain ⟨a, ha⟩ :=
      exists_p0_pos_payoff_response (σ p1) hnon
    -- Nash equilibrium forbids player 0 from
    -- improving by switching to pure action a.
    have hdev := hσ p0 (FinDist.pure a)
    -- Rewrite the deviating strategy profile.
    have hupdate :
        Function.update σ p0 (FinDist.pure a) =
          ![FinDist.pure a, σ p1] := by
      funext i
      fin_cases i <;> simp [p0, p1]
    rw [hupdate] at hdev
    simp only [expectedPayoff_p0_closed] at hdev
    -- Since player 0 plays uniformly, their payoff is zero.
    have hpay0 : expectedPayoff_p0 σ = 0 := by
      have hprofile :
          σ = ![uniformAction, σ p1] := by
        funext i
        fin_cases i
        · simpa [p0] using hp0
        · rfl
      rw [hprofile]
      exact (expectedPayoff_zero_of_uniformAction (σ p0) (σ p1)).1
    -- Player 0 cannot improve beyond zero,
    -- but ha says a positive payoff is possible.
    linarith
  -- Both players are uniform, hence so is the profile.
  funext i
  fin_cases i
  · simpa [uniformProfile, p0] using hp0
  · simpa [uniformProfile, p1] using hp1


/-- Uniform randomization is a mixed Nash equilibrium. -/
theorem rockPaperScissors_uniform_is_mixed_nash :
    rockPaperScissors.IsFiniteMixedNash uniformProfile := by
  obtain ⟨σ, hσ⟩ := rockPaperScissors_exists_mixedNash
  have h := rockPaperScissors_mixed_nash_unique σ hσ
  rw [← h]
  exact hσ

/-- No pure Nash equilibrium exists. -/
theorem rockPaperScissors_no_pure_nash :
    ¬ ∃ s : Fin 2 → Fin 3,
      rockPaperScissors.IsNash s := by
  rw [(finTwoArrowEquiv (Fin 3)).exists_congr_left]
  rintro ⟨⟨a, b⟩, hs⟩
  rw [StrategicGame.isNash_iff] at hs
  -- Nash equilibrium forbids these six pure deviations.
  have h0r := hs p0 rock
  have h0p := hs p0 paper
  have h0s := hs p0 scissors
  have h1r := hs p1 rock
  have h1p := hs p1 paper
  have h1s := hs p1 scissors
  -- Check all 3 × 3 action profiles.
  fin_cases a <;> fin_cases b <;>
    norm_num [rockPaperScissors, finTwoArrowEquiv,
              p0, p1, rock, paper, scissors] at *


end MathEconLibExamples.GameTheory.RockPaperScissors

end
