/-
Copyright (c) 2026 Yaron Velner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaron Velner
-/
module

public import MathEconLibExamples

/-!
# Tic-tac-toe tests

These examples test the strategic-form tic-tac-toe implementation in
`MathEconLibExamples.GameTheory.TicTacToe`. They check the move-count adapter,
winning play for either player, the penalty for selecting an occupied square,
and a draw between the example's non-losing strategies.

A strategy is a function from boards to positions, so it can choose an illegal
move. The simulator treats an attempt to play on any occupied square as an
immediate loss, regardless of which player occupies it.

The test strategies below select moves by the number of occupied squares.
Since X moves first, X acts at counts `0`, `2`, `4`, `6`, and `8`, while O acts
at counts `1`, `3`, `5`, and `7`. The payoff assertions use `decide +kernel`
to compute Boolean winning conditions before simplifying real-valued payoffs.

## Tests

* The move counter correctly counts occupied squares.
* X and O can each win against a specified opponent strategy.
* Either player loses for replaying its own square or selecting the opponent's square.
* The verified non-losing strategies produce a draw when played against one another.

## Tags

tic-tac-toe, strategic games, executable tests, illegal moves, payoffs
-/

@[expose] public noncomputable section

open MathEconLibExamples.GameTheory.TicTacToe

namespace MathEconLibTest.GameTheory.TicTacToe

/-!
## Test strategies

The helpers in this section are private to the test module. They make it easy to
specify a complete strategy by listing moves for successive turns, including
moves that are deliberately illegal.
-/

/-- A board with three occupied squares, used to test `moveCount`. -/
private def exampleBoard : Board :=
  fun (i, j) ↦
    ![
      ![none, some X, none],
      ![some X, some O, none],
      ![none, none, none]
    ] i j

/-- The number of occupied positions on a board. -/
private def moveCount (b : Board) : Nat :=
  ((Finset.univ : Finset Position).filter (fun pos ↦ b pos ≠ none)).card

/-- Turn a sequence of moves indexed by occupied-square count into a strategy. -/
private def moveNumberStrategy (f : Nat → Position) : Strategy :=
  fun b ↦ f (moveCount b)

/-- A fixed X strategy that completes the antidiagonal against `basicOStrategy`. -/
private def basicXStrategy : Strategy :=
  moveNumberStrategy fun
    | 0 => (0, 0)
    | 2 => (2, 0)
    | 4 => (1, 1)
    | 6 => (0, 2)
    | 8 => (2, 2)
    | _ => (0, 0)

/-- A fixed O strategy used as the opponent in X's winning and illegal-move tests. -/
private def basicOStrategy : Strategy :=
  moveNumberStrategy fun
    | 1 => (1, 0)
    | 3 => (0, 1)
    | 5 => (2, 1)
    | 7 => (1, 2)
    | _ => (0, 0)

/-- An X strategy that leaves the main diagonal available to O. -/
private def losingXStrategy : Strategy :=
  moveNumberStrategy fun
    | 0 => (1, 0)
    | 2 => (1, 2)
    | 4 => (0, 1)
    | 6 => (2, 1)
    | _ => (0, 0)

/-- An O strategy that completes the main diagonal against `losingXStrategy`. -/
private def winningOStrategy : Strategy :=
  moveNumberStrategy fun
    | 1 => (0, 0)
    | 3 => (1, 1)
    | 5 => (2, 2)
    | _ => (0, 0)

/-- X illegally attempts to reuse its own center square on its fourth turn. -/
private def xRepeatsOwnSquare : Strategy :=
  fun b ↦ if moveCount b = 6 then (1, 1) else basicXStrategy b

/-- X illegally attempts to use O's square `(2, 1)` on its fourth turn. -/
private def xUsesOpponentsSquare : Strategy :=
  fun b ↦ if moveCount b = 6 then (2, 1) else basicXStrategy b

/-- O illegally attempts to use X's square `(0, 0)` on its third turn. -/
private def oUsesOpponentsSquare : Strategy :=
  fun b ↦ if moveCount b = 5 then (0, 0) else basicOStrategy b

/-- O illegally attempts to reuse its own square `(1, 0)` on its third turn. -/
private def oRepeatsOwnSquare : Strategy :=
  fun b ↦ if moveCount b = 5 then (1, 0) else basicOStrategy b

/-!
## Move counting and legal wins
-/

/-- The example board contains exactly three marks. -/
example : moveCount exampleBoard = 3 := by
  decide

/-- X wins by completing `(2, 0)`, `(1, 1)`, `(0, 2)`. -/
example : ticTacToe.payoff X ![basicXStrategy, basicOStrategy] = (1 : ℝ) := by
  have hx :
      hasWon
        (playAccordingToStrategyProfile
          ![basicXStrategy, basicOStrategy] 9 X emptyBoard) X = true := by
    decide +kernel
  simp [hx]

/-- O wins by completing `(0, 0)`, `(1, 1)`, `(2, 2)`. -/
example : ticTacToe.payoff O ![losingXStrategy, winningOStrategy] = (1 : ℝ) := by
  have hx :
      hasWon
        (playAccordingToStrategyProfile
          ![losingXStrategy, winningOStrategy] 9 X emptyBoard) X = false := by
    decide +kernel
  have ho :
      hasWon
        (playAccordingToStrategyProfile
          ![losingXStrategy, winningOStrategy] 9 X emptyBoard) O = true := by
    decide +kernel
  simp [hx, ho]

/-!
## Illegal moves

In each test below, the offending player chooses an occupied square before the
game ends naturally. The resulting sentinel board awards the win to the other
player, so the offender's payoff is `-1`.
-/

/-- X loses for selecting its own previously occupied center square. -/
example : ticTacToe.payoff X ![xRepeatsOwnSquare, basicOStrategy] = (-1 : ℝ) := by
  have hx :
      hasWon
        (playAccordingToStrategyProfile
          ![xRepeatsOwnSquare, basicOStrategy] 9 X emptyBoard) X = false := by
    decide +kernel
  have ho :
      hasWon
        (playAccordingToStrategyProfile
          ![xRepeatsOwnSquare, basicOStrategy] 9 X emptyBoard) O = true := by
    decide +kernel
  simp [hx, ho]

/-- X loses for selecting a square already occupied by O. -/
example : ticTacToe.payoff X ![xUsesOpponentsSquare, basicOStrategy] = (-1 : ℝ) := by
  have hx :
      hasWon
        (playAccordingToStrategyProfile
          ![xUsesOpponentsSquare, basicOStrategy] 9 X emptyBoard) X = false := by
    decide +kernel
  have ho :
      hasWon
        (playAccordingToStrategyProfile
          ![xUsesOpponentsSquare, basicOStrategy] 9 X emptyBoard) O = true := by
    decide +kernel
  simp [hx, ho]

/-- O loses for selecting a square already occupied by X. -/
example : ticTacToe.payoff O ![basicXStrategy, oUsesOpponentsSquare] = (-1 : ℝ) := by
  have hx :
      hasWon
        (playAccordingToStrategyProfile
          ![basicXStrategy, oUsesOpponentsSquare] 9 X emptyBoard) X = true := by
    decide +kernel
  simp [hx]

/-- O loses for selecting its own previously occupied square. -/
example : ticTacToe.payoff O ![basicXStrategy, oRepeatsOwnSquare] = (-1 : ℝ) := by
  have hx :
      hasWon
        (playAccordingToStrategyProfile
          ![basicXStrategy, oRepeatsOwnSquare] 9 X emptyBoard) X = true := by
    decide +kernel
  simp [hx]

/-!
## Draw between non-losing strategies
-/

/-- Both players receive zero when using the example's verified non-losing strategies. -/
example : ticTacToe.payoff X ![xStrategy, oStrategy] = (0 : ℝ) ∧
    ticTacToe.payoff O ![xStrategy, oStrategy] = (0 : ℝ) := by
  have hx :
      hasWon
        (playAccordingToStrategyProfile
          ![xStrategy, oStrategy] 9 X emptyBoard) X = false := by
    decide +kernel
  have ho :
      hasWon
        (playAccordingToStrategyProfile
          ![xStrategy, oStrategy] 9 X emptyBoard) O = false := by
    decide +kernel
  constructor <;> simp [hx, ho]

end MathEconLibTest.GameTheory.TicTacToe
end
