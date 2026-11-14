/-
Copyright (c) 2026 Yaron Velner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaron Velner
-/
module

public import MathEconLib.GameTheory.Strategic.Existence

/-!
# Tic-tac-toe: verified strategies and Nash equilibrium payoffs

This example represents tic-tac-toe as a two-player, zero-sum strategic game. The players
alternate moves, but each strategic-form action is a complete deterministic policy mapping
boards to moves. A bounded simulator evaluates the resulting play. Illegal moves
count as losses, so even policies choosing occupied squares have well-defined payoffs.

The example defines explicit non-losing strategies for X and O. Exhaustive Boolean checkers
explore every legal opposing move, and soundness theorems connect their results to the game
simulator. It follows that every **pure** Nash equilibrium has payoff zero for both players.

## Main definitions

* `Board`, `Strategy`, `StrategyProfile`: The board and strategy representations.
* `playAccordingToStrategyProfile`: Bounded simulation of a strategy profile.
* `ticTacToe`: The strategic game with win/loss/draw payoffs of `1`, `-1`, and `0`.
* `xStrategy`, `oStrategy`: Explicit deterministic strategies for the two players.

## Verification

* `checkXNeverLoses`, `checkONeverLoses`: Exhaustive checks against all legal opponent moves.
* `xStrategy_never_loses`, `oStrategy_never_loses`: Soundness-based non-loss guarantees.
* `ticTacToe_payoff_add_eq_zero`: The game's payoff sum is zero.

## Main result

* `ticTacToe_nash_payoffs_eq_zero`: Both payoffs vanish in any pure Nash equilibrium.

## Tags

tic-tac-toe, strategic games, pure strategies, nash equilibrium, zero-sum games,
exhaustive verification
-/

@[expose] public noncomputable section

open MathEconLib.GameTheory

namespace MathEconLibExamples.GameTheory.TicTacToe

/-!
## Players, boards, and game semantics
-/

/-- The two players of tic-tac-toe, represented by `Fin 2`. -/
abbrev Player := Fin 2

/-- Player X (`0`), who moves first. -/
abbrev X : Fin 2 := 0

/-- Player O (`1`), who moves second. -/
abbrev O : Fin 2 := 1

/-- A board position, represented by a row and column in `Fin 3`. -/
abbrev Position := Fin 3 × Fin 3

/-- A board assigning each position either no mark or a player mark. -/
abbrev Board := Position → Option Player

/-- A deterministic policy selecting a position from the current board. -/
abbrev Strategy := Board → Position

/-- A pair of deterministic strategies, indexed by player. -/
abbrev StrategyProfile := Player → Strategy

/-- Return the other player. -/
def otherPlayer (p : Player) : Player :=
  if p = X then O else X

/-- The initial board, with every square empty. -/
abbrev emptyBoard : Board := fun _ ↦ none

/-- Sentinel board awarding X the win when O attempts an illegal move. -/
abbrev xWinningBoard : Board := fun _ ↦ some X

/-- Sentinel board awarding O the win when X attempts an illegal move. -/
abbrev oWinningBoard : Board := fun _ ↦ some O

/-- Check whether a player occupies a complete row, column, or diagonal. -/
def hasWon (b : Board) (p : Player) : Bool :=
  decide (
    -- A winning row
    (∃ r : Fin 3, ∀ c : Fin 3, b (r, c) = some p) ∨
    -- A winning column
    (∃ c : Fin 3, ∀ r : Fin 3, b (r, c) = some p) ∨
    -- Main diagonal
    (∀ i : Fin 3, b (i, i) = some p) ∨
    -- Other diagonal
    (b (0, 2) = some p ∧
     b (1, 1) = some p ∧
     b (2, 0) = some p)
  )

/-- Check whether every square is occupied. -/
def boardFull (b : Board) : Bool :=
  (List.finRange 3).all fun i ↦
    (List.finRange 3).all fun j ↦
      (b (i, j)).isSome

/-- Check whether a player has won or the board is full. -/
def gameOver (b : Board) : Bool :=
  hasWon b X || hasWon b O || boardFull b

/-- Simulate at most `remainingSteps` turns from a given board.
An illegal move ends the game with the other player winning; the result is a
sentinel board rather than the last legally reachable board. -/
def playAccordingToStrategyProfile (σ : StrategyProfile) (remainingSteps : Nat)
    (p : Player) (b : Board) : Board :=
  match remainingSteps with
  | 0 => b
  | n + 1 =>
      if gameOver b then
        b
      else
        let pos := σ p b
        if (b pos).isSome then
          if p = X then
            oWinningBoard  -- X loses for making an illegal move
          else
            xWinningBoard  -- O loses for making an illegal move
        else
          playAccordingToStrategyProfile σ n (otherPlayer p)
            (Function.update b pos (some p))

/-- The strategic-form representation of tic-tac-toe. Each action is a complete
board-dependent policy; a win pays `1`, a loss pays `-1`, and a draw pays `0`.
Illegal moves are treated as losses. -/
abbrev ticTacToe : StrategicGame Player (fun _ ↦ Strategy) ℝ where
  payoff i σ :=
    let b := playAccordingToStrategyProfile σ 9 X emptyBoard
    if hasWon b X then
      if i = X then 1 else -1
    else if hasWon b O then
      if i = O then 1 else -1
    else
      0

/-!
## Strategy heuristics
-/

/-- Find the first empty square that completes a line of two marks belonging
to the opponent of `p`. This can be used to block that line, or to find a
winning move by passing the other player as `p`. -/
def findOpponentWinningMove (p : Player) (b : Board) : Option Position :=
  let opponent : Player := otherPlayer p
  -- Top row
  if b (0, 0) = opponent ∧ b (0, 1) = opponent ∧ b (0, 2) = none then
    some (0, 2)
  else if b (0, 0) = opponent ∧ b (0, 1) = none ∧ b (0, 2) = opponent then
    some (0, 1)
  else if b (0, 0) = none ∧ b (0, 1) = opponent ∧ b (0, 2) = opponent then
    some (0, 0)
  -- Middle row
  else if b (1, 0) = opponent ∧ b (1, 1) = opponent ∧ b (1, 2) = none then
    some (1, 2)
  else if b (1, 0) = opponent ∧ b (1, 1) = none ∧ b (1, 2) = opponent then
    some (1, 1)
  else if b (1, 0) = none ∧ b (1, 1) = opponent ∧ b (1, 2) = opponent then
    some (1, 0)
  -- Bottom row
  else if b (2, 0) = opponent ∧ b (2, 1) = opponent ∧ b (2, 2) = none then
    some (2, 2)
  else if b (2, 0) = opponent ∧ b (2, 1) = none ∧ b (2, 2) = opponent then
    some (2, 1)
  else if b (2, 0) = none ∧ b (2, 1) = opponent ∧ b (2, 2) = opponent then
    some (2, 0)
  -- Left column
  else if b (0, 0) = opponent ∧ b (1, 0) = opponent ∧ b (2, 0) = none then
    some (2, 0)
  else if b (0, 0) = opponent ∧ b (1, 0) = none ∧ b (2, 0) = opponent then
    some (1, 0)
  else if b (0, 0) = none ∧ b (1, 0) = opponent ∧ b (2, 0) = opponent then
    some (0, 0)
  -- Middle column
  else if b (0, 1) = opponent ∧ b (1, 1) = opponent ∧ b (2, 1) = none then
    some (2, 1)
  else if b (0, 1) = opponent ∧ b (1, 1) = none ∧ b (2, 1) = opponent then
    some (1, 1)
  else if b (0, 1) = none ∧ b (1, 1) = opponent ∧ b (2, 1) = opponent then
    some (0, 1)
  -- Right column
  else if b (0, 2) = opponent ∧ b (1, 2) = opponent ∧ b (2, 2) = none then
    some (2, 2)
  else if b (0, 2) = opponent ∧ b (1, 2) = none ∧ b (2, 2) = opponent then
    some (1, 2)
  else if b (0, 2) = none ∧ b (1, 2) = opponent ∧ b (2, 2) = opponent then
    some (0, 2)
  -- Main diagonal
  else if b (0, 0) = opponent ∧ b (1, 1) = opponent ∧ b (2, 2) = none then
    some (2, 2)
  else if b (0, 0) = opponent ∧ b (1, 1) = none ∧ b (2, 2) = opponent then
    some (1, 1)
  else if b (0, 0) = none ∧ b (1, 1) = opponent ∧ b (2, 2) = opponent then
    some (0, 0)
  -- Antidiagonal
  else if b (2, 0) = opponent ∧ b (1, 1) = opponent ∧ b (0, 2) = none then
    some (0, 2)
  else if b (2, 0) = opponent ∧ b (1, 1) = none ∧ b (0, 2) = opponent then
    some (1, 1)
  else if b (2, 0) = none ∧ b (1, 1) = opponent ∧ b (0, 2) = opponent then
    some (2, 0)
  else
    none

/-- Return the first empty corner, if one exists. -/
def findEmptyCorner (b : Board) : Option Position :=
  if b (0, 0) = none then
    some (0, 0)
  else if b (0, 2) = none then
    some (0, 2)
  else if b (2, 0) = none then
    some (2, 0)
  else if b (2, 2) = none then
    some (2, 2)
  else
    none

/-- Return the first empty square in row-major order, if one exists. -/
def findEmptySquare (b : Board) : Option Position := Id.run do
  for i in List.finRange 3 do
    for j in List.finRange 3 do
      if b (i, j) = none then
        return some (i, j)
  return none

/-- Score a candidate position by unoccupied-by-`p` rows and columns.
An additional point is awarded for each such line containing an opponent mark. -/
def positionScore (p : Player) (pos : Position) (b : Board) : Fin 5 := Id.run do
  let mut score : Fin 5 := 0
  let opponent : Player := otherPlayer p
  -- Score the row.
  if b (pos.1, 0) ≠ p ∧ b (pos.1, 1) ≠ p ∧ b (pos.1, 2) ≠ p then
    score := score + 1
    if b (pos.1, 0) = opponent ∨ b (pos.1, 1) = opponent ∨ b (pos.1, 2) = opponent then
      score := score + 1
  -- Score the column.
  if b (0, pos.2) ≠ p ∧ b (1, pos.2) ≠ p ∧ b (2, pos.2) ≠ p then
    score := score + 1
    if b (0, pos.2) = opponent ∨ b (1, pos.2) = opponent ∨ b (2, pos.2) = opponent then
      score := score + 1
  return score

/-- Choose the position with the higher `positionScore`, preferring the
second position in case of a tie. -/
def higherScoringPosition (p : Player) (pos1 : Position) (pos2 : Position) (b : Board) : Position :=
  if positionScore p pos1 b > positionScore p pos2 b then
    pos1
  else
    pos2

/-- Select the higher-scoring position in the first eligible pair
of opposite empty squares. Not a global search over all moves. -/
def findPreferredEmptyOppositePosition (p : Player) (b : Board) : Option Position :=
  if b (1, 0) = none ∧ b (1, 2) = none then
    higherScoringPosition p (1, 0) (1, 2) b
  else if b (0, 1) = none ∧ b (2, 1) = none then
    higherScoringPosition p (0, 1) (2, 1) b
  -- Opposite corners on the main diagonal.
  else if b (0, 0) = none ∧ b (2, 2) = none then
    higherScoringPosition p (0, 0) (2, 2) b
  -- Opposite corners on the antidiagonal.
  else if b (2, 0) = none ∧ b (0, 2) = none then
    higherScoringPosition p (2, 0) (0, 2) b
  else
    none

/-- A fixed strategy for X: take the center, block immediate threats, then prefer
corners and finally any empty square. Its non-losing property is proved below. -/
def xStrategy : Strategy := fun b ↦
  if b (1, 1) = none then
    (1, 1)
  else
    -- first check if we must do a move to block O from winning in the next move.
    match findOpponentWinningMove X b with
    | some pos => pos
    | none =>
        -- catch the corners
        match findEmptyCorner b with
        | some pos => pos
        | none =>
            -- do whatever
            match findEmptySquare b with
            | some pos => pos
            -- unreachable
            | none => (0, 0)

/-- A fixed strategy for O using immediate wins, blocks, corners, and a positional
heuristic. Its non-losing property is proved below. -/
def oStrategy : Strategy := fun b ↦
  if b (1, 1) = none then
    -- if X didn't take the middle in the first move, then take it now
    (1, 1)
  else
    if b (1, 1) = X ∧ b (0, 2) = none then
      -- if X took the middle, O prefer the upper-right corner
      (0, 2)
  else
    -- see if can win in this move
    match findOpponentWinningMove X b with
    | some pos => pos
    | none =>
      -- if there is a move that is necessary to block X from winning in next move, then do it
      match findOpponentWinningMove O b with
      | some pos => pos
      | none =>
          if b (1, 1) = X then
            -- If X holds the middle, then take the corners
            match findEmptyCorner b with
            | some pos => pos
            | none =>
              -- do whatever
              match findEmptySquare b with
              | some pos => pos
              -- unreachable
              | none => (0, 0)
          else
            -- If O holds the middle, then find a move that will force X to block O in the next move
            -- Use a simple positional score to compare paired candidates.
            match findPreferredEmptyOppositePosition O b with
            | some pos => pos
            | none =>
                -- do whatever
                match findEmptySquare b with
                | some pos => pos
                -- unreachable
                | none => (0, 0)

/-!
## Exhaustive strategy checks
-/

/-- Exhaustively check that X avoids defeat from a position, while X follows
`xStrategy` and O may choose any legal move. Returns `false` for an illegal X move. -/
def checkXNeverLoses (fuel : Nat) (p : Player) (b : Board) : Bool :=
  match fuel with
  | 0 =>
      !hasWon b O
  | n + 1 =>
      if gameOver b then
        !hasWon b O
      else if p = X then
        -- X follows our fixed strategy.
        let pos := xStrategy b
        if (b pos).isSome then
          false  -- X makes an illegal move and loses
        else
          checkXNeverLoses n O (Function.update b pos (some X))
      else
        -- Check EVERY possible legal move by O.
        (List.finRange 3).all fun i ↦
          (List.finRange 3).all fun j ↦
            if (b (i, j)).isNone then
              checkXNeverLoses n X
                (Function.update b (i, j) (some O))
            else
              true

/-- Exhaustively check that O avoids defeat from a position, while O follows
`oStrategy` and X may choose any legal move. Returns `false` for an illegal O move. -/
def checkONeverLoses (fuel : Nat) (p : Player) (b : Board) : Bool :=
  match fuel with
  | 0 =>
      !hasWon b X
  | n + 1 =>
      if gameOver b then
        !hasWon b X
      else if p = O then
        -- O follows our fixed strategy.
        let pos := oStrategy b
        if (b pos).isSome then
          false  -- O makes an illegal move and loses
        else
          checkONeverLoses n X (Function.update b pos (some O))
      else
        -- Check EVERY possible legal move by X.
        (List.finRange 3).all fun i ↦
          (List.finRange 3).all fun j ↦
            if (b (i, j)).isNone then
              checkONeverLoses n O
                (Function.update b (i, j) (some X))
            else
              true

/-! informal check that X's strategy never loses. -/
example : checkXNeverLoses 9 X emptyBoard = true := by decide +kernel

/-! informal check that Y's strategy never loses. -/
example : checkONeverLoses 9 X emptyBoard = true := by decide +kernel

/-!
## Checker soundness and non-losing strategies
-/

/-- If the X checker succeeds with O to move, its check succeeds after
any particular legal O move. -/
private lemma checkXNeverLoses_of_o_move
    (n : Nat) (b : Board)
    (hgame : gameOver b = false)
    (h : checkXNeverLoses (n + 1) O b = true)
    (pos : Position) (hempty : (b pos).isNone = true) :
    checkXNeverLoses n X (Function.update b pos (some O)) = true := by
  have hall :
      (List.finRange 3).all (fun i ↦
        (List.finRange 3).all (fun j ↦
          if (b (i, j)).isNone then
            checkXNeverLoses n X (Function.update b (i, j) (some O))
          else true)) = true := by
    simpa [checkXNeverLoses, hgame, X, O] using h
  rcases pos with ⟨i, j⟩
  have hi := (List.all_eq_true.mp hall) i (List.mem_finRange i)
  have hj := (List.all_eq_true.mp hi) j (List.mem_finRange j)
  simpa [hempty] using hj

/-- A successful X checker implies that actual play against any O strategy
cannot end with O winning, provided X uses `xStrategy`. -/
private theorem checkXNeverLoses_sound
    (σ : StrategyProfile) (hX : σ X = xStrategy) :
    ∀ n p b, checkXNeverLoses n p b = true →
      hasWon (playAccordingToStrategyProfile σ n p b) O = false := by
  intro n
  induction n with
  | zero =>
      intro p b h
      cases hw : hasWon b O <;> simp_all [checkXNeverLoses, playAccordingToStrategyProfile]
  | succ n ih =>
      intro p b h
      cases hgame : gameOver b with
      | true =>
          cases hw : hasWon b O <;>
            simp_all [checkXNeverLoses, playAccordingToStrategyProfile]
      | false =>
          by_cases hp : p = X
          · subst p
            cases hocc : (b (xStrategy b)).isSome with
            | true =>
                simp [checkXNeverLoses, hgame, hocc] at h
            | false =>
                have hnext :
                    checkXNeverLoses n O
                      (Function.update b (xStrategy b) (some X)) = true := by
                  simpa [checkXNeverLoses, hgame, hocc] using h
                have hplay :
                    playAccordingToStrategyProfile σ (n + 1) X b =
                      playAccordingToStrategyProfile σ n O
                        (Function.update b (xStrategy b) (some X)) := by
                  simp [playAccordingToStrategyProfile, hgame, hX, hocc, otherPlayer, X, O]
                rw [hplay]
                exact ih O _ hnext
          · have hpO : p = O := by
              fin_cases p <;> simp_all [X, O]
            subst p
            let pos := σ O b
            cases hocc : (b pos).isSome with
            | true =>
                have hplay : playAccordingToStrategyProfile σ (n + 1) O b = xWinningBoard := by
                  simp [playAccordingToStrategyProfile, hgame, pos, hocc, X, O]
                rw [hplay]
                decide +kernel
            | false =>
                have hempty : (b pos).isNone = true := by
                  cases hv : b pos with
                  | none => simp []
                  | some _ => simp [hv] at hocc
                have hnext := checkXNeverLoses_of_o_move n b hgame h pos hempty
                have hplay :
                    playAccordingToStrategyProfile σ (n + 1) O b =
                      playAccordingToStrategyProfile σ n X
                        (Function.update b pos (some O)) := by
                  simp [playAccordingToStrategyProfile, hgame, pos, hocc, otherPlayer, X, O]
                rw [hplay]
                exact ih X _ hnext

/-- X cannot lose from the empty board when following `xStrategy`,
against any deterministic O strategy. -/
theorem xStrategy_never_loses (oStrategy : Strategy) :
    hasWon
      (playAccordingToStrategyProfile
        (fun p ↦ if p = X then xStrategy else oStrategy)
        9 X emptyBoard)
      O = false := by
  let σ : StrategyProfile := fun p ↦ if p = X then xStrategy else oStrategy
  have hX : σ X = xStrategy := by simp [σ]
  have hcheck : checkXNeverLoses 9 X emptyBoard = true := by
    decide +kernel
  exact checkXNeverLoses_sound σ hX 9 X emptyBoard hcheck

/-- If the O checker succeeds with X to move, its check succeeds after
any particular legal X move. -/
private lemma checkONeverLoses_of_x_move
    (n : Nat) (b : Board)
    (hgame : gameOver b = false)
    (h : checkONeverLoses (n + 1) X b = true)
    (pos : Position) (hempty : (b pos).isNone = true) :
    checkONeverLoses n O (Function.update b pos (some X)) = true := by
  have hall :
      (List.finRange 3).all (fun i ↦
        (List.finRange 3).all (fun j ↦
          if (b (i, j)).isNone then
            checkONeverLoses n O (Function.update b (i, j) (some X))
          else true)) = true := by
    simpa [checkONeverLoses, hgame, X, O] using h
  rcases pos with ⟨i, j⟩
  have hi := (List.all_eq_true.mp hall) i (List.mem_finRange i)
  have hj := (List.all_eq_true.mp hi) j (List.mem_finRange j)
  simpa [hempty] using hj

/-- A successful O checker implies that actual play against any X strategy
cannot end with X winning, provided O uses `oStrategy`. -/
private theorem checkONeverLoses_sound
    (σ : StrategyProfile) (hO : σ O = oStrategy) :
    ∀ n p b, checkONeverLoses n p b = true →
      hasWon (playAccordingToStrategyProfile σ n p b) X = false := by
  intro n
  induction n with
  | zero =>
      intro p b h
      cases hw : hasWon b X <;> simp_all [checkONeverLoses, playAccordingToStrategyProfile]
  | succ n ih =>
      intro p b h
      cases hgame : gameOver b with
      | true =>
          cases hw : hasWon b X <;> simp_all [checkONeverLoses, playAccordingToStrategyProfile]
      | false =>
          by_cases hp : p = O
          · subst p
            cases hocc : (b (oStrategy b)).isSome with
            | true =>
                simp [checkONeverLoses, hgame, hocc, O] at h
            | false =>
                have hnext :
                    checkONeverLoses n X
                      (Function.update b (oStrategy b) (some O)) = true := by
                  simpa [checkONeverLoses, hgame, hocc, X, O] using h
                have hplay :
                    playAccordingToStrategyProfile σ (n + 1) O b =
                      playAccordingToStrategyProfile σ n X
                        (Function.update b (oStrategy b) (some O)) := by
                  simp [playAccordingToStrategyProfile, hgame, hO, hocc, otherPlayer, X, O]
                rw [hplay]
                exact ih X _ hnext
          · have hpX : p = X := by
              fin_cases p <;> simp_all [X, O]
            subst p
            let pos := σ X b
            cases hocc : (b pos).isSome with
            | true =>
                have hplay : playAccordingToStrategyProfile σ (n + 1) X b = oWinningBoard := by
                  simp [playAccordingToStrategyProfile, hgame, pos, hocc, X]
                rw [hplay]
                decide +kernel
            | false =>
                have hempty : (b pos).isNone = true := by
                  cases hv : b pos with
                  | none => simp []
                  | some _ => simp [hv] at hocc
                have hnext := checkONeverLoses_of_x_move n b hgame h pos hempty
                have hplay :
                    playAccordingToStrategyProfile σ (n + 1) X b =
                      playAccordingToStrategyProfile σ n O
                        (Function.update b pos (some X)) := by
                  simp [playAccordingToStrategyProfile, hgame, pos, hocc, otherPlayer, X, O]
                rw [hplay]
                exact ih O _ hnext

/-- O cannot lose from the empty board when following `oStrategy`,
against any deterministic X strategy. -/
theorem oStrategy_never_loses (xStrat : Strategy) :
    hasWon
      (playAccordingToStrategyProfile
        (fun p ↦ if p = O then oStrategy else xStrat)
        9 X emptyBoard)
      X = false := by
  let σ : StrategyProfile := fun p ↦ if p = O then oStrategy else xStrat
  have hO : σ O = oStrategy := by simp [σ, O]
  have hcheck : checkONeverLoses 9 X emptyBoard = true := by
    decide +kernel
  exact checkONeverLoses_sound σ hO 9 X emptyBoard hcheck

/-!
## Nash equilibrium payoffs
-/

/-- At every pure strategy profile, the two players’ payoffs sum to zero. -/
private lemma ticTacToe_payoff_add_eq_zero (σ : StrategyProfile) :
    ticTacToe.payoff X σ + ticTacToe.payoff O σ = 0 := by
  let b := playAccordingToStrategyProfile σ 9 X emptyBoard
  change (if hasWon b X then (1 : ℝ) else if hasWon b O then -1 else 0) +
    (if hasWon b X then (-1 : ℝ) else if hasWon b O then 1 else 0) = 0
  cases hx : hasWon b X <;> cases ho : hasWon b O <;> simp []

/-- In every pure Nash equilibrium, both players receive zero payoff.
Each player can guarantee a nonnegative payoff and the game is zero-sum. -/
theorem ticTacToe_nash_payoffs_eq_zero
    (σ : StrategyProfile) (hσ : ticTacToe.IsNash σ) :
    ticTacToe.payoff X σ = 0 ∧ ticTacToe.payoff O σ = 0 := by
  rw [StrategicGame.isNash_iff] at hσ
  have hdevX := hσ X xStrategy
  have hdevO := hσ O oStrategy
  have hupdateX :
      Function.update σ X xStrategy =
        (fun p ↦ if p = X then xStrategy else σ O) := by
    funext p
    fin_cases p <;> simp [X, O]
  have hupdateO :
      Function.update σ O oStrategy =
        (fun p ↦ if p = O then oStrategy else σ X) := by
    funext p
    fin_cases p <;> simp [X, O]
  have hx : 0 ≤ ticTacToe.payoff X (Function.update σ X xStrategy) := by
    rw [hupdateX]
    let b := playAccordingToStrategyProfile
      (fun p ↦ if p = X then xStrategy else σ O) 9 X emptyBoard
    have hno : hasWon b O = false := xStrategy_never_loses (σ O)
    change 0 ≤ (if hasWon b X then (1 : ℝ) else if hasWon b O then -1 else 0)
    cases hw : hasWon b X <;> simp [hno]
  have ho : 0 ≤ ticTacToe.payoff O (Function.update σ O oStrategy) := by
    rw [hupdateO]
    let b := playAccordingToStrategyProfile
      (fun p ↦ if p = O then oStrategy else σ X) 9 X emptyBoard
    have hno : hasWon b X = false := oStrategy_never_loses (σ X)
    change 0 ≤ (if hasWon b X then (-1 : ℝ) else if hasWon b O then 1 else 0)
    cases hw : hasWon b O <;> simp [hno]
  have hX : 0 ≤ ticTacToe.payoff X σ := le_trans hx hdevX
  have hO : 0 ≤ ticTacToe.payoff O σ := le_trans ho hdevO
  have hzero := ticTacToe_payoff_add_eq_zero σ
  constructor <;> linarith


end MathEconLibExamples.GameTheory.TicTacToe
end
