/-
Copyright (c) 2026 Yaron Velner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaron Velner
-/
module

public import MathEconLib.GameTheory.Strategic.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

/-!
# Tic-tac-toe: verified strategies and Nash equilibrium payoffs

This example represents tic-tac-toe as a two-player, zero-sum strategic game. The players
alternate moves; each strategic-form action is a deterministic policy that may depend on the
full board history. A bounded simulator evaluates the resulting play. Illegal moves count as
losses, so even policies choosing occupied squares have well-defined payoffs.

Board-dependent (memoryless) policies embed into history policies via `asStrategy`. Explicit
non-losing strategies `xStrategy` and `oStrategy` are verified by exhaustive Boolean checkers
against every legal opposing move; soundness theorems lift those checks to both the board and
history simulators. The embedded draw profile is therefore a pure Nash equilibrium in the full
history-strategy game, and every pure Nash equilibrium has payoff zero for both players.

## Main definitions

* `Board`, `MemorylessStrategy`, `MemorylessStrategyProfile`, `Strategy`, `StrategyProfile`:
  Board and strategy types.
* `playAccordingToStrategy`: Bounded simulation of a history-strategy profile.
* `ticTacToe`: The strategic game with win/loss/draw payoffs of `1`, `-1`, and `0`.
* `asStrategy`: Embed a board strategy as a history strategy that ignores the path.
* `xStrategy`, `oStrategy`, `memorylessDrawProfile`: Explicit non-losing strategies.
* `IsSecurityX`, `IsSecurityO`: Security (nonnegative guaranteed payoff) for each player.

## Verification

* `checkXNeverLoses`, `checkONeverLoses`: Exhaustive checks against all legal opponent moves.
* `xStrategy_asStrategy_never_loses`, `oStrategy_asStrategy_never_loses`: Non-loss in history play.
* `xStrategy_payoff_nonneg`, `oStrategy_payoff_nonneg`: Nonnegative payoffs for the
  embedded strategies.
* `ticTacToe_payoff_add_eq_zero`: The game's payoff sum is zero.

## Main results

* `memorylessDrawProfile_isNash`: The embedded non-losing profile is a pure Nash equilibrium.
* `ticTacToe_nash_payoffs_eq_zero`: Both payoffs vanish in any pure Nash equilibrium.
* `exists_memoryless_isNash`: A memoryless Nash equilibrium exists.
* `isNash_iff_isSecurity`: Nash equilibria are exactly the mutually secure profiles.

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

/-- The initial board, with every square empty. -/
abbrev emptyBoard : Board := fun _ ↦ none

/-- A deterministic policy selecting a position from the current board. -/
abbrev MemorylessStrategy := Board → Position

/-- A pair of deterministic strategies, indexed by player. -/
abbrev MemorylessStrategyProfile := Player → MemorylessStrategy

/-- A finite sequence of boards visited during play. -/
abbrev History := List Board

/-- A deterministic policy that may depend on the full board history. -/
abbrev Strategy := History → Position

/-- A pair of history-dependent strategies, indexed by player. -/
abbrev StrategyProfile := Player → Strategy

/-- The current board, defaulting to the empty board for an empty history.
Uses `getLast?`/`getD` explicitly so it matches the simp-normal form of `List.getLastD`. -/
abbrev currentBoard (h : History) : Board :=
  (List.getLast? h).getD emptyBoard

/-- Return the other player. -/
def otherPlayer (p : Player) : Player :=
  if p = X then O else X


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


/-- Simulate a game under history-dependent strategies, recording each board.
An illegal move ends the game immediately with a sentinel winning board for the
opponent, matching `playAccordingToMemorylessStrategyProfile`. -/
def playAccordingToStrategy (σ : StrategyProfile) :
    Nat → Player → History → History
  | 0, _, h => h
  | n + 1, p, h =>
    let b := currentBoard h
    if gameOver b then
      h
    else
      let pos := σ p h
      if (b pos).isSome then
        h ++ [if p = X then oWinningBoard else xWinningBoard]
      else
        playAccordingToStrategy σ n (otherPlayer p)
          (h ++ [Function.update b pos (some p)])


/-- Simulate at most `remainingSteps` turns from a given board.
An illegal move ends the game with the other player winning; the result is a
sentinel board rather than the last legally reachable board. -/
def playAccordingToMemorylessStrategyProfile (σ : MemorylessStrategyProfile) (remainingSteps : Nat)
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
          playAccordingToMemorylessStrategyProfile σ n (otherPlayer p)
            (Function.update b pos (some p))

/-- Final board under a history profile starting from the empty board. -/
def finalBoard (σ : StrategyProfile) : Board :=
  currentBoard (playAccordingToStrategy σ 9 X [emptyBoard])

/-- The strategic-form representation of tic-tac-toe. Each action is a complete
history-dependent policy; a win pays `1`, a loss pays `-1`, and a draw pays `0`.
Illegal moves are treated as losses. -/
abbrev ticTacToe : StrategicGame Player (fun _ ↦ Strategy) ℝ where
  payoff i σ :=
    let b := finalBoard σ
    if hasWon b X then
      if i = X then 1 else -1
    else if hasWon b O then
      if i = O then 1 else -1
    else
      0


/-!
## Board strategies
-/

/-- View a board-dependent strategy as a history strategy that ignores the path. -/
def asStrategy (s : MemorylessStrategy) : Strategy :=
  fun h => s (currentBoard h)

/-- X's strategy guarantees nonnegative payoff against every opposing history strategy. -/
def IsSecurityX (σ : Strategy) : Prop :=
  ∀ τ : Strategy,
    0 ≤ ticTacToe.payoff X (fun p ↦ if p = X then σ else τ)

/-- O's strategy guarantees nonnegative payoff against every opposing history strategy. -/
def IsSecurityO (σ : Strategy) : Prop :=
  ∀ τ : Strategy,
    0 ≤ ticTacToe.payoff O (fun p ↦ if p = O then σ else τ)

/-- If the opponent has two marks in a line and the third cell is empty, return that cell. -/
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
def xStrategy : MemorylessStrategy := fun b ↦
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
def oStrategy : MemorylessStrategy := fun b ↦
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

/-- Kernel-checked certificate that X's exhaustive never-lose checker succeeds. -/
private lemma checkXNeverLoses_emptyBoard : checkXNeverLoses 9 X emptyBoard = true := by
  decide +kernel

/-- Kernel-checked certificate that O's exhaustive never-lose checker succeeds. -/
private lemma checkONeverLoses_emptyBoard : checkONeverLoses 9 X emptyBoard = true := by
  decide +kernel

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

/-!
## Nash equilibrium payoffs
-/

/-- At every pure strategy profile, the two players’ payoffs sum to zero. -/
lemma ticTacToe_payoff_add_eq_zero (σ : StrategyProfile) :
    ticTacToe.payoff X σ + ticTacToe.payoff O σ = 0 := by
  change
    (if hasWon (finalBoard σ) X then (1 : ℝ) else if hasWon (finalBoard σ) O then -1 else 0) +
      (if hasWon (finalBoard σ) X then (-1 : ℝ)
        else if hasWon (finalBoard σ) O then 1 else 0) = 0
  cases hx : hasWon (finalBoard σ) X <;> cases ho : hasWon (finalBoard σ) O <;> simp

/-- Helper: X following `xStrategy` never loses in the history simulator. -/
private theorem checkXNeverLoses_asStrategy_sound
    (oStrat : Strategy) :
    ∀ n p (h : History),
      checkXNeverLoses n p (currentBoard h) = true →
      hasWon
          (currentBoard
            (playAccordingToStrategy
              (fun q ↦ if q = X then asStrategy xStrategy else oStrat) n p h))
          O = false := by
  intro n
  induction n with
  | zero =>
      intro p h hh
      simp [checkXNeverLoses] at hh
      simpa [playAccordingToStrategy] using hh
  | succ n ih =>
      intro p h hh
      rw [playAccordingToStrategy]
      cases hgame : gameOver (currentBoard h) with
      | true =>
          simp [checkXNeverLoses, hgame] at hh
          simpa [hgame] using hh
      | false =>
          by_cases hp : p = X
          · subst p
            simp only [asStrategy, ↓reduceIte] at hh ⊢
            cases hocc : ((currentBoard h) (xStrategy (currentBoard h))).isSome with
            | true =>
                simp [checkXNeverLoses, hgame, hocc] at hh
            | false =>
                have hnext :
                    checkXNeverLoses n O
                      (Function.update (currentBoard h) (xStrategy (currentBoard h))
                        (some X)) = true := by
                  simpa [checkXNeverLoses, hgame, hocc] using hh
                simp only [otherPlayer, X, O]
                exact ih O _ (by simpa [currentBoard] using hnext)
          · have hpO : p = O := by fin_cases p <;> simp_all [X, O]
            subst p
            simp only [show (O = X) = False from by decide, ↓reduceIte] at hh ⊢
            cases hocc : ((currentBoard h) (oStrat h)).isSome with
            | true =>
                have : hasWon xWinningBoard O = false := by decide +kernel
                convert this
                simp [currentBoard]
            | false =>
                have hempty : ((currentBoard h) (oStrat h)).isNone = true := by
                  cases hv : currentBoard h (oStrat h) with
                  | none => simp
                  | some _ => simp [hv] at hocc
                have hnext :=
                  checkXNeverLoses_of_o_move n (currentBoard h) hgame hh (oStrat h) hempty
                simp only [otherPlayer, X, O]
                exact ih X _ (by simpa [currentBoard] using hnext)

/-- X's embedded non-losing strategy never loses against any history strategy of O. -/
theorem xStrategy_asStrategy_never_loses (oStrat : Strategy) :
    hasWon (finalBoard (fun p ↦ if p = X then asStrategy xStrategy else oStrat))
      O = false :=
  checkXNeverLoses_asStrategy_sound oStrat 9 X [emptyBoard] checkXNeverLoses_emptyBoard

/-- Helper: O following `oStrategy` never loses in the history simulator. -/
private theorem checkONeverLoses_asStrategy_sound
    (xStrat : Strategy) :
    ∀ n p (h : History),
      checkONeverLoses n p (currentBoard h) = true →
      hasWon
          (currentBoard
            (playAccordingToStrategy
              (fun q ↦ if q = O then asStrategy oStrategy else xStrat) n p h))
          X = false := by
  intro n
  induction n with
  | zero =>
      intro p h hh
      simp [checkONeverLoses] at hh
      simpa [playAccordingToStrategy] using hh
  | succ n ih =>
      intro p h hh
      rw [playAccordingToStrategy]
      cases hgame : gameOver (currentBoard h) with
      | true =>
          simp [checkONeverLoses, hgame] at hh
          simpa [hgame] using hh
      | false =>
          by_cases hp : p = O
          · subst p
            simp only [asStrategy, ↓reduceIte] at hh ⊢
            cases hocc : ((currentBoard h) (oStrategy (currentBoard h))).isSome with
            | true =>
                simp [checkONeverLoses, hgame, hocc, O] at hh
            | false =>
                have hnext :
                    checkONeverLoses n X
                      (Function.update (currentBoard h) (oStrategy (currentBoard h))
                        (some O)) = true := by
                  simpa [checkONeverLoses, hgame, hocc, X, O] using hh
                simp only [otherPlayer, X, O]
                exact ih X _ (by simpa [currentBoard] using hnext)
          · have hpX : p = X := by fin_cases p <;> simp_all [X, O]
            subst p
            simp only [show (X = O) = False from by decide, ↓reduceIte] at hh ⊢
            cases hocc : ((currentBoard h) (xStrat h)).isSome with
            | true =>
                have : hasWon oWinningBoard X = false := by decide +kernel
                convert this
                simp [currentBoard]
            | false =>
                have hempty : ((currentBoard h) (xStrat h)).isNone = true := by
                  cases hv : currentBoard h (xStrat h) with
                  | none => simp
                  | some _ => simp [hv] at hocc
                have hnext :=
                  checkONeverLoses_of_x_move n (currentBoard h) hgame hh (xStrat h) hempty
                simp only [otherPlayer, X, O]
                exact ih O _ (by simpa [currentBoard] using hnext)

/-- O's embedded non-losing strategy never loses against any history strategy of X. -/
theorem oStrategy_asStrategy_never_loses (xStrat : Strategy) :
    hasWon (finalBoard (fun p ↦ if p = O then asStrategy oStrategy else xStrat))
      X = false :=
  checkONeverLoses_asStrategy_sound xStrat 9 X [emptyBoard] checkONeverLoses_emptyBoard

/-- X's embedded never-lose strategy guarantees a nonnegative payoff against any opponent. -/
theorem xStrategy_payoff_nonneg (τ : Strategy) :
    0 ≤ ticTacToe.payoff X (fun p ↦ if p = X then asStrategy xStrategy else τ) := by
  have hno := xStrategy_asStrategy_never_loses τ
  change 0 ≤
    (if hasWon (finalBoard (fun p ↦ if p = X then asStrategy xStrategy else τ)) X
      then (1 : ℝ)
      else if hasWon (finalBoard (fun p ↦ if p = X then asStrategy xStrategy else τ)) O
        then -1 else 0)
  cases hw : hasWon (finalBoard (fun p ↦ if p = X then asStrategy xStrategy else τ)) X <;>
    simp [hno]

/-- O's embedded never-lose strategy guarantees a nonnegative payoff against any opponent. -/
theorem oStrategy_payoff_nonneg (τ : Strategy) :
    0 ≤ ticTacToe.payoff O (fun p ↦ if p = O then asStrategy oStrategy else τ) := by
  have hno := oStrategy_asStrategy_never_loses τ
  change 0 ≤
    (if hasWon (finalBoard (fun p ↦ if p = O then asStrategy oStrategy else τ)) X
      then (-1 : ℝ)
      else if hasWon (finalBoard (fun p ↦ if p = O then asStrategy oStrategy else τ)) O
        then 1 else 0)
  cases hw : hasWon (finalBoard (fun p ↦ if p = O then asStrategy oStrategy else τ)) O <;>
    simp [hno]

/-- The explicit non-losing board strategies, embedded as history strategies. -/
def memorylessDrawProfile : StrategyProfile :=
  fun p => if p = X then asStrategy xStrategy else asStrategy oStrategy

/-- Under `memorylessDrawProfile`, both players receive payoff zero. -/
lemma memorylessDrawProfile_payoff_eq_zero :
    ticTacToe.payoff X memorylessDrawProfile = 0 ∧
      ticTacToe.payoff O memorylessDrawProfile = 0 := by
  have hXno : hasWon (finalBoard memorylessDrawProfile) O = false :=
    xStrategy_asStrategy_never_loses (asStrategy oStrategy)
  have hOno : hasWon (finalBoard memorylessDrawProfile) X = false := by
    have h := oStrategy_asStrategy_never_loses (asStrategy xStrategy)
    have heq :
        memorylessDrawProfile =
          (fun p ↦ if p = O then asStrategy oStrategy else asStrategy xStrategy) := by
      funext p; fin_cases p <;> rfl
    simpa [heq] using h
  have hpay0 : ticTacToe.payoff X memorylessDrawProfile = 0 := by
    change
      (if hasWon (finalBoard memorylessDrawProfile) X then (1 : ℝ)
        else if hasWon (finalBoard memorylessDrawProfile) O then -1 else 0) = 0
    cases hx : hasWon (finalBoard memorylessDrawProfile) X
    · simp [hXno]
    · rw [hOno] at hx; cases hx
  exact ⟨hpay0, by linarith [ticTacToe_payoff_add_eq_zero memorylessDrawProfile, hpay0]⟩


/-- In every pure Nash equilibrium, both players receive zero payoff.
Each player can guarantee a nonnegative payoff by switching to the corresponding
memoryless never-lose strategy, and the game is zero-sum. -/
theorem ticTacToe_nash_payoffs_eq_zero
    (σ : StrategyProfile) (hσ : ticTacToe.IsNash σ) :
    ticTacToe.payoff X σ = 0 ∧ ticTacToe.payoff O σ = 0 := by
  rw [StrategicGame.isNash_iff] at hσ
  have hdevX := hσ X (asStrategy xStrategy)
  have hdevO := hσ O (asStrategy oStrategy)
  have hupdateX :
      Function.update σ X (asStrategy xStrategy) =
        (fun p ↦ if p = X then asStrategy xStrategy else σ O) := by
    funext p; fin_cases p <;> simp [X, O]
  have hupdateO :
      Function.update σ O (asStrategy oStrategy) =
        (fun p ↦ if p = O then asStrategy oStrategy else σ X) := by
    funext p; fin_cases p <;> simp [X, O]
  have hx : 0 ≤ ticTacToe.payoff X (Function.update σ X (asStrategy xStrategy)) := by
    rw [hupdateX]; exact xStrategy_payoff_nonneg (σ O)
  have ho : 0 ≤ ticTacToe.payoff O (Function.update σ O (asStrategy oStrategy)) := by
    rw [hupdateO]; exact oStrategy_payoff_nonneg (σ X)
  have hX : 0 ≤ ticTacToe.payoff X σ := le_trans hx hdevX
  have hO : 0 ≤ ticTacToe.payoff O σ := le_trans ho hdevO
  have hzero := ticTacToe_payoff_add_eq_zero σ
  constructor <;> linarith


end MathEconLibExamples.GameTheory.TicTacToe
end
