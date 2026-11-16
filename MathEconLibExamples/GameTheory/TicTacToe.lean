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

Board-dependent (memoryless) policies embed into history policies via `asStrategy`; they forget
move order, so distinct legal histories can share a board. Their non-loss certificates are
proved from `emptyBoard` against every opposing policy. Exhaustive Boolean checkers explore
every legal opposing move, and soundness theorems connect those checks to both the board and
history simulators. Against a memoryless opponent any history strategy can be path-simulated by
a board strategy with equal payoff, so the memoryless draw profile is Nash even when deviations
may depend on history. Every pure Nash equilibrium has payoff zero for both players, since each
can secure a draw by switching to the corresponding memoryless never-lose strategy.

## Main definitions

* `Board`, `MemorylessStrategy`, `MemorylessStrategyProfile`, `Strategy`, `StrategyProfile`:
  Board and strategy types.
* `playAccordingToStrategy`: Bounded simulation of a history-strategy profile.
* `ticTacToe`: The strategic game with win/loss/draw payoffs of `1`, `-1`, and `0`.
* `asStrategy`, `toMemoryless`, `simulateMemorylessX/O`: Memoryless embedding, projection,
  and path-simulation against a memoryless opponent.
* `xStrategy`, `oStrategy`, `memorylessDrawProfile`: Explicit non-losing strategies.

## Verification

* `checkXNeverLoses`, `checkONeverLoses`: Exhaustive checks against all legal opponent moves.
* `xStrategy_asStrategy_never_loses`, `oStrategy_asStrategy_never_loses`: Non-loss in history play.
* `xStrategy_payoff_nonneg`, `oStrategy_payoff_nonneg`: Nonnegative payoffs for the
  embedded strategies.
* `ticTacToe_payoff_add_eq_zero`: The game's payoff sum is zero.

## Main results

* `memorylessDrawProfile_isNash_among_memoryless`: No memoryless deviation is profitable.
* `memorylessDrawProfile_isNash`: The profile remains Nash against history deviations (via
  path-simulation).
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

/-- The length-`n` prefix of a history. -/
def historyPrefix (h : History) (n : Nat) : History :=
  h.take n

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

/-- All legal history prefixes in which player `p` follows strategy `σ`. -/
def historiesFollowing (p : Player) (σ : Strategy) :
    Nat → Player → History → List History
  | 0, _, h => [h]
  | n + 1, turn, h =>
    let b := currentBoard h
    if gameOver b then [h]
    else if turn = p then
      let pos := σ h
      if (b pos).isSome then [h]
      else
        h :: historiesFollowing p σ n (otherPlayer turn)
          (h ++ [Function.update b pos (some turn)])
    else
      h :: (List.finRange 3).flatMap (fun i =>
        (List.finRange 3).flatMap (fun j =>
          let pos : Position := (i, j)
          if (b pos).isSome then []
          else
            historiesFollowing p σ n (otherPlayer turn)
              (h ++ [Function.update b pos (some turn)])))

/-- Cell encoding used by `boardCode`. -/
def cellCode : Option Player → Nat
  | none => 0
  | some p => p.val + 1

/-- Distinct cells receive distinct codes. -/
lemma cellCode_injective : Function.Injective cellCode := by
  intro x y h
  cases x with
  | none =>
      cases y with
      | none => rfl
      | some q => simp [cellCode] at h
  | some p =>
      cases y with
      | none => simp [cellCode] at h
      | some q =>
          refine congrArg some (Fin.ext ?_)
          simpa [cellCode] using h

/-- Encode a board as nine numbers in row-major order:
0 = empty, 1 = X, 2 = O. -/
def boardCode (b : Board) : List Nat :=
  (List.finRange 3).flatMap fun i =>
    (List.finRange 3).map fun j =>
      cellCode (b (i, j))

/-- A board code always has length nine. -/
lemma boardCode_length (b : Board) : (boardCode b).length = 9 := by
  simp [boardCode]

private lemma boardCode_get (b : Board) (i j : Fin 3) :
    (boardCode b)[i.val * 3 + j.val]'(by have := boardCode_length b; omega) =
      cellCode (b (i, j)) := by
  simp only [boardCode]
  fin_cases i <;> fin_cases j <;> simp [List.finRange]


/-- The lexicographic encoding of a history of boards. -/
def historyCode (h : History) : List (List Nat) :=
  h.map boardCode

/-- Computational lexicographic comparison of histories. -/
def historyLt (h₁ h₂ : History) : Bool :=
  compare (historyCode h₁) (historyCode h₂) == .lt

/-- One step of the lex-min fold used by `smallestCompatibleHistory?`. -/
def historyMinStep (acc : Option History) (h' : History) : Option History :=
  match acc with
  | none => some h'
  | some best => some (if historyLt h' best then h' else best)

/-- The lexicographically smallest legal history reaching the same board,
in which player `p` follows strategy `σ`. -/
def smallestCompatibleHistory?
    (p : Player) (σ : Strategy) (h : History) : Option History :=
  let target := boardCode (currentBoard h)
  let candidates :=
    (historiesFollowing p σ 9 X [emptyBoard]).filter
      (fun h' => boardCode (currentBoard h') == target)
  candidates.foldl historyMinStep none

/-- A memoryless strategy obtained from a history-dependent strategy. -/
def toMemorylessStrategy (p : Player) (σ : Strategy) : MemorylessStrategy :=
  fun b =>
    match smallestCompatibleHistory? p σ [b] with
    | some h => σ h
    | none => (0, 0)

/-- View a board-dependent strategy as a history strategy that ignores the path. -/
def asStrategy (s : MemorylessStrategy) : Strategy :=
  fun h => s (currentBoard h)

/-- The history-strategy profile that plays the memoryless projection of each
player's strategy at the current board. -/
def toMemoryless (σ : StrategyProfile) : StrategyProfile :=
  fun p => asStrategy (toMemorylessStrategy p (σ p))

/-- Replace a single player's strategy by its memoryless projection. -/
def toMemorylessOne (σ : StrategyProfile) (i : Player) : StrategyProfile :=
  Function.update σ i (asStrategy (toMemorylessStrategy i (σ i)))

/-- X's strategy guarantees nonnegative payoff against every opposing history strategy. -/
def IsSecurityX (σ : Strategy) : Prop :=
  ∀ τ : Strategy,
    0 ≤ ticTacToe.payoff X (fun p ↦ if p = X then σ else τ)

/-- O's strategy guarantees nonnegative payoff against every opposing history strategy. -/
def IsSecurityO (σ : Strategy) : Prop :=
  ∀ τ : Strategy,
    0 ≤ ticTacToe.payoff O (fun p ↦ if p = O then σ else τ)

/-- Under memoryless strategies, history play depends only on the current board. -/
lemma play_asStrategy_eq_playAccordingToMemorylessStrategyProfile
    (σ : MemorylessStrategyProfile) (n : Nat) (p : Player) (h : History) :
    currentBoard (playAccordingToStrategy (fun q => asStrategy (σ q)) n p h) =
      playAccordingToMemorylessStrategyProfile σ n p (currentBoard h) := by
  induction n generalizing p h with
  | zero =>
      rfl
  | succ n ih =>
      cases hgame : gameOver (currentBoard h) with
      | true =>
          simp [playAccordingToStrategy, playAccordingToMemorylessStrategyProfile, hgame]
      | false =>
          cases hocc : ((currentBoard h) (σ p (currentBoard h))).isSome with
          | true =>
              simp [playAccordingToStrategy, playAccordingToMemorylessStrategyProfile,
                asStrategy, hgame, hocc, currentBoard]
          | false =>
              simp only [playAccordingToStrategy, playAccordingToMemorylessStrategyProfile,
                asStrategy, hgame, hocc]
              exact (ih (otherPlayer p) _).trans (by simp [currentBoard])

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

/-- A successful X checker implies that actual play against any O strategy
cannot end with O winning, provided X uses `xStrategy`. -/
private theorem checkXNeverLoses_sound
    (σ : MemorylessStrategyProfile) (hX : σ X = xStrategy) :
    ∀ n p b, checkXNeverLoses n p b = true →
      hasWon (playAccordingToMemorylessStrategyProfile σ n p b) O = false := by
  intro n
  induction n with
  | zero =>
      intro p b h
      cases hw : hasWon b O <;>
        simp_all [checkXNeverLoses, playAccordingToMemorylessStrategyProfile]
  | succ n ih =>
      intro p b h
      cases hgame : gameOver b with
      | true =>
          cases hw : hasWon b O <;>
            simp_all [checkXNeverLoses, playAccordingToMemorylessStrategyProfile]
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
                    playAccordingToMemorylessStrategyProfile σ (n + 1) X b =
                      playAccordingToMemorylessStrategyProfile σ n O
                        (Function.update b (xStrategy b) (some X)) := by
                  simp [playAccordingToMemorylessStrategyProfile, hgame, hX, hocc,
                    otherPlayer, X, O]
                rw [hplay]
                exact ih O _ hnext
          · have hpO : p = O := by
              fin_cases p <;> simp_all [X, O]
            subst p
            let pos := σ O b
            cases hocc : (b pos).isSome with
            | true =>
                have hplay :
                    playAccordingToMemorylessStrategyProfile σ (n + 1) O b =
                      xWinningBoard := by
                  simp [playAccordingToMemorylessStrategyProfile, hgame, pos, hocc, X, O]
                rw [hplay]
                decide +kernel
            | false =>
                have hempty : (b pos).isNone = true := by
                  cases hv : b pos with
                  | none => simp []
                  | some _ => simp [hv] at hocc
                have hnext := checkXNeverLoses_of_o_move n b hgame h pos hempty
                have hplay :
                    playAccordingToMemorylessStrategyProfile σ (n + 1) O b =
                      playAccordingToMemorylessStrategyProfile σ n X
                        (Function.update b pos (some O)) := by
                  simp [playAccordingToMemorylessStrategyProfile, hgame, pos, hocc,
                    otherPlayer, X, O]
                rw [hplay]
                exact ih X _ hnext

/-- X cannot lose from the empty board when following `xStrategy`,
against any deterministic O strategy. -/
theorem xStrategy_never_loses (oStrategy : MemorylessStrategy) :
    hasWon
      (playAccordingToMemorylessStrategyProfile
        (fun p ↦ if p = X then xStrategy else oStrategy)
        9 X emptyBoard)
      O = false := by
  let σ : MemorylessStrategyProfile := fun p ↦ if p = X then xStrategy else oStrategy
  have hX : σ X = xStrategy := by simp [σ]
  exact checkXNeverLoses_sound σ hX 9 X emptyBoard checkXNeverLoses_emptyBoard

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
    (σ : MemorylessStrategyProfile) (hO : σ O = oStrategy) :
    ∀ n p b, checkONeverLoses n p b = true →
      hasWon (playAccordingToMemorylessStrategyProfile σ n p b) X = false := by
  intro n
  induction n with
  | zero =>
      intro p b h
      cases hw : hasWon b X <;>
        simp_all [checkONeverLoses, playAccordingToMemorylessStrategyProfile]
  | succ n ih =>
      intro p b h
      cases hgame : gameOver b with
      | true =>
          cases hw : hasWon b X <;>
        simp_all [checkONeverLoses, playAccordingToMemorylessStrategyProfile]
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
                    playAccordingToMemorylessStrategyProfile σ (n + 1) O b =
                      playAccordingToMemorylessStrategyProfile σ n X
                        (Function.update b (oStrategy b) (some O)) := by
                  simp [playAccordingToMemorylessStrategyProfile, hgame, hO, hocc,
                    otherPlayer, X, O]
                rw [hplay]
                exact ih X _ hnext
          · have hpX : p = X := by
              fin_cases p <;> simp_all [X, O]
            subst p
            let pos := σ X b
            cases hocc : (b pos).isSome with
            | true =>
                have hplay :
                    playAccordingToMemorylessStrategyProfile σ (n + 1) X b =
                      oWinningBoard := by
                  simp [playAccordingToMemorylessStrategyProfile, hgame, pos, hocc, X]
                rw [hplay]
                decide +kernel
            | false =>
                have hempty : (b pos).isNone = true := by
                  cases hv : b pos with
                  | none => simp []
                  | some _ => simp [hv] at hocc
                have hnext := checkONeverLoses_of_x_move n b hgame h pos hempty
                have hplay :
                    playAccordingToMemorylessStrategyProfile σ (n + 1) X b =
                      playAccordingToMemorylessStrategyProfile σ n O
                        (Function.update b pos (some X)) := by
                  simp [playAccordingToMemorylessStrategyProfile, hgame, pos, hocc,
                    otherPlayer, X, O]
                rw [hplay]
                exact ih O _ hnext

/-- O cannot lose from the empty board when following `oStrategy`,
against any deterministic X strategy. -/
theorem oStrategy_never_loses (xStrat : MemorylessStrategy) :
    hasWon
      (playAccordingToMemorylessStrategyProfile
        (fun p ↦ if p = O then oStrategy else xStrat)
        9 X emptyBoard)
      X = false := by
  let σ : MemorylessStrategyProfile := fun p ↦ if p = O then oStrategy else xStrat
  have hO : σ O = oStrategy := by simp [σ, O]
  exact checkONeverLoses_sound σ hO 9 X emptyBoard checkONeverLoses_emptyBoard

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

/-- `boardCode` determines the board. -/
lemma boardCode_injective : Function.Injective boardCode := by
  intro b₁ b₂ heq
  funext pos
  obtain ⟨i, j⟩ := pos
  apply cellCode_injective
  calc
    cellCode (b₁ (i, j)) =
        (boardCode b₁)[i.val * 3 + j.val]'(by have := boardCode_length b₁; omega) :=
      (boardCode_get b₁ i j).symm
    _ = (boardCode b₂)[i.val * 3 + j.val]'(by have := boardCode_length b₂; omega) := by
        simp [heq]
    _ = cellCode (b₂ (i, j)) := boardCode_get b₂ i j

/-- Number of empty squares of a board. -/
def emptyCount (b : Board) : Nat :=
  (Finset.univ.filter fun pos : Position => (b pos).isNone = true).card

/-- The empty board has nine empty squares. -/
lemma emptyCount_empty : emptyCount emptyBoard = 9 := by
  decide +kernel

/-- Filling an empty square decreases `emptyCount` by one. -/
lemma emptyCount_update (b : Board) (pos : Position) (t : Player)
    (h : (b pos).isNone = true) :
    emptyCount (Function.update b pos (some t)) + 1 = emptyCount b := by
  unfold emptyCount
  have hset : (Finset.univ.filter fun q : Position =>
      (Function.update b pos (some t) q).isNone = true) =
      (Finset.univ.filter fun q : Position => (b q).isNone = true).erase pos := by
    ext q
    by_cases hq : q = pos
    · subst hq; simp
    · simp [hq]
  rw [hset, Finset.card_erase_add_one]
  simpa using h

/-- A non-terminal board still has at least one empty square. -/
lemma emptyCount_pos {b : Board} (h : gameOver b = false) : 1 ≤ emptyCount b := by
  by_contra hlt
  have h0 : emptyCount b = 0 := by omega
  unfold emptyCount at h0
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
  have hfull : boardFull b = true := by
    simp only [boardFull, List.all_eq_true, List.mem_finRange, true_implies]
    intro i j
    have := h0 (Finset.mem_univ (i, j))
    cases hb : b (i, j) <;> simp_all
  simp [gameOver, hfull] at h

/-!
## Memoryless simulation of history strategies

Against a memoryless opponent the play path is unique, so any history-dependent
reply can be copied by a board strategy that, at each board on that path, plays
whatever the history strategy played on the unique prefix ending there. Hence a
profitable history deviation against a memoryless profile yields a profitable
memoryless deviation as well.
-/

/-- The history produced by playing `σx` against memoryless `so`. -/
def playHistoryVsMemorylessO (σx : Strategy) (so : MemorylessStrategy) : History :=
  playAccordingToStrategy
    (fun p ↦ if p = X then σx else asStrategy so) 9 X [emptyBoard]

/-- The history produced by playing `σo` against memoryless `sx`. -/
def playHistoryVsMemorylessX (σo : Strategy) (sx : MemorylessStrategy) : History :=
  playAccordingToStrategy
    (fun p ↦ if p = O then σo else asStrategy sx) 9 X [emptyBoard]

/-- Shortest nonempty prefix of `hs` whose current board matches `b` (by `boardCode`). -/
def prefixEndingAt (hs : History) (b : Board) : Option History :=
  (List.range hs.length).findSome? fun i =>
    let h := hs.take (i + 1)
    if boardCode (currentBoard h) == boardCode b then some h else none

/-- Memoryless strategy copying `σx` along its unique path against memoryless `so`. -/
noncomputable def simulateMemorylessX (σx : Strategy) (so : MemorylessStrategy) :
    MemorylessStrategy :=
  fun b =>
    match prefixEndingAt (playHistoryVsMemorylessO σx so) b with
    | some h => σx h
    | none => (0, 0)

/-- Memoryless strategy copying `σo` along its unique path against memoryless `sx`. -/
noncomputable def simulateMemorylessO (σo : Strategy) (sx : MemorylessStrategy) :
    MemorylessStrategy :=
  fun b =>
    match prefixEndingAt (playHistoryVsMemorylessX σo sx) b with
    | some h => σo h
    | none => (0, 0)

/-- Along a play, the boards have strictly decreasing numbers of empty squares. -/
private def StrictPlay (h : History) : Prop :=
  h ≠ [] ∧ h.Pairwise (fun a b => emptyCount b < emptyCount a) ∧
    ∀ a ∈ h, emptyCount (currentBoard h) ≤ emptyCount a

private lemma StrictPlay.snoc {h : History} (hs : StrictPlay h) {b : Board}
    (hb : emptyCount b < emptyCount (currentBoard h)) : StrictPlay (h ++ [b]) := by
  obtain ⟨hne, hpw, hmin⟩ := hs
  have hcur : currentBoard (h ++ [b]) = b := by simp [currentBoard]
  refine ⟨by simp, ?_, ?_⟩
  · rw [List.pairwise_append]
    refine ⟨hpw, by simp, ?_⟩
    intro a ha c hc
    simp only [List.mem_singleton] at hc
    subst hc
    exact lt_of_lt_of_le hb (hmin a ha)
  · intro a ha
    rw [hcur]
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact le_of_lt (lt_of_lt_of_le hb (hmin a ha))
    · exact le_rfl

private lemma emptyCount_sentinel (p : Player) :
    emptyCount (if p = X then oWinningBoard else xWinningBoard) = 0 := by
  split_ifs <;> simp [emptyCount]

private lemma emptyCount_update_lt {b : Board} {pos : Position} {t : Player}
    (hocc : ¬ (b pos).isSome = true) :
    emptyCount (Function.update b pos (some t)) < emptyCount b := by
  have hnone : (b pos).isNone = true := by
    cases hb : b pos <;> simp_all
  have := emptyCount_update b pos t hnone
  omega

private lemma play_strictPlay (σ : StrategyProfile) :
    ∀ (n : Nat) (turn : Player) (h : History), StrictPlay h →
      StrictPlay (playAccordingToStrategy σ n turn h) := by
  intro n
  induction n with
  | zero =>
      intro turn h hs
      simpa [playAccordingToStrategy] using hs
  | succ n ih =>
      intro turn h hs
      by_cases hg : gameOver (currentBoard h) = true
      · simpa [playAccordingToStrategy, hg] using hs
      · have hg' : gameOver (currentBoard h) = false := by simpa using hg
        have hpos := emptyCount_pos hg'
        simp only [playAccordingToStrategy, hg]
        by_cases hocc : (currentBoard h (σ turn h)).isSome = true
        · simp only [hocc]
          apply hs.snoc
          rw [emptyCount_sentinel]
          omega
        · simp only [hocc]
          exact ih _ _ (hs.snoc (emptyCount_update_lt hocc))

private lemma prefix_play (σ : StrategyProfile) :
    ∀ (n : Nat) (turn : Player) (h : History),
      h.IsPrefix (playAccordingToStrategy σ n turn h) := by
  intro n
  induction n with
  | zero => intro turn h; exact List.prefix_refl _
  | succ n ih =>
      intro turn h
      simp only [playAccordingToStrategy]
      split_ifs <;>
        first
        | exact List.prefix_refl _
        | exact List.prefix_append _ _
        | exact (List.prefix_append _ _).trans (ih _ _)

private lemma currentBoard_take_succ (hs : History) (i : Nat) (hi : i < hs.length) :
    currentBoard (hs.take (i + 1)) = hs[i] := by
  simp [currentBoard, List.getLast?_take, hi]

private lemma findSome?_range_of {α : Type} (f : Nat → Option α) (L m : Nat) (r : α)
    (hm : m < L) (hf : f m = some r) (hlt : ∀ i < m, f i = none) :
    (List.range L).findSome? f = some r := by
  rw [List.findSome?_eq_some_iff]
  refine ⟨(List.range L).take m, m, (List.range L).drop (m + 1), ?_, hf, ?_⟩
  · have hm' : m < (List.range L).length := by simpa using hm
    conv_lhs => rw [← List.take_append_drop m (List.range L)]
    rw [List.drop_eq_getElem_cons hm']
    simp
  · intro x hx
    have hx' : x ∈ List.range m := by
      have : (List.range L).take m = List.range m := by
        rw [List.take_range]; congr 1; omega
      rwa [this] at hx
    exact hlt x (List.mem_range.mp hx')

/-- In a strictly decreasing play, a nonempty prefix is found by `prefixEndingAt`. -/
private lemma prefixEndingAt_of_pairwise
    (hs h : History) (hpw : hs.Pairwise (fun a b => emptyCount b < emptyCount a))
    (hp : h.IsPrefix hs) (hne : h ≠ []) :
    prefixEndingAt hs (currentBoard h) = some h := by
  have hlen : h.length ≤ hs.length := hp.length_le
  have hpos : 0 < h.length := List.length_pos_of_ne_nil hne
  have htake : hs.take h.length = h := (List.prefix_iff_eq_take.mp hp).symm
  obtain ⟨m, hm⟩ : ∃ m, h.length = m + 1 := ⟨h.length - 1, by omega⟩
  have hmlt : m < hs.length := by omega
  have hcur : currentBoard h = hs[m] := by
    rw [← htake, hm]
    exact currentBoard_take_succ hs m hmlt
  unfold prefixEndingAt
  apply findSome?_range_of _ hs.length m h hmlt
  · rw [← hm, htake]
    simp
  · intro i hi
    have hi' : i < hs.length := by omega
    have hbeq : (boardCode (currentBoard (hs.take (i + 1))) == boardCode (currentBoard h)) =
        false := by
      rw [currentBoard_take_succ hs i hi', hcur, beq_eq_false_iff_ne]
      intro hcode
      have heq := boardCode_injective hcode
      have hlt : emptyCount hs[m] < emptyCount hs[i] :=
        List.pairwise_iff_getElem.mp hpw i m hi' hmlt hi
      rw [heq] at hlt
      exact lt_irrefl _ hlt
    simp [hbeq]

/-- Generic path-simulation lemma: if the memoryless `s'` agrees with `σme` along every
nonempty prefix of the full play, then replacing `σme` by `s'` does not change the play. -/
private lemma play_sim_eq (me : Player) (σme : Strategy) (other s' : MemorylessStrategy)
    (full : History)
    (key : ∀ h', h'.IsPrefix full → h' ≠ [] → s' (currentBoard h') = σme h') :
    ∀ (n : Nat) (turn : Player) (h : History) (m : Nat), n ≤ m → h ≠ [] →
      full = playAccordingToStrategy
        (fun q ↦ if q = me then σme else asStrategy other) m turn h →
      playAccordingToStrategy
          (fun q ↦ if q = me then asStrategy s' else asStrategy other)
          n turn h =
        playAccordingToStrategy
          (fun q ↦ if q = me then σme else asStrategy other) n turn h := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
      intro turn h m hnm hne hfull
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      by_cases hg : gameOver (currentBoard h) = true
      · simp [playAccordingToStrategy, hg]
      · have hpref : h.IsPrefix full := by
          rw [hfull]; exact prefix_play _ _ _ _
        have hpos :
            (if turn = me then asStrategy s' else asStrategy other) h =
            (if turn = me then σme else asStrategy other) h := by
          by_cases ht : turn = me
          · subst ht
            simpa [asStrategy] using key h hpref hne
          · simp [ht]
        simp only [playAccordingToStrategy, hg]
        rw [hpos]
        by_cases hocc : (currentBoard h
            ((if turn = me then σme else asStrategy other) h)).isSome = true
        · simp [hocc]
        · simp only [hocc]
          apply ih _ _ m' (by omega) (by simp)
          simpa [playAccordingToStrategy, hg, hocc] using hfull

/-- Against memoryless O, the path-simulation of `σx` yields the same final board. -/
lemma finalBoard_simulateMemorylessX (σx : Strategy) (so : MemorylessStrategy) :
    finalBoard (fun p ↦ if p = X then asStrategy (simulateMemorylessX σx so)
      else asStrategy so) =
      finalBoard (fun p ↦ if p = X then σx else asStrategy so) := by
  have hstrict := play_strictPlay
    (fun p ↦ if p = X then σx else asStrategy so) 9 X [emptyBoard]
    ⟨by simp, by simp, fun a ha ↦ by
      rw [List.mem_singleton.mp ha]; exact le_rfl⟩
  have hpw : (playHistoryVsMemorylessO σx so).Pairwise
      (fun a b => emptyCount b < emptyCount a) := hstrict.2.1
  have key : ∀ h', h'.IsPrefix (playHistoryVsMemorylessO σx so) → h' ≠ [] →
      simulateMemorylessX σx so (currentBoard h') = σx h' := by
    intro h' hp hne
    unfold simulateMemorylessX
    rw [prefixEndingAt_of_pairwise _ h' hpw hp hne]
  unfold finalBoard
  rw [play_sim_eq X σx so (simulateMemorylessX σx so) (playHistoryVsMemorylessO σx so) key
    9 X [emptyBoard] 9 le_rfl (by simp) rfl]

/-- Against memoryless X, the path-simulation of `σo` yields the same final board. -/
lemma finalBoard_simulateMemorylessO (σo : Strategy) (sx : MemorylessStrategy) :
    finalBoard (fun p ↦ if p = O then asStrategy (simulateMemorylessO σo sx)
      else asStrategy sx) =
      finalBoard (fun p ↦ if p = O then σo else asStrategy sx) := by
  have hstrict := play_strictPlay
    (fun p ↦ if p = O then σo else asStrategy sx) 9 X [emptyBoard]
    ⟨by simp, by simp, fun a ha ↦ by
      rw [List.mem_singleton.mp ha]; exact le_rfl⟩
  have hpw : (playHistoryVsMemorylessX σo sx).Pairwise
      (fun a b => emptyCount b < emptyCount a) := hstrict.2.1
  have key : ∀ h', h'.IsPrefix (playHistoryVsMemorylessX σo sx) → h' ≠ [] →
      simulateMemorylessO σo sx (currentBoard h') = σo h' := by
    intro h' hp hne
    unfold simulateMemorylessO
    rw [prefixEndingAt_of_pairwise _ h' hpw hp hne]
  unfold finalBoard
  rw [play_sim_eq O σo sx (simulateMemorylessO σo sx) (playHistoryVsMemorylessX σo sx) key
    9 X [emptyBoard] 9 le_rfl (by simp) rfl]

/-- Path-simulation preserves X's payoff against a memoryless opponent. -/
lemma payoffX_simulateMemorylessX (σx : Strategy) (so : MemorylessStrategy) :
    ticTacToe.payoff X
        (fun p ↦ if p = X then asStrategy (simulateMemorylessX σx so)
          else asStrategy so) =
      ticTacToe.payoff X
        (fun p ↦ if p = X then σx else asStrategy so) := by
  simp_rw [finalBoard_simulateMemorylessX]

/-- Path-simulation preserves O's payoff against a memoryless opponent. -/
lemma payoffO_simulateMemorylessO (σo : Strategy) (sx : MemorylessStrategy) :
    ticTacToe.payoff O
        (fun p ↦ if p = O then asStrategy (simulateMemorylessO σo sx)
          else asStrategy sx) =
      ticTacToe.payoff O
        (fun p ↦ if p = O then σo else asStrategy sx) := by
  simp_rw [finalBoard_simulateMemorylessO]

/-!
## Memoryless Nash equilibrium
-/

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

/-- No memoryless deviation improves on `memorylessDrawProfile`. -/
theorem memorylessDrawProfile_isNash_among_memoryless :
    (∀ sx : MemorylessStrategy,
        ticTacToe.payoff X
            (fun p ↦ if p = X then asStrategy sx else asStrategy oStrategy) ≤
          ticTacToe.payoff X memorylessDrawProfile) ∧
      ∀ so : MemorylessStrategy,
        ticTacToe.payoff O
            (fun p ↦ if p = O then asStrategy so else asStrategy xStrategy) ≤
          ticTacToe.payoff O memorylessDrawProfile := by
  refine ⟨?_, ?_⟩
  · intro sx
    rw [(memorylessDrawProfile_payoff_eq_zero).1]
    have hno := oStrategy_never_loses sx
    have hplay :
        finalBoard (fun p ↦ if p = X then asStrategy sx else asStrategy oStrategy) =
          playAccordingToMemorylessStrategyProfile
            (fun p ↦ if p = O then oStrategy else sx) 9 X emptyBoard := by
      have hprof :
          (fun p ↦ if p = X then asStrategy sx else asStrategy oStrategy) =
            (fun q ↦ asStrategy (if q = O then oStrategy else sx)) := by
        funext q; fin_cases q <;> simp [X, O]
      rw [hprof]
      simpa [finalBoard, currentBoard] using
        (play_asStrategy_eq_playAccordingToMemorylessStrategyProfile
          (fun p ↦ if p = O then oStrategy else sx) 9 X [emptyBoard])
    change
      (if hasWon (finalBoard
            (fun p ↦ if p = X then asStrategy sx else asStrategy oStrategy)) X
        then (1 : ℝ)
        else if hasWon (finalBoard
            (fun p ↦ if p = X then asStrategy sx else asStrategy oStrategy)) O
          then -1 else 0) ≤ 0
    rw [hplay]
    cases hx : hasWon (playAccordingToMemorylessStrategyProfile
        (fun p ↦ if p = O then oStrategy else sx) 9 X emptyBoard) X
    · cases ho : hasWon (playAccordingToMemorylessStrategyProfile
          (fun p ↦ if p = O then oStrategy else sx) 9 X emptyBoard) O <;> simp
    · have : hasWon (playAccordingToMemorylessStrategyProfile
          (fun p ↦ if p = O then oStrategy else sx) 9 X emptyBoard) X = false := hno
      simp [this] at hx
  · intro so
    rw [(memorylessDrawProfile_payoff_eq_zero).2]
    have hno := xStrategy_never_loses so
    have hplay :
        finalBoard (fun p ↦ if p = O then asStrategy so else asStrategy xStrategy) =
          playAccordingToMemorylessStrategyProfile
            (fun p ↦ if p = X then xStrategy else so) 9 X emptyBoard := by
      have hprof :
          (fun p ↦ if p = O then asStrategy so else asStrategy xStrategy) =
            (fun q ↦ asStrategy (if q = X then xStrategy else so)) := by
        funext q; fin_cases q <;> simp [X, O]
      rw [hprof]
      simpa [finalBoard, currentBoard] using
        (play_asStrategy_eq_playAccordingToMemorylessStrategyProfile
          (fun p ↦ if p = X then xStrategy else so) 9 X [emptyBoard])
    change
      (if hasWon (finalBoard
            (fun p ↦ if p = O then asStrategy so else asStrategy xStrategy)) X
        then (-1 : ℝ)
        else if hasWon (finalBoard
            (fun p ↦ if p = O then asStrategy so else asStrategy xStrategy)) O
          then 1 else 0) ≤ 0
    rw [hplay]
    cases ho : hasWon (playAccordingToMemorylessStrategyProfile
        (fun p ↦ if p = X then xStrategy else so) 9 X emptyBoard) O
    · cases hx : hasWon (playAccordingToMemorylessStrategyProfile
          (fun p ↦ if p = X then xStrategy else so) 9 X emptyBoard) X <;> simp
    · have : hasWon (playAccordingToMemorylessStrategyProfile
          (fun p ↦ if p = X then xStrategy else so) 9 X emptyBoard) O = false := hno
      simp [this] at ho

/-- The embedded non-losing profile is a pure Nash equilibrium in the full
history-strategy game: any profitable history deviation would yield, via
path-simulation, a profitable memoryless deviation, contradicting
`memorylessDrawProfile_isNash_among_memoryless`. -/
theorem memorylessDrawProfile_isNash : ticTacToe.IsNash memorylessDrawProfile := by
  rw [StrategicGame.isNash_iff]
  intro i s
  have hpay0 := memorylessDrawProfile_payoff_eq_zero
  fin_cases i
  · change ticTacToe.payoff X (Function.update memorylessDrawProfile X s) ≤
      ticTacToe.payoff X memorylessDrawProfile
    have hupd :
        Function.update memorylessDrawProfile X s =
          (fun p ↦ if p = X then s else asStrategy oStrategy) := by
      funext p; fin_cases p <;> simp [memorylessDrawProfile, X]
    rw [hupd, hpay0.1]
    have hsim := payoffX_simulateMemorylessX s oStrategy
    have hmem := (memorylessDrawProfile_isNash_among_memoryless).1
      (simulateMemorylessX s oStrategy)
    rw [hpay0.1] at hmem
    calc
      ticTacToe.payoff X (fun p ↦ if p = X then s else asStrategy oStrategy)
          = ticTacToe.payoff X (fun p ↦ if p = X then
              asStrategy (simulateMemorylessX s oStrategy)
              else asStrategy oStrategy) := hsim.symm
      _ ≤ 0 := hmem
  · change ticTacToe.payoff O (Function.update memorylessDrawProfile O s) ≤
      ticTacToe.payoff O memorylessDrawProfile
    have hupd :
        Function.update memorylessDrawProfile O s =
          (fun p ↦ if p = O then s else asStrategy xStrategy) := by
      funext p; fin_cases p <;> simp [memorylessDrawProfile, X, O]
    rw [hupd, hpay0.2]
    have hsim := payoffO_simulateMemorylessO s xStrategy
    have hmem := (memorylessDrawProfile_isNash_among_memoryless).2
      (simulateMemorylessO s xStrategy)
    rw [hpay0.2] at hmem
    calc
      ticTacToe.payoff O (fun p ↦ if p = O then s else asStrategy xStrategy)
          = ticTacToe.payoff O (fun p ↦ if p = O then
              asStrategy (simulateMemorylessO s xStrategy)
              else asStrategy xStrategy) := hsim.symm
      _ ≤ 0 := hmem

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

/-- A memoryless Nash equilibrium exists, and every Nash equilibrium has payoff zero. -/
theorem exists_memoryless_isNash :
    ∃ σ : StrategyProfile,
      (∀ p h, σ p h = σ p [currentBoard h]) ∧ ticTacToe.IsNash σ := by
  refine ⟨memorylessDrawProfile, ?_, memorylessDrawProfile_isNash⟩
  intro p h
  dsimp only [memorylessDrawProfile]
  split_ifs <;> simp [asStrategy, currentBoard]

/-!
## Unilateral memoryless projection preserves Nash

In this zero-sum win/draw/loss game, a profile is Nash iff both players use
**security strategies** (each guarantees a draw against every opposing strategy)
and the payoff is zero. Security of X means O never wins; security of O means X
never wins.

On every history compatible with a security strategy of X, that strategy's move
from the current board still leaves X able to guarantee a draw (otherwise an
opponent could steer to that history and win). The memoryless projection plays,
at each board, exactly one such move (the one from the lex-smallest compatible
history). Hence the projection remains a security strategy, and replacing either
player's strategy by its memoryless version preserves Nash.
-/

/-- Mutual security implies the profile payoff is zero. -/
private lemma payoff_eq_zero_of_isSecurity
    (σ : StrategyProfile)
    (hX : IsSecurityX (σ X)) (hO : IsSecurityO (σ O)) :
    ticTacToe.payoff X σ = 0 := by
  have hx : 0 ≤ ticTacToe.payoff X σ := by
    have := hX (σ O)
    have hprof : (fun p ↦ if p = X then σ X else σ O) = σ := by
      funext p; fin_cases p <;> simp [X, O]
    rwa [hprof] at this
  have ho : 0 ≤ ticTacToe.payoff O σ := by
    have := hO (σ X)
    have hprof : (fun p ↦ if p = O then σ O else σ X) = σ := by
      funext p; fin_cases p <;> simp [X, O]
    rwa [hprof] at this
  linarith [ticTacToe_payoff_add_eq_zero σ]

/-- Nash equilibria are exactly the mutually secure profiles (payoff zero follows). -/
theorem isNash_iff_isSecurity (σ : StrategyProfile) :
    ticTacToe.IsNash σ ↔ IsSecurityX (σ X) ∧ IsSecurityO (σ O) := by
  constructor
  · intro hσ
    have hpay := ticTacToe_nash_payoffs_eq_zero σ hσ
    rw [StrategicGame.isNash_iff] at hσ
    refine ⟨fun τ => ?_, fun τ => ?_⟩
    · have hdev := hσ O τ
      have hupd :
          Function.update σ O τ = (fun p ↦ if p = X then σ X else τ) := by
        funext p; fin_cases p <;> simp [X, O]
      rw [hupd] at hdev
      linarith [hdev, hpay.2,
        ticTacToe_payoff_add_eq_zero (fun p ↦ if p = X then σ X else τ)]
    · have hdev := hσ X τ
      have hupd :
          Function.update σ X τ = (fun p ↦ if p = O then σ O else τ) := by
        funext p; fin_cases p <;> simp [X, O]
      rw [hupd] at hdev
      linarith [hdev, hpay.1,
        ticTacToe_payoff_add_eq_zero (fun p ↦ if p = O then σ O else τ)]
  · intro ⟨hX, hO⟩
    rw [StrategicGame.isNash_iff]
    intro i s
    have hzero := payoff_eq_zero_of_isSecurity σ hX hO
    fin_cases i
    · change ticTacToe.payoff X (Function.update σ X s) ≤ ticTacToe.payoff X σ
      rw [hzero]
      have hupd :
          Function.update σ X s = (fun p ↦ if p = O then σ O else s) := by
        funext p; fin_cases p <;> simp [X, O]
      rw [hupd]
      have hsum := ticTacToe_payoff_add_eq_zero (fun p ↦ if p = O then σ O else s)
      linarith [hO s, hsum]
    · change ticTacToe.payoff O (Function.update σ O s) ≤ ticTacToe.payoff O σ
      have hzeroO : ticTacToe.payoff O σ = 0 := by
        linarith [ticTacToe_payoff_add_eq_zero σ, hzero]
      rw [hzeroO]
      have hupd :
          Function.update σ O s = (fun p ↦ if p = X then σ X else s) := by
        funext p; fin_cases p <;> simp [X, O]
      rw [hupd]
      have hsum := ticTacToe_payoff_add_eq_zero (fun p ↦ if p = X then σ X else s)
      linarith [hX s, hsum]

/-!
### Security is preserved by memoryless projection

We show that if `σ` is a security strategy for X, then its memoryless projection is
too. The argument is positional: every board reachable while X follows `σ` (with
arbitrary legal replies by O) is a “safe” board, the projection plays a legal
`σ`-move at every such board, and safe boards are closed under those moves and
under every legal O reply. Induction on the remaining length of play then shows
the projection forces a draw from every safe board, in particular from the empty
board.
-/

/-- X's payoff after `n` steps from a given history, with prescribed strategies. -/
def playPayoffX (σx σo : Strategy) (n : Nat) (turn : Player) (h : History) : ℝ :=
  let b := currentBoard
    (playAccordingToStrategy (fun p ↦ if p = X then σx else σo) n turn h)
  if hasWon b X then (1 : ℝ) else if hasWon b O then -1 else 0

/-- `σx` forces a nonnegative payoff for X from this history against every opponent. -/
def ForcesDrawXFrom (σx : Strategy) (n : Nat) (turn : Player) (h : History) : Prop :=
  ∀ σo : Strategy, 0 ≤ playPayoffX σx σo n turn h

/-- O's payoff after `n` steps from a given history. -/
def playPayoffO (σo σx : Strategy) (n : Nat) (turn : Player) (h : History) : ℝ :=
  let b := currentBoard
    (playAccordingToStrategy (fun p ↦ if p = O then σo else σx) n turn h)
  if hasWon b X then (-1 : ℝ) else if hasWon b O then 1 else 0

/-- `σo` forces a nonnegative payoff for O from this history against every opponent. -/
def ForcesDrawOFrom (σo : Strategy) (n : Nat) (turn : Player) (h : History) : Prop :=
  ∀ σx : Strategy, 0 ≤ playPayoffO σo σx n turn h

/-- Histories reachable while X follows `σ` and O may play any legal move. -/
inductive ReachableX (σ : Strategy) : Player → History → Prop where
  | start : ReachableX σ X [emptyBoard]
  | stopGameOver {turn : Player} {h : History} :
      ReachableX σ turn h → gameOver (currentBoard h) = true → ReachableX σ turn h
  | xMove {h : History} :
      ReachableX σ X h →
      gameOver (currentBoard h) = false →
      (currentBoard h (σ h)).isNone = true →
      ReachableX σ O
        (h ++ [Function.update (currentBoard h) (σ h) (some X)])
  | oMove {h : History} :
      ReachableX σ O h →
      gameOver (currentBoard h) = false →
      (pos : Position) →
      (currentBoard h pos).isNone = true →
      ReachableX σ X
        (h ++ [Function.update (currentBoard h) pos (some O)])

/-- Histories reachable while O follows `σ` and X may play any legal move. -/
inductive ReachableO (σ : Strategy) : Player → History → Prop where
  | start : ReachableO σ X [emptyBoard]
  | stopGameOver {turn : Player} {h : History} :
      ReachableO σ turn h → gameOver (currentBoard h) = true → ReachableO σ turn h
  | oMove {h : History} :
      ReachableO σ O h →
      gameOver (currentBoard h) = false →
      (currentBoard h (σ h)).isNone = true →
      ReachableO σ X
        (h ++ [Function.update (currentBoard h) (σ h) (some O)])
  | xMove {h : History} :
      ReachableO σ X h →
      gameOver (currentBoard h) = false →
      (pos : Position) →
      (currentBoard h pos).isNone = true →
      ReachableO σ O
        (h ++ [Function.update (currentBoard h) pos (some X)])

/-- Boards that appear while X follows `σ`, with the indicated player to move. -/
def CompatibleBoardX (σ : Strategy) (turn : Player) (b : Board) : Prop :=
  ∃ h, ReachableX σ turn h ∧ currentBoard h = b

/-- Boards that appear while O follows `σ`, with the indicated player to move. -/
def CompatibleBoardO (σ : Strategy) (turn : Player) (b : Board) : Prop :=
  ∃ h, ReachableO σ turn h ∧ currentBoard h = b

@[simp] lemma playPayoffX_isSecurityX (σ : Strategy) :
    IsSecurityX σ ↔ ForcesDrawXFrom σ 9 X [emptyBoard] := by
  simp only [IsSecurityX, ForcesDrawXFrom, playPayoffX, finalBoard]
  rfl

@[simp] lemma playPayoffO_isSecurityO (σ : Strategy) :
    IsSecurityO σ ↔ ForcesDrawOFrom σ 9 X [emptyBoard] := by
  simp only [IsSecurityO, ForcesDrawOFrom, playPayoffO, finalBoard]
  rfl

/-- The empty board is X-compatible with X to move. -/
lemma compatibleBoardX_empty (σ : Strategy) :
    CompatibleBoardX σ X emptyBoard :=
  ⟨[emptyBoard], ReachableX.start, rfl⟩

/-- The empty board is O-compatible with X to move (X moves first). -/
lemma compatibleBoardO_empty (σ : Strategy) :
    CompatibleBoardO σ X emptyBoard :=
  ⟨[emptyBoard], ReachableO.start, rfl⟩


private lemma foldl_historyMin_from_some (l : List History) (b h : History) :
    l.foldl historyMinStep (some b) = some h → h = b ∨ h ∈ l := by
  induction l generalizing b with
  | nil =>
      intro hh
      simp at hh
      exact Or.inl hh.symm
  | cons x xs ih =>
      intro hh
      simp only [List.foldl_cons, historyMinStep] at hh
      rcases ih _ hh with heq | hmem
      · split_ifs at heq with hlt
        · exact Or.inr (heq ▸ List.mem_cons_self)
        · exact Or.inl heq
      · exact Or.inr (List.mem_cons_of_mem _ hmem)

/-- Fold that selects a lex-min history only returns an element of the list. -/
private lemma foldl_historyMin_mem (l : List History) (h : History) :
    l.foldl historyMinStep none = some h → h ∈ l := by
  cases l with
  | nil => simp
  | cons x xs =>
      intro hh
      simp only [List.foldl_cons, historyMinStep] at hh
      rcases foldl_historyMin_from_some xs x h hh with heq | hmem
      · exact heq ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ hmem

lemma player_cases (t : Player) : t = X ∨ t = O := by
  fin_cases t <;> simp [X, O]

lemma otherPlayer_val (t : Player) : (otherPlayer t).val = (t.val + 1) % 2 := by
  rcases player_cases t with rfl | rfl <;> simp [otherPlayer, X, O]

lemma currentBoard_append_singleton (h : History) (b : Board) :
    currentBoard (h ++ [b]) = b := by
  simp [currentBoard]

lemma isNone_iff_not_isSome {o : Option Player} : o.isNone = true ↔ ¬ o.isSome = true := by
  cases o <;> simp

lemma hasWon_mono {b b' : Board} {p : Player} (hle : ∀ q, b' q = some p → b q = some p)
    (h : hasWon b' p = true) : hasWon b p = true := by
  simp only [hasWon, decide_eq_true_eq] at h ⊢
  rcases h with ⟨r, hr⟩ | ⟨c, hc⟩ | hd | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨r, fun c => hle _ (hr c)⟩
  · exact Or.inr (Or.inl ⟨c, fun r => hle _ (hc r)⟩)
  · exact Or.inr (Or.inr (Or.inl fun i => hle _ (hd i)))
  · exact Or.inr (Or.inr (Or.inr ⟨hle _ h1, hle _ h2, hle _ h3⟩))

lemma hasWon_update_other {b : Board} {pos : Position} {p q : Player} (hpq : p ≠ q)
    (h : hasWon b p = false) : hasWon (Function.update b pos (some q)) p = false := by
  by_contra hw
  have hw' : hasWon (Function.update b pos (some q)) p = true := by simpa using hw
  have := hasWon_mono (b := b) (fun r hr => by
    by_cases hrp : r = pos
    · subst hrp
      simp at hr
      exact absurd hr.symm hpq
    · simpa [Function.update_of_ne hrp] using hr) hw'
  simp [h] at this

lemma hasWon_false_of_not_gameOver {b : Board} (h : gameOver b = false) (p : Player)
    (hp : p = X ∨ p = O) : hasWon b p = false := by
  simp only [gameOver, Bool.or_eq_false_iff] at h
  rcases hp with rfl | rfl
  · exact h.1.1
  · exact h.1.2

lemma play_gameOver (σ : StrategyProfile) (n : Nat) (turn : Player) (h : History)
    (hg : gameOver (currentBoard h) = true) :
    playAccordingToStrategy σ n turn h = h := by
  cases n <;> simp [playAccordingToStrategy, hg]

lemma play_congr (σ σ' : StrategyProfile) (n : Nat) :
    ∀ (turn : Player) (h : History),
      (∀ q g, h.length ≤ g.length → σ q g = σ' q g) →
      playAccordingToStrategy σ n turn h = playAccordingToStrategy σ' n turn h := by
  induction n with
  | zero => intro turn h _; rfl
  | succ n ih =>
      intro turn h hag
      simp only [playAccordingToStrategy]
      rw [hag turn h le_rfl]
      split_ifs <;> first
        | rfl
        | exact ih _ _ (fun q g hg => hag q g (le_trans (by simp) hg))

lemma playPayoffX_gameOver (σx σo : Strategy) (n : Nat) (turn : Player) (h : History)
    (hg : gameOver (currentBoard h) = true) :
    playPayoffX σx σo n turn h =
      if hasWon (currentBoard h) X then (1 : ℝ)
        else if hasWon (currentBoard h) O then -1 else 0 := by
  simp [playPayoffX, play_gameOver _ _ _ _ hg]

lemma playPayoffX_step_X (σx σo : Strategy) (n : Nat) (h : History)
    (hg : gameOver (currentBoard h) = false) (hl : (currentBoard h (σx h)).isNone = true) :
    playPayoffX σx σo (n + 1) X h =
      playPayoffX σx σo n O (h ++ [Function.update (currentBoard h) (σx h) (some X)]) := by
  have hl' : (currentBoard h (σx h)).isSome = false := by simpa [isNone_iff_not_isSome] using hl
  simp [playPayoffX, playAccordingToStrategy, hg, hl', otherPlayer]

lemma playPayoffX_step_O (σx σo : Strategy) (n : Nat) (h : History)
    (hg : gameOver (currentBoard h) = false) (hl : (currentBoard h (σo h)).isNone = true) :
    playPayoffX σx σo (n + 1) O h =
      playPayoffX σx σo n X (h ++ [Function.update (currentBoard h) (σo h) (some O)]) := by
  have hl' : (currentBoard h (σo h)).isSome = false := by simpa [isNone_iff_not_isSome] using hl
  simp [playPayoffX, playAccordingToStrategy, hg, hl', otherPlayer, X, O]

lemma hasWon_oWinning_X : hasWon oWinningBoard X = false := by decide +kernel
lemma hasWon_oWinning_O : hasWon oWinningBoard O = true := by decide +kernel
lemma hasWon_xWinning_X : hasWon xWinningBoard X = true := by decide +kernel
lemma hasWon_xWinning_O : hasWon xWinningBoard O = false := by decide +kernel

lemma playPayoffX_illegal_X (σx σo : Strategy) (n : Nat) (h : History)
    (hg : gameOver (currentBoard h) = false) (hl : (currentBoard h (σx h)).isNone = false) :
    playPayoffX σx σo (n + 1) X h = -1 := by
  have hl' : (currentBoard h (σx h)).isSome = true := by simpa [isNone_iff_not_isSome] using hl
  simp [playPayoffX, playAccordingToStrategy, hg, hl', currentBoard, X,
    hasWon_oWinning_X, hasWon_oWinning_O]

lemma playPayoffX_illegal_O (σx σo : Strategy) (n : Nat) (h : History)
    (hg : gameOver (currentBoard h) = false) (hl : (currentBoard h (σo h)).isNone = false) :
    playPayoffX σx σo (n + 1) O h = 1 := by
  have hl' : (currentBoard h (σo h)).isSome = true := by simpa [isNone_iff_not_isSome] using hl
  simp [playPayoffX, playAccordingToStrategy, hg, hl', currentBoard, X, O,
    hasWon_xWinning_X]

lemma playPayoffX_congr_opponent (σx σo σo' : Strategy) (n : Nat) (turn : Player)
    (h : History) (hag : ∀ g, h.length ≤ g.length → σo g = σo' g) :
    playPayoffX σx σo n turn h = playPayoffX σx σo' n turn h := by
  have hc : playAccordingToStrategy (fun p ↦ if p = X then σx else σo) n turn h =
      playAccordingToStrategy (fun p ↦ if p = X then σx else σo') n turn h := by
    apply play_congr
    intro q g hgl
    by_cases hq : q = X
    · simp [hq]
    · simp [hq, hag g hgl]
  simp only [playPayoffX, hc]

lemma playPayoffO_gameOver (σo σx : Strategy) (n : Nat) (turn : Player) (h : History)
    (hg : gameOver (currentBoard h) = true) :
    playPayoffO σo σx n turn h =
      if hasWon (currentBoard h) X then (-1 : ℝ)
        else if hasWon (currentBoard h) O then 1 else 0 := by
  simp [playPayoffO, play_gameOver _ _ _ _ hg]

lemma playPayoffO_step_O (σo σx : Strategy) (n : Nat) (h : History)
    (hg : gameOver (currentBoard h) = false) (hl : (currentBoard h (σo h)).isNone = true) :
    playPayoffO σo σx (n + 1) O h =
      playPayoffO σo σx n X (h ++ [Function.update (currentBoard h) (σo h) (some O)]) := by
  have hl' : (currentBoard h (σo h)).isSome = false := by simpa [isNone_iff_not_isSome] using hl
  simp [playPayoffO, playAccordingToStrategy, hg, hl', otherPlayer, X, O]

lemma playPayoffO_step_X (σo σx : Strategy) (n : Nat) (h : History)
    (hg : gameOver (currentBoard h) = false) (hl : (currentBoard h (σx h)).isNone = true) :
    playPayoffO σo σx (n + 1) X h =
      playPayoffO σo σx n O (h ++ [Function.update (currentBoard h) (σx h) (some X)]) := by
  have hl' : (currentBoard h (σx h)).isSome = false := by simpa [isNone_iff_not_isSome] using hl
  simp [playPayoffO, playAccordingToStrategy, hg, hl', otherPlayer, X, O]

lemma playPayoffO_illegal_O (σo σx : Strategy) (n : Nat) (h : History)
    (hg : gameOver (currentBoard h) = false) (hl : (currentBoard h (σo h)).isNone = false) :
    playPayoffO σo σx (n + 1) O h = -1 := by
  have hl' : (currentBoard h (σo h)).isSome = true := by simpa [isNone_iff_not_isSome] using hl
  simp [playPayoffO, playAccordingToStrategy, hg, hl', currentBoard, X, O,
    hasWon_xWinning_X]

lemma playPayoffO_illegal_X (σo σx : Strategy) (n : Nat) (h : History)
    (hg : gameOver (currentBoard h) = false) (hl : (currentBoard h (σx h)).isNone = false) :
    playPayoffO σo σx (n + 1) X h = 1 := by
  have hl' : (currentBoard h (σx h)).isSome = true := by simpa [isNone_iff_not_isSome] using hl
  simp [playPayoffO, playAccordingToStrategy, hg, hl', currentBoard, X, O,
    hasWon_oWinning_X, hasWon_oWinning_O]

lemma playPayoffO_congr_opponent (σo σx σx' : Strategy) (n : Nat) (turn : Player)
    (h : History) (hag : ∀ g, h.length ≤ g.length → σx g = σx' g) :
    playPayoffO σo σx n turn h = playPayoffO σo σx' n turn h := by
  have hc : playAccordingToStrategy (fun p ↦ if p = O then σo else σx) n turn h =
      playAccordingToStrategy (fun p ↦ if p = O then σo else σx') n turn h := by
    apply play_congr
    intro q g hgl
    by_cases hq : q = O
    · simp [hq]
    · simp [hq, hag g hgl]
  simp only [playPayoffO, hc]

lemma mem_historiesFollowing_succ {p : Player} {σ : Strategy} {n : Nat} {turn : Player}
    {h h' : History} :
    h' ∈ historiesFollowing p σ (n + 1) turn h ↔
      h' = h ∨
      (gameOver (currentBoard h) = false ∧
        ((turn = p ∧ (currentBoard h (σ h)).isNone = true ∧
            h' ∈ historiesFollowing p σ n (otherPlayer turn)
              (h ++ [Function.update (currentBoard h) (σ h) (some turn)])) ∨
          (turn ≠ p ∧ ∃ pos : Position, (currentBoard h pos).isNone = true ∧
            h' ∈ historiesFollowing p σ n (otherPlayer turn)
              (h ++ [Function.update (currentBoard h) pos (some turn)])))) := by
  rw [historiesFollowing]
  by_cases hg : gameOver (currentBoard h) = true
  · conv_lhs => simp only [hg, ↓reduceIte]
    simp [hg]
  · have hg' : gameOver (currentBoard h) = false := by simpa using hg
    conv_lhs => simp only [hg', Bool.false_eq_true, ↓reduceIte]
    by_cases ht : turn = p
    · subst ht
      conv_lhs => simp only [↓reduceIte]
      by_cases hocc : (currentBoard h (σ h)).isNone = true
      · have hocc' : ¬ (currentBoard h (σ h)).isSome = true := isNone_iff_not_isSome.1 hocc
        conv_lhs => simp only [hocc', ↓reduceIte]
        simp [hg', hocc]
      · have hocc' : (currentBoard h (σ h)).isSome = true := by
          by_contra hh
          exact hocc (isNone_iff_not_isSome.2 hh)
        conv_lhs => simp only [hocc', ↓reduceIte]
        simp [hg', hocc]
    · conv_lhs =>
        simp only [ht, ↓reduceIte, List.mem_cons, List.mem_flatMap, List.mem_finRange, true_and]
      constructor
      · rintro (rfl | ⟨i, j, hij⟩)
        · exact Or.inl rfl
        · refine Or.inr ⟨hg', Or.inr ⟨ht, (i, j), ?_⟩⟩
          by_cases hs : (currentBoard h (i, j)).isSome = true
          · simp [hs] at hij
          · simp only [hs] at hij
            exact ⟨isNone_iff_not_isSome.2 hs, hij⟩
      · rintro (rfl | ⟨_, (hcontra | ⟨_, ⟨i, j⟩, hl, hm⟩)⟩)
        · exact Or.inl rfl
        · exact absurd hcontra.1 ht
        · refine Or.inr ⟨i, j, ?_⟩
          have hs : ¬ (currentBoard h (i, j)).isSome = true := isNone_iff_not_isSome.1 hl
          simpa [hs] using hm

lemma historiesFollowing_mem_self (p : Player) (σ : Strategy) (n : Nat)
    (turn : Player) (h : History) : h ∈ historiesFollowing p σ n turn h := by
  cases n with
  | zero => simp [historiesFollowing]
  | succ n => exact mem_historiesFollowing_succ.2 (Or.inl rfl)

lemma historiesFollowing_length_ge (p : Player) (σ : Strategy) (n : Nat) :
    ∀ (turn : Player) (s h' : History), h' ∈ historiesFollowing p σ n turn s →
      s.length ≤ h'.length := by
  induction n with
  | zero =>
      intro turn s h' hh
      rw [historiesFollowing, List.mem_singleton] at hh
      subst hh; rfl
  | succ n ih =>
      intro turn s h' hh
      rcases mem_historiesFollowing_succ.1 hh with
        rfl | ⟨_, ⟨_, _, hm⟩ | ⟨_, pos, _, hm⟩⟩
      · rfl
      · exact le_trans (by simp) (ih _ _ _ hm)
      · exact le_trans (by simp) (ih _ _ _ hm)

lemma historiesFollowing_mono_succ (p : Player) (σ : Strategy) (n : Nat) :
    ∀ (turn : Player) (s h' : History), h' ∈ historiesFollowing p σ n turn s →
      h' ∈ historiesFollowing p σ (n + 1) turn s := by
  induction n with
  | zero =>
      intro turn s h' hh
      rw [historiesFollowing, List.mem_singleton] at hh
      subst hh
      exact historiesFollowing_mem_self _ _ _ _ _
  | succ n ih =>
      intro turn s h' hh
      rcases mem_historiesFollowing_succ.1 hh with
        rfl | ⟨hg, ⟨ht, hl, hm⟩ | ⟨ht, pos, hl, hm⟩⟩
      · exact historiesFollowing_mem_self _ _ _ _ _
      · exact mem_historiesFollowing_succ.2 (Or.inr ⟨hg, Or.inl ⟨ht, hl, ih _ _ _ hm⟩⟩)
      · exact mem_historiesFollowing_succ.2
          (Or.inr ⟨hg, Or.inr ⟨ht, pos, hl, ih _ _ _ hm⟩⟩)

lemma historiesFollowing_mono (p : Player) (σ : Strategy) {m n : Nat} (hmn : m ≤ n)
    {turn : Player} {s h' : History} (hh : h' ∈ historiesFollowing p σ m turn s) :
    h' ∈ historiesFollowing p σ n turn s := by
  induction n, hmn using Nat.le_induction with
  | base => exact hh
  | succ n _ ih => exact historiesFollowing_mono_succ p σ n _ _ _ ih

/-- A legal child of a node of the enumeration tree appears one level deeper. -/
lemma historiesFollowing_child (p : Player) (σ : Strategy) (n : Nat) :
    ∀ (turn : Player) (s h : History) (tH : Player) (pos : Position),
      h ∈ historiesFollowing p σ n turn s →
      (tH.val + h.length) % 2 = (turn.val + s.length) % 2 →
      gameOver (currentBoard h) = false → (currentBoard h pos).isNone = true →
      (tH = p → pos = σ h) →
      h ++ [Function.update (currentBoard h) pos (some tH)] ∈
        historiesFollowing p σ (n + 1) turn s := by
  induction n with
  | zero =>
      intro turn s h tH pos hh hpar hg hl hp
      rw [historiesFollowing, List.mem_singleton] at hh
      subst hh
      have htH : tH = turn := by
        apply Fin.ext
        have := tH.isLt
        have := turn.isLt
        omega
      subst htH
      refine mem_historiesFollowing_succ.2 (Or.inr ⟨hg, ?_⟩)
      by_cases ht : tH = p
      · subst ht
        have := hp rfl
        subst this
        exact Or.inl ⟨rfl, hl, historiesFollowing_mem_self _ _ _ _ _⟩
      · exact Or.inr ⟨ht, pos, hl, historiesFollowing_mem_self _ _ _ _ _⟩
  | succ n ih =>
      intro turn s h tH pos hh hpar hg hl hp
      rcases mem_historiesFollowing_succ.1 hh with
        rfl | ⟨hgs, ⟨ht, hls, hm⟩ | ⟨ht, pos', hls, hm⟩⟩
      · have htH : tH = turn := by
          apply Fin.ext
          have := tH.isLt
          have := turn.isLt
          omega
        subst htH
        refine mem_historiesFollowing_succ.2 (Or.inr ⟨hg, ?_⟩)
        by_cases ht : tH = p
        · subst ht
          have := hp rfl
          subst this
          exact Or.inl ⟨rfl, hl, historiesFollowing_mem_self _ _ _ _ _⟩
        · exact Or.inr ⟨ht, pos, hl, historiesFollowing_mem_self _ _ _ _ _⟩
      · have := ih _ _ _ tH pos hm (by
          rw [otherPlayer_val]
          simp only [List.length_append, List.length_singleton] at hpar ⊢
          omega) hg hl hp
        exact mem_historiesFollowing_succ.2 (Or.inr ⟨hgs, Or.inl ⟨ht, hls, this⟩⟩)
      · have := ih _ _ _ tH pos hm (by
          rw [otherPlayer_val]
          simp only [List.length_append, List.length_singleton] at hpar ⊢
          omega) hg hl hp
        exact mem_historiesFollowing_succ.2 (Or.inr ⟨hgs, Or.inr ⟨ht, pos', hls, this⟩⟩)

lemma X_val : X.val = 0 := rfl

lemma O_val : O.val = 1 := rfl

lemma currentBoard_singleton (b : Board) : currentBoard [b] = b := rfl

lemma ReachableX.inv {σ : Strategy} {turn : Player} {h : History}
    (hr : ReachableX σ turn h) :
    (turn.val + h.length) % 2 = 1 ∧ h.length + emptyCount (currentBoard h) = 10 := by
  induction hr with
  | start => simp [emptyCount_empty, currentBoard_singleton]
  | stopGameOver _ _ ih => exact ih
  | xMove hr hg hl ih =>
      have := emptyCount_update (currentBoard _) _ X hl
      simp only [currentBoard_append_singleton, List.length_append, List.length_singleton, O_val]
      rw [X_val] at ih
      omega
  | oMove hr hg pos hl ih =>
      have := emptyCount_update (currentBoard _) pos O hl
      simp only [currentBoard_append_singleton, List.length_append, List.length_singleton, X_val]
      rw [O_val] at ih
      omega

lemma ReachableO.inv {σ : Strategy} {turn : Player} {h : History}
    (hr : ReachableO σ turn h) :
    (turn.val + h.length) % 2 = 1 ∧ h.length + emptyCount (currentBoard h) = 10 := by
  induction hr with
  | start => simp [emptyCount_empty, currentBoard_singleton]
  | stopGameOver _ _ ih => exact ih
  | oMove hr hg hl ih =>
      have := emptyCount_update (currentBoard _) _ O hl
      simp only [currentBoard_append_singleton, List.length_append, List.length_singleton, X_val]
      rw [O_val] at ih
      omega
  | xMove hr hg pos hl ih =>
      have := emptyCount_update (currentBoard _) pos X hl
      simp only [currentBoard_append_singleton, List.length_append, List.length_singleton, O_val]
      rw [X_val] at ih
      omega

/-- Every `ReachableX` history appears in `historiesFollowing` with enough fuel. -/
lemma ReachableX.mem_historiesFollowing_fuel {σ : Strategy} {turn : Player}
    {h : History} (hr : ReachableX σ turn h) :
    h ∈ historiesFollowing X σ (h.length - 1) X [emptyBoard] := by
  induction hr with
  | start => exact historiesFollowing_mem_self _ _ _ _ _
  | stopGameOver _ _ ih => exact ih
  | @xMove h hr hg hl ih =>
      have hlen := historiesFollowing_length_ge _ _ _ _ _ _ ih
      have hinv := hr.inv
      have := historiesFollowing_child X σ (h.length - 1) X [emptyBoard] h X (σ h) ih
        (by simp only [X] at hinv ⊢; simpa using hinv.1) hg hl (fun _ => rfl)
      simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
      simp only [List.length_singleton] at hlen
      rwa [Nat.sub_add_cancel hlen] at this
  | @oMove h hr hg pos hl ih =>
      have hlen := historiesFollowing_length_ge _ _ _ _ _ _ ih
      have hinv := hr.inv
      have := historiesFollowing_child X σ (h.length - 1) X [emptyBoard] h O pos ih
        (by simp only [X, O] at hinv ⊢; simpa using hinv.1) hg hl
        (fun hh => absurd hh (by decide))
      simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
      simp only [List.length_singleton] at hlen
      rwa [Nat.sub_add_cancel hlen] at this

lemma ReachableX.mem_historiesFollowing {σ : Strategy} {turn : Player} {h : History}
    (hr : ReachableX σ turn h) :
    h ∈ historiesFollowing X σ 9 X [emptyBoard] :=
  historiesFollowing_mono X σ (by have := hr.inv; omega) hr.mem_historiesFollowing_fuel

lemma ReachableO.mem_historiesFollowing_fuel {σ : Strategy} {turn : Player}
    {h : History} (hr : ReachableO σ turn h) :
    h ∈ historiesFollowing O σ (h.length - 1) X [emptyBoard] := by
  induction hr with
  | start => exact historiesFollowing_mem_self _ _ _ _ _
  | stopGameOver _ _ ih => exact ih
  | @oMove h hr hg hl ih =>
      have hlen := historiesFollowing_length_ge _ _ _ _ _ _ ih
      have hinv := hr.inv
      have := historiesFollowing_child O σ (h.length - 1) X [emptyBoard] h O (σ h) ih
        (by simp only [X, O] at hinv ⊢; simpa using hinv.1) hg hl (fun _ => rfl)
      simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
      simp only [List.length_singleton] at hlen
      rwa [Nat.sub_add_cancel hlen] at this
  | @xMove h hr hg pos hl ih =>
      have hlen := historiesFollowing_length_ge _ _ _ _ _ _ ih
      have hinv := hr.inv
      have := historiesFollowing_child O σ (h.length - 1) X [emptyBoard] h X pos ih
        (by simp only [X] at hinv ⊢; simpa using hinv.1) hg hl
        (fun hh => absurd hh (by decide))
      simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
      simp only [List.length_singleton] at hlen
      rwa [Nat.sub_add_cancel hlen] at this

/-- Dual: membership for `ReachableO`. -/
lemma ReachableO.mem_historiesFollowing {σ : Strategy} {turn : Player} {h : History}
    (hr : ReachableO σ turn h) :
    h ∈ historiesFollowing O σ 9 X [emptyBoard] :=
  historiesFollowing_mono O σ (by have := hr.inv; omega) hr.mem_historiesFollowing_fuel

/-- Anything enumerated from a reachable seed is itself reachable. -/
lemma ReachableX.of_mem_historiesFollowing {σ : Strategy} (n : Nat) :
    ∀ {turn : Player} {s h' : History}, ReachableX σ turn s →
      h' ∈ historiesFollowing X σ n turn s → ∃ t, ReachableX σ t h' := by
  induction n with
  | zero =>
      intro turn s h' hr hh
      rw [historiesFollowing, List.mem_singleton] at hh
      subst hh
      exact ⟨turn, hr⟩
  | succ n ih =>
      intro turn s h' hr hh
      rcases mem_historiesFollowing_succ.1 hh with
        rfl | ⟨hg, ⟨ht, hl, hm⟩ | ⟨ht, pos, hl, hm⟩⟩
      · exact ⟨turn, hr⟩
      · subst ht
        exact ih (ReachableX.xMove hr hg hl) hm
      · rcases player_cases turn with rfl | rfl
        · exact absurd rfl ht
        · exact ih (ReachableX.oMove hr hg pos hl) hm

lemma ReachableO.of_mem_historiesFollowing {σ : Strategy} (n : Nat) :
    ∀ {turn : Player} {s h' : History}, ReachableO σ turn s →
      h' ∈ historiesFollowing O σ n turn s → ∃ t, ReachableO σ t h' := by
  induction n with
  | zero =>
      intro turn s h' hr hh
      rw [historiesFollowing, List.mem_singleton] at hh
      subst hh
      exact ⟨turn, hr⟩
  | succ n ih =>
      intro turn s h' hr hh
      rcases mem_historiesFollowing_succ.1 hh with
        rfl | ⟨hg, ⟨ht, hl, hm⟩ | ⟨ht, pos, hl, hm⟩⟩
      · exact ⟨turn, hr⟩
      · subst ht
        exact ih (ReachableO.oMove hr hg hl) hm
      · rcases player_cases turn with rfl | rfl
        · exact ih (ReachableO.xMove hr hg pos hl) hm
        · exact absurd rfl ht

private lemma foldl_historyMin_from_some_ne (l : List History) (b : History) :
    ∃ h, l.foldl historyMinStep (some b) = some h := by
  induction l generalizing b with
  | nil => exact ⟨b, rfl⟩
  | cons x xs ih => exact ih _

private lemma foldl_historyMin_ne_none (l : List History) (hl : l ≠ []) :
    ∃ h, l.foldl historyMinStep none = some h := by
  cases l with
  | nil => exact absurd rfl hl
  | cons x xs => exact foldl_historyMin_from_some_ne xs x

lemma smallestCompatibleHistory?_spec (p : Player) (σ : Strategy) (b : Board)
    {h : History} (hh : smallestCompatibleHistory? p σ [b] = some h) :
    h ∈ historiesFollowing p σ 9 X [emptyBoard] ∧
      boardCode (currentBoard h) = boardCode b := by
  unfold smallestCompatibleHistory? at hh
  have hmem := foldl_historyMin_mem _ _ hh
  rw [List.mem_filter] at hmem
  refine ⟨hmem.1, ?_⟩
  simpa [currentBoard_singleton] using hmem.2

lemma smallestCompatibleHistory?_exists (p : Player) (σ : Strategy) {b : Board}
    {h₀ : History} (hm : h₀ ∈ historiesFollowing p σ 9 X [emptyBoard])
    (hb : currentBoard h₀ = b) : ∃ h, smallestCompatibleHistory? p σ [b] = some h := by
  unfold smallestCompatibleHistory?
  apply foldl_historyMin_ne_none
  intro hnil
  have : h₀ ∈ (historiesFollowing p σ 9 X [emptyBoard]).filter
      (fun h' => boardCode (currentBoard h') == boardCode (currentBoard [b])) := by
    rw [List.mem_filter]
    exact ⟨hm, by simp [currentBoard_singleton, hb]⟩
  rw [hnil] at this
  simp at this

/-- If `smallestCompatibleHistory?` finds a history for board `b`, that history is in
`historiesFollowing` and ends at a board with the same `boardCode` as `b`. -/
lemma smallestCompatibleHistory?_spec_X (σ : Strategy) (b : Board) {h : History}
    (hh : smallestCompatibleHistory? X σ [b] = some h) :
    h ∈ historiesFollowing X σ 9 X [emptyBoard] ∧
      boardCode (currentBoard h) = boardCode b :=
  smallestCompatibleHistory?_spec X σ b hh

lemma smallestCompatibleHistory?_spec_O (σ : Strategy) (b : Board) {h : History}
    (hh : smallestCompatibleHistory? O σ [b] = some h) :
    h ∈ historiesFollowing O σ 9 X [emptyBoard] ∧
      boardCode (currentBoard h) = boardCode b :=
  smallestCompatibleHistory?_spec O σ b hh

/-- On an X-compatible board, the memoryless projection uses a real `σ`-reply on an
X-to-move reachable history ending at that board. -/
lemma toMemorylessStrategy_eq_of_compatibleBoardX
    (σ : Strategy) {b : Board} (hb : CompatibleBoardX σ X b) :
    ∃ h, ReachableX σ X h ∧ currentBoard h = b ∧ toMemorylessStrategy X σ b = σ h := by
  obtain ⟨h₀, hr₀, hb₀⟩ := hb
  obtain ⟨h, hs⟩ := smallestCompatibleHistory?_exists X σ hr₀.mem_historiesFollowing hb₀
  obtain ⟨hmem, hcode⟩ := smallestCompatibleHistory?_spec_X σ b hs
  have hcb : currentBoard h = b := boardCode_injective hcode
  obtain ⟨t, hrt⟩ := ReachableX.of_mem_historiesFollowing 9 ReachableX.start hmem
  have hi := hrt.inv
  have hi₀ := hr₀.inv
  have hle : h.length = h₀.length := by
    rw [hcb, ← hb₀] at hi
    omega
  have ht : t = X := by
    apply Fin.ext
    have := t.isLt
    rw [X_val]
    rw [X_val] at hi₀
    omega
  subst ht
  refine ⟨h, hrt, hcb, ?_⟩
  simp [toMemorylessStrategy, hs]

lemma toMemorylessStrategy_eq_of_compatibleBoardO
    (σ : Strategy) {b : Board} (hb : CompatibleBoardO σ O b) :
    ∃ h, ReachableO σ O h ∧ currentBoard h = b ∧ toMemorylessStrategy O σ b = σ h := by
  obtain ⟨h₀, hr₀, hb₀⟩ := hb
  obtain ⟨h, hs⟩ := smallestCompatibleHistory?_exists O σ hr₀.mem_historiesFollowing hb₀
  obtain ⟨hmem, hcode⟩ := smallestCompatibleHistory?_spec_O σ b hs
  have hcb : currentBoard h = b := boardCode_injective hcode
  obtain ⟨t, hrt⟩ := ReachableO.of_mem_historiesFollowing 9 ReachableO.start hmem
  have hi := hrt.inv
  have hi₀ := hr₀.inv
  have hle : h.length = h₀.length := by
    rw [hcb, ← hb₀] at hi
    omega
  have ht : t = O := by
    apply Fin.ext
    have := t.isLt
    rw [O_val]
    rw [O_val] at hi₀
    omega
  subst ht
  refine ⟨h, hrt, hcb, ?_⟩
  simp [toMemorylessStrategy, hs]

/-- Along an `X`-reachable history, `σ` still forces a draw for X with the remaining fuel. -/
lemma forcesDrawXFrom_of_reachableX (σ : Strategy) (hσ : IsSecurityX σ)
    {turn : Player} {h : History} (hr : ReachableX σ turn h) :
    ∀ n, n + h.length = 10 → ForcesDrawXFrom σ n turn h := by
  induction hr with
  | start =>
      intro n hn
      obtain rfl : n = 9 := by simpa using hn
      exact (playPayoffX_isSecurityX σ).1 hσ
  | stopGameOver _ _ ih => exact ih
  | @xMove h hr hg hl ih =>
      intro n hn σo
      have := ih (n + 1) (by simp only [List.length_append, List.length_singleton] at hn; omega) σo
      rwa [playPayoffX_step_X σ σo n h hg hl] at this
  | @oMove h hr hg pos hl ih =>
      intro n hn σo
      have hn' : n + 1 + h.length = 10 := by
        simp only [List.length_append, List.length_singleton] at hn; omega
      set σo' : Strategy := fun g => if g = h then pos else σo g with hσo'
      have := ih (n + 1) hn' σo'
      have hpos : σo' h = pos := by simp [hσo']
      rw [playPayoffX_step_O σ σo' n h hg (by simpa [hpos] using hl), hpos] at this
      rw [playPayoffX_congr_opponent σ σo σo' n X _ (fun g hgl => ?_)]
      · exact this
      · simp only [List.length_append, List.length_singleton] at hgl
        have hgh : g ≠ h := by
          rintro rfl
          omega
        simp [hσo', hgh]

lemma payoffX_nonneg {b : Board} (hO : hasWon b O = false) :
    0 ≤ (if hasWon b X then (1 : ℝ) else if hasWon b O then -1 else 0) := by
  by_cases hx : hasWon b X = true <;> simp [hx, hO]

lemma hasWon_O_false_of_reachableX (σ : Strategy) (hσ : IsSecurityX σ)
    {turn : Player} {h : History} (hr : ReachableX σ turn h) :
    hasWon (currentBoard h) O = false := by
  induction hr with
  | start => decide +kernel
  | stopGameOver _ _ ih => exact ih
  | @xMove h hr hg hl ih =>
      rw [currentBoard_append_singleton]
      exact hasWon_update_other (by decide) ih
  | @oMove h hr hg pos hl ih =>
      by_contra hw
      have hw' : hasWon (currentBoard (h ++ [Function.update (currentBoard h) pos (some O)])) O
          = true := by simpa using hw
      have hr' := ReachableX.oMove hr hg pos hl
      have hinv := hr'.inv
      have hX : hasWon (currentBoard h) X = false := hasWon_false_of_not_gameOver hg X (Or.inl rfl)
      have hX' : hasWon (currentBoard (h ++ [Function.update (currentBoard h) pos (some O)])) X
          = false := by
        rw [currentBoard_append_singleton]
        exact hasWon_update_other (by decide) hX
      have hover : gameOver (currentBoard (h ++ [Function.update (currentBoard h) pos (some O)]))
          = true := by simp [gameOver, hw']
      have := forcesDrawXFrom_of_reachableX σ hσ hr'
        (10 - (h ++ [Function.update (currentBoard h) pos (some O)]).length) (by omega)
        (fun _ => (0, 0))
      rw [playPayoffX_gameOver _ _ _ _ _ hover, hX', hw'] at this
      norm_num at this

/-- Security forbids O-wins on any X-compatible board. -/
lemma not_hasWon_O_of_compatibleBoardX
    (σ : Strategy) (hσ : IsSecurityX σ) {turn : Player} {b : Board}
    (hb : CompatibleBoardX σ turn b) : hasWon b O = false := by
  obtain ⟨h, hr, rfl⟩ := hb
  exact hasWon_O_false_of_reachableX σ hσ hr

/-- The memoryless X-move on an X-to-move compatible board is legal. -/
lemma toMemorylessStrategy_legal_of_compatibleBoardX
    (σ : Strategy) (hσ : IsSecurityX σ) {b : Board}
    (hb : CompatibleBoardX σ X b) (hgame : gameOver b = false) :
    (b (toMemorylessStrategy X σ b)).isNone = true := by
  obtain ⟨h, hr, hbEq, hμ⟩ := toMemorylessStrategy_eq_of_compatibleBoardX σ hb
  subst hbEq
  rw [hμ]
  by_contra hne
  have hne' : (currentBoard h (σ h)).isNone = false := Bool.eq_false_iff.2 hne
  have hinv := hr.inv
  have hpos := emptyCount_pos hgame
  obtain ⟨m, hm⟩ : ∃ m, 10 - h.length = m + 1 := ⟨10 - h.length - 1, by omega⟩
  have := forcesDrawXFrom_of_reachableX σ hσ hr (m + 1) (by omega) (fun _ => (0, 0))
  rw [playPayoffX_illegal_X _ _ _ _ hgame hne'] at this
  norm_num at this

/-- After a memoryless X-move from an X-to-move compatible board, O is to move. -/
lemma compatibleBoardX_after_memoryless_move
    (σ : Strategy) {b : Board} (hb : CompatibleBoardX σ X b)
    (hgame : gameOver b = false)
    (hlegal : (b (toMemorylessStrategy X σ b)).isNone = true) :
    CompatibleBoardX σ O
      (Function.update b (toMemorylessStrategy X σ b) (some X)) := by
  obtain ⟨h, hr, hbEq, hμ⟩ := toMemorylessStrategy_eq_of_compatibleBoardX σ hb
  have hNone : (currentBoard h (σ h)).isNone = true := by
    simpa [hbEq, hμ] using hlegal
  refine ⟨h ++ [Function.update (currentBoard h) (σ h) (some X)],
    ReachableX.xMove hr (by simpa [hbEq] using hgame) hNone, ?_⟩
  simp [currentBoard, hbEq, hμ]

/-- After any legal O-move from an O-to-move compatible board, X is to move. -/
lemma compatibleBoardX_after_o_move
    (σ : Strategy) {b : Board} (hb : CompatibleBoardX σ O b)
    (hgame : gameOver b = false) (pos : Position)
    (hlegal : (b pos).isNone = true) :
    CompatibleBoardX σ X (Function.update b pos (some O)) := by
  obtain ⟨h, hr, rfl⟩ := hb
  exact ⟨h ++ [Function.update (currentBoard h) pos (some O)],
    ReachableX.oMove hr hgame pos hlegal, by simp [currentBoard]⟩

/-- The memoryless projection forces a draw from every history whose current board is
X-compatible for the player about to move.

Proof sketch (induction on `n`):
* If the board is already terminal, `not_hasWon_O_of_compatibleBoardX` gives payoff ≥ 0.
* If X to move: the memoryless reply is a legal `σ`-move on some X-reachable history
  (`toMemorylessStrategy_legal` / `toMemorylessStrategy_eq`), the child board is
  O-compatible (`compatibleBoardX_after_memoryless_move`), and the IH applies.
* If O to move: an illegal reply awards the win to X; a legal reply lands on an
  X-compatible board (`compatibleBoardX_after_o_move`), and the IH applies.
-/
lemma forcesDrawXFrom_memoryless_of_compatible
    (σ : Strategy) (hσ : IsSecurityX σ) :
    ∀ n turn (h : History), CompatibleBoardX σ turn (currentBoard h) →
      ForcesDrawXFrom (asStrategy (toMemorylessStrategy X σ)) n turn h := by
  intro n
  induction n with
  | zero =>
      intro turn h hc σo
      have hO := not_hasWon_O_of_compatibleBoardX σ hσ hc
      simp only [playPayoffX, playAccordingToStrategy]
      exact payoffX_nonneg hO
  | succ n ih =>
      intro turn h hc σo
      by_cases hg : gameOver (currentBoard h) = true
      · have hO := not_hasWon_O_of_compatibleBoardX σ hσ hc
        rw [playPayoffX_gameOver _ _ _ _ _ hg]
        exact payoffX_nonneg hO
      · have hg' : gameOver (currentBoard h) = false := by simpa using hg
        rcases player_cases turn with rfl | rfl
        · have hl := toMemorylessStrategy_legal_of_compatibleBoardX σ hσ hc hg'
          rw [playPayoffX_step_X _ _ _ _ hg' hl]
          refine ih O _ ?_ σo
          rw [currentBoard_append_singleton]
          exact compatibleBoardX_after_memoryless_move σ hc hg' hl
        · by_cases hl : (currentBoard h (σo h)).isNone = true
          · rw [playPayoffX_step_O _ _ _ _ hg' hl]
            refine ih X _ ?_ σo
            rw [currentBoard_append_singleton]
            exact compatibleBoardX_after_o_move σ hc hg' _ hl
          · have hl' : (currentBoard h (σo h)).isNone = false := Bool.eq_false_iff.2 hl
            rw [playPayoffX_illegal_O _ _ _ _ hg' hl']
            norm_num

theorem isSecurityX_toMemorylessStrategy (σ : Strategy) (hσ : IsSecurityX σ) :
    IsSecurityX (asStrategy (toMemorylessStrategy X σ)) := by
  rw [playPayoffX_isSecurityX]
  exact forcesDrawXFrom_memoryless_of_compatible σ hσ 9 X [emptyBoard]
    (compatibleBoardX_empty σ)

/-- Along an `O`-reachable history, `σ` still forces a draw for O with the remaining fuel. -/
lemma forcesDrawOFrom_of_reachableO (σ : Strategy) (hσ : IsSecurityO σ)
    {turn : Player} {h : History} (hr : ReachableO σ turn h) :
    ∀ n, n + h.length = 10 → ForcesDrawOFrom σ n turn h := by
  induction hr with
  | start =>
      intro n hn
      obtain rfl : n = 9 := by simpa using hn
      exact (playPayoffO_isSecurityO σ).1 hσ
  | stopGameOver _ _ ih => exact ih
  | @oMove h hr hg hl ih =>
      intro n hn σx
      have := ih (n + 1) (by simp only [List.length_append, List.length_singleton] at hn; omega) σx
      rwa [playPayoffO_step_O σ σx n h hg hl] at this
  | @xMove h hr hg pos hl ih =>
      intro n hn σx
      have hn' : n + 1 + h.length = 10 := by
        simp only [List.length_append, List.length_singleton] at hn; omega
      set σx' : Strategy := fun g => if g = h then pos else σx g with hσx'
      have := ih (n + 1) hn' σx'
      have hpos : σx' h = pos := by simp [hσx']
      rw [playPayoffO_step_X σ σx' n h hg (by simpa [hpos] using hl), hpos] at this
      rw [playPayoffO_congr_opponent σ σx σx' n O _ (fun g hgl => ?_)]
      · exact this
      · simp only [List.length_append, List.length_singleton] at hgl
        have hgh : g ≠ h := by
          rintro rfl
          omega
        simp [hσx', hgh]

lemma payoffO_nonneg {b : Board} (hX : hasWon b X = false) :
    0 ≤ (if hasWon b X then (-1 : ℝ) else if hasWon b O then 1 else 0) := by
  by_cases hx : hasWon b O = true <;> simp [hx, hX]

lemma hasWon_X_false_of_reachableO (σ : Strategy) (hσ : IsSecurityO σ)
    {turn : Player} {h : History} (hr : ReachableO σ turn h) :
    hasWon (currentBoard h) X = false := by
  induction hr with
  | start => decide +kernel
  | stopGameOver _ _ ih => exact ih
  | @oMove h hr hg hl ih =>
      rw [currentBoard_append_singleton]
      exact hasWon_update_other (by decide) ih
  | @xMove h hr hg pos hl ih =>
      by_contra hw
      have hw' : hasWon (currentBoard (h ++ [Function.update (currentBoard h) pos (some X)])) X
          = true := by simpa using hw
      have hr' := ReachableO.xMove hr hg pos hl
      have hinv := hr'.inv
      have hover : gameOver (currentBoard (h ++ [Function.update (currentBoard h) pos (some X)]))
          = true := by simp [gameOver, hw']
      have := forcesDrawOFrom_of_reachableO σ hσ hr'
        (10 - (h ++ [Function.update (currentBoard h) pos (some X)]).length) (by omega)
        (fun _ => (0, 0))
      rw [playPayoffO_gameOver _ _ _ _ _ hover, hw'] at this
      norm_num at this

lemma not_hasWon_X_of_compatibleBoardO
    (σ : Strategy) (hσ : IsSecurityO σ) {turn : Player} {b : Board}
    (hb : CompatibleBoardO σ turn b) : hasWon b X = false := by
  obtain ⟨h, hr, rfl⟩ := hb
  exact hasWon_X_false_of_reachableO σ hσ hr

lemma toMemorylessStrategy_legal_of_compatibleBoardO
    (σ : Strategy) (hσ : IsSecurityO σ) {b : Board}
    (hb : CompatibleBoardO σ O b) (hgame : gameOver b = false) :
    (b (toMemorylessStrategy O σ b)).isNone = true := by
  obtain ⟨h, hr, hbEq, hμ⟩ := toMemorylessStrategy_eq_of_compatibleBoardO σ hb
  subst hbEq
  rw [hμ]
  by_contra hne
  have hne' : (currentBoard h (σ h)).isNone = false := Bool.eq_false_iff.2 hne
  have hinv := hr.inv
  have hpos := emptyCount_pos hgame
  obtain ⟨m, hm⟩ : ∃ m, 10 - h.length = m + 1 := ⟨10 - h.length - 1, by omega⟩
  have := forcesDrawOFrom_of_reachableO σ hσ hr (m + 1) (by omega) (fun _ => (0, 0))
  rw [playPayoffO_illegal_O _ _ _ _ hgame hne'] at this
  norm_num at this

lemma compatibleBoardO_after_memoryless_move
    (σ : Strategy) {b : Board} (hb : CompatibleBoardO σ O b)
    (hgame : gameOver b = false)
    (hlegal : (b (toMemorylessStrategy O σ b)).isNone = true) :
    CompatibleBoardO σ X
      (Function.update b (toMemorylessStrategy O σ b) (some O)) := by
  obtain ⟨h, hr, hbEq, hμ⟩ := toMemorylessStrategy_eq_of_compatibleBoardO σ hb
  have hNone : (currentBoard h (σ h)).isNone = true := by
    simpa [hbEq, hμ] using hlegal
  refine ⟨h ++ [Function.update (currentBoard h) (σ h) (some O)],
    ReachableO.oMove hr (by simpa [hbEq] using hgame) hNone, ?_⟩
  simp [currentBoard, hbEq, hμ]

lemma compatibleBoardO_after_x_move
    (σ : Strategy) {b : Board} (hb : CompatibleBoardO σ X b)
    (hgame : gameOver b = false) (pos : Position)
    (hlegal : (b pos).isNone = true) :
    CompatibleBoardO σ O (Function.update b pos (some X)) := by
  obtain ⟨h, hr, rfl⟩ := hb
  exact ⟨h ++ [Function.update (currentBoard h) pos (some X)],
    ReachableO.xMove hr hgame pos hlegal, by simp [currentBoard]⟩

/-- Dual of `forcesDrawXFrom_memoryless_of_compatible`. -/
lemma forcesDrawOFrom_memoryless_of_compatible
    (σ : Strategy) (hσ : IsSecurityO σ) :
    ∀ n turn (h : History), CompatibleBoardO σ turn (currentBoard h) →
      ForcesDrawOFrom (asStrategy (toMemorylessStrategy O σ)) n turn h := by
  intro n
  induction n with
  | zero =>
      intro turn h hc σx
      have hX := not_hasWon_X_of_compatibleBoardO σ hσ hc
      simp only [playPayoffO, playAccordingToStrategy]
      exact payoffO_nonneg hX
  | succ n ih =>
      intro turn h hc σx
      by_cases hg : gameOver (currentBoard h) = true
      · have hX := not_hasWon_X_of_compatibleBoardO σ hσ hc
        rw [playPayoffO_gameOver _ _ _ _ _ hg]
        exact payoffO_nonneg hX
      · have hg' : gameOver (currentBoard h) = false := by simpa using hg
        rcases player_cases turn with rfl | rfl
        · by_cases hl : (currentBoard h (σx h)).isNone = true
          · rw [playPayoffO_step_X _ _ _ _ hg' hl]
            refine ih O _ ?_ σx
            rw [currentBoard_append_singleton]
            exact compatibleBoardO_after_x_move σ hc hg' _ hl
          · have hl' : (currentBoard h (σx h)).isNone = false := Bool.eq_false_iff.2 hl
            rw [playPayoffO_illegal_X _ _ _ _ hg' hl']
            norm_num
        · have hl := toMemorylessStrategy_legal_of_compatibleBoardO σ hσ hc hg'
          rw [playPayoffO_step_O _ _ _ _ hg' hl]
          refine ih X _ ?_ σx
          rw [currentBoard_append_singleton]
          exact compatibleBoardO_after_memoryless_move σ hc hg' hl

theorem isSecurityO_toMemorylessStrategy (σ : Strategy) (hσ : IsSecurityO σ) :
    IsSecurityO (asStrategy (toMemorylessStrategy O σ)) := by
  rw [playPayoffO_isSecurityO]
  exact forcesDrawOFrom_memoryless_of_compatible σ hσ 9 X [emptyBoard]
    (compatibleBoardO_empty σ)

/-- Replacing X's strategy by its memoryless projection preserves Nash equilibrium. -/
theorem isNash_toMemorylessOne_X
    (σ : StrategyProfile) (hσ : ticTacToe.IsNash σ) :
    ticTacToe.IsNash (toMemorylessOne σ X) := by
  rw [isNash_iff_isSecurity] at hσ ⊢
  refine ⟨?_, ?_⟩
  · simpa [toMemorylessOne, Function.update_self] using
      isSecurityX_toMemorylessStrategy (σ X) hσ.1
  · intro τ
    have h := hσ.2 τ
    have hupd :
        (fun p ↦ if p = O then toMemorylessOne σ X O else τ) =
          (fun p ↦ if p = O then σ O else τ) := by
      funext p; fin_cases p <;> simp [toMemorylessOne, X, O]
    simpa [hupd] using h

/-- Replacing O's strategy by its memoryless projection preserves Nash equilibrium. -/
theorem isNash_toMemorylessOne_O
    (σ : StrategyProfile) (hσ : ticTacToe.IsNash σ) :
    ticTacToe.IsNash (toMemorylessOne σ O) := by
  rw [isNash_iff_isSecurity] at hσ ⊢
  refine ⟨?_, ?_⟩
  · intro τ
    have h := hσ.1 τ
    have hupd :
        (fun p ↦ if p = X then toMemorylessOne σ O X else τ) =
          (fun p ↦ if p = X then σ X else τ) := by
      funext p; fin_cases p <;> simp [toMemorylessOne, X, O]
    simpa [hupd] using h
  · simpa [toMemorylessOne, Function.update_self] using
      isSecurityO_toMemorylessStrategy (σ O) hσ.2

/-- Replacing either player's strategy by its memoryless projection preserves Nash. -/
theorem isNash_toMemorylessOne
    (σ : StrategyProfile) (hσ : ticTacToe.IsNash σ) (i : Player) :
    ticTacToe.IsNash (toMemorylessOne σ i) := by
  fin_cases i
  · exact isNash_toMemorylessOne_X σ hσ
  · exact isNash_toMemorylessOne_O σ hσ

/-- In particular, projecting both players (sequentially) yields a memoryless Nash. -/
theorem isNash_toMemoryless
    (σ : StrategyProfile) (hσ : ticTacToe.IsNash σ) :
    ticTacToe.IsNash (toMemoryless σ) := by
  have hX := isNash_toMemorylessOne_X σ hσ
  have hBoth := isNash_toMemorylessOne_O (toMemorylessOne σ X) hX
  convert hBoth
  funext p
  fin_cases p <;> simp [toMemoryless, toMemorylessOne, X, O]


end MathEconLibExamples.GameTheory.TicTacToe
end
