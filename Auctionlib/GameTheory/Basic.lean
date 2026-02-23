module

public import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Basic game-theoretic concepts

WIP.

In this file we set up basic game-theoretic concepts. We focus on normal-form games so far, i.e.
games that are simply given by a function assigning outcomes to combinations of strategies instead
detailed descriptions in terms of turns and states. Even so, there are still a lot of things to
consider for finding the right implementation:
* do we want games to include utility functions for each player or just a type of outcomes?
  We have gone with the latter approach for now, but maybe it would make sense to switch.
* What about nondeterministic games? These can currently be modelled as games whose outcome type is
  `MeasureTheory.ProbabilityMeasure α` for some measurable space `α`, but another option would be to
  directly define a game as something that assigns probability measures on the outcome space to
  strategy combinations.
* What about mixed / nondeterministic strategies? We could model this by constructing from any game
  with strategy types `A i` and outcome type `O` a game with strategy types
  `MeasureTheory.ProbabilityMeasure (A i)` and outcome type `MeasureTheory.ProbabilityMeasure O`,
  but then applying this to a game that was already nondeterministic would result in the outcome
  type `MeasureTheory.ProbabilityMeasure (MeasureTheory.ProbabilityMeasure O)`, forcing us to go
  through the Giry monad.
* At what point do we want to impose measurability conditions? In the definition of games already,
  or only later?

## Main definitions / results
* `Game A O`: a normal-form game with strategy types `A i` and an outcome type `O`, given
  simply by a function `((i : ι) → A i) → O`.
* `G.Strategy u i`: a type synonym for the type `A i` of strategies available to player `i` in the
  game `G`. This takes in a utility function `u` and is then equipped with the preorder given by
  weak dominance with respect to `u`.
* `Strategy.IsDominant s`: a strategy is called weakly dominant if it weakly dominates every other
  strategy, i.e. if it is a top element with respect to the order we put on `G.Strategy u i`.
* `Strategy.IsStrictlyDominant s`: a strategy is called weakly dominant if it strictly dominates
  every other strategy, i.e. if it is the only top element with respect to the order we put on
  `G.Strategy u i`.
* `G.IsNashEquilibrium u a`: a family of strategies `a i` is called a Nash equilibrium with respect
  to a family of utility functions `u i` if no player benefits from changing their strategy.
* `G.IsStrictNashEquilibrium u a`: a family of strategies `a i` is called a strict Nash equilibrium
  with respect to a family of utility functions `u i` if every player would incur a utility loss by
  changing their strategy.
* `isNashEquilibrium_of_isDominant`: any family of weakly dominant strategies is a Nash equilibrium.
  The analogous statement for strictly dominant strategies and strict Nash equilibria does not hold.
* `G.IsStrongNashEquilibrium u a`: a family of strategies `a i` is called a strong Nash equilibrium
  with respect to a family of utility functions `u i` if no coalition can form and change their
  strategies in a way that would strictly benefit each of its members.

-/

namespace GameTheory

/-- A deterministic normal-form game, given by a type `ι` of players, a type `A i` of pure
strategies for each player `i`, a type `O` of outcomes and a function that assigns
each combination `a : (i : ι) → A i` of strategies an outcome. We implement this
using an unbundled approach, so only the outcome-assigning function is actually
part of the structure. -/
structure Game {ι : Type*} (A : ι → Type*) (O : Type*) where
  outcome (a : (i : ι) → A i) : O

namespace Game

variable {ι : Type*} {A : ι → Type*} {O : Type*}

section Strategies

set_option linter.unusedVariables false in
/-- A type synonym for the type `A i` of pure strategies available to player `i` in the game
`G : Game A O`, equipped with the preorder given by weak dominance with respect to a given
utility function `u`. -/
def Strategy (G : Game A O) {O' : Type*} (u : O → O') (i : ι) := A i

namespace Strategy

instance (G : Game A O) {O' : Type*} [LE O'] (u : O → O') (i : ι) :
    LE (G.Strategy u i) where
  le s s' := ∀ (a a' : (i : ι) → A i),
    a i = s → a' i = s' → (∀ j ≠ i, a j = a' j) → u (G.outcome a) ≤ u (G.outcome a')

protected lemma le_def {G : Game A O} {O' : Type*} [LE O'] {u : O → O'} {i : ι}
    {s s' : G.Strategy u i} : s ≤ s' ↔ ∀ (a a' : (i : ι) → A i),
      a i = s → a' i = s' → (∀ j ≠ i, a j = a' j) → u (G.outcome a) ≤ u (G.outcome a') :=
  Iff.rfl

protected lemma le_iff [DecidableEq ι] {G : Game A O} {O' : Type*} [LE O']
    {u : O → O'} {i : ι} {s s' : G.Strategy u i} : s ≤ s' ↔ ∀ (a a' : (i : ι) → A i),
      a i = s → a' = Function.update a i s' → u (G.outcome a) ≤ u (G.outcome a') := by
  simp only [le_def, Function.eq_update_iff, and_imp, eq_comm]

protected lemma le_iff' [DecidableEq ι] {G : Game A O} {O' : Type*} [LE O']
    {u : O → O'} {i : ι} {s s' : G.Strategy u i} : s ≤ s' ↔ ∀ a : (i : ι) → A i,
      u (G.outcome (Function.update a i s)) ≤ u (G.outcome (Function.update a i s')) := by
  rw [le_iff]
  refine ⟨fun h a ↦ h _ _ (by simp) (by simp), fun h a a' ha ha' ↦ ?_⟩
  rw [Function.eq_update_self_iff.2 ha, ha']
  exact h a

instance (G : Game A O) {O' : Type*} [Preorder O'] (u : O → O') (i : ι) :
    Preorder (G.Strategy u i) where
  le_refl s a a' hai hai' h := Eq.le <| by congr; grind
  le_trans s s' s'' := by
    classical
    simp_rw [le_iff']
    grind

/-- A strategy strictly dominates another iff it weakly dominates it and there is at least one
scenario in which it is strictly better. -/
protected lemma lt_iff [DecidableEq ι] {G : Game A O} {O' : Type*} [Preorder O']
      {u : O → O'} {i : ι} {s s' : G.Strategy u i} : s < s' ↔ s ≤ s' ∧ ∃ a : (i : ι) → A i,
      u (G.outcome (Function.update a i s)) < u (G.outcome (Function.update a i s')) := by
    refine lt_iff_le_not_ge.trans <| and_congr_right fun h ↦ ?_
    simp only [le_iff', not_forall, lt_iff_le_not_ge, le_iff'.1 h, true_and]

/-- A strategy is called weakly dominant iff it weakly dominates every strategy. -/
def IsDominant {G : Game A O} {O' : Type*} [LE O']
    {u : O → O'} {i : ι} (s : G.Strategy u i) := IsTop s

/-- A strategy is called strictly dominant iff it strictly dominates every other strategy. -/
def IsStrictlyDominant {G : Game A O} {O' : Type*} [Preorder O']
    {u : O → O'} {i : ι} (s : G.Strategy u i) := ∀ s' ≠ s, s' < s

lemma IsStrictlyDominant.isDominant {G : Game A O} {O' : Type*} [Preorder O']
    {u : O → O'} {i : ι} {s : G.Strategy u i} (hs : s.IsStrictlyDominant) : s.IsDominant := by
  intro s'
  by_cases h : s' = s
  · exact h.le
  · exact (hs _ h).le

end Strategy

end Strategies

section Equilibria

/-- A family of strategies `a i` is called a Nash equilibrium with respect to a family
of utility functions `u i` if no player can benefit from changing their strategy. -/
def IsNashEquilibrium [DecidableEq ι] (G : Game A O) {O' : ι → Type*} [∀ i, LE (O' i)]
    (u : (i : ι) → O → O' i) (a : (i : ι) → A i) :=
  ∀ i (s : A i), u i (G.outcome (Function.update a i s)) ≤ u i (G.outcome a)

/-- A family of strategies `a i` is called a strict Nash equilibrium with respect to a family
of utility functions `u i` if every player would suffer a loss when changing their strategy. -/
def IsStrictNashEquilibrium [DecidableEq ι] (G : Game A O) {O' : ι → Type*} [∀ i, Preorder (O' i)]
    (u : (i : ι) → O → O' i) (a : (i : ι) → A i) :=
  ∀ i, ∀ s ≠ a i, u i (G.outcome (Function.update a i s)) < u i (G.outcome a)

/-- Every strict Nash equilibrium is a Nash equilibrium. -/
lemma IsStrictNashEquilibrium.isNashEquilibrium [DecidableEq ι] {G : Game A O} {O' : ι → Type*}
    [∀ i, Preorder (O' i)] {u : (i : ι) → O → O' i} {a : (i : ι) → A i}
    (ha : G.IsStrictNashEquilibrium u a) : G.IsNashEquilibrium u a := by
  intro i s
  by_cases h : s = a i
  · simp [h]
  · exact (ha i s h).le

/-- Any family of weakly dominant strategies is a nash equilibrium. Note however that the
corresponding statement for strictly dominant strategies and strict nash equilibria isn't true. -/
lemma isNashEquilibrium_of_isDominant [DecidableEq ι] {G : Game A O} {O' : ι → Type*}
    [∀ i, LE (O' i)] {u : (i : ι) → O → O' i} {a : (i : ι) → A i}
    (ha : ∀ i, Strategy.IsDominant (G := G) (u := u i) (a i)) : G.IsNashEquilibrium u a :=
  fun i s ↦ ha i s _ _ (by simp) rfl (by grind)

/-- A family of strategies `a i` is called a strong Nash equilibrium if every other strategy leaves
at least one player who changed their strategy no better off than they were before, i.e. if it is
impossible for a coalition to form that strictly benefits each of its members. -/
def IsStrongNashEquilibrium (G : Game A O) {O' : ι → Type*} [∀ i, Preorder (O' i)]
    (u : (i : ι) → O → O' i) (a : (i : ι) → A i) :=
  ∀ a' ≠ a, ∃ i, a i ≠ a' i ∧ u i (G.outcome a') ≤ u i (G.outcome a)

/-- Every strong Nash equilibrium is a Nash equilibrium. -/
lemma IsStrongNashEquilibrium.isNashEquilibrium [DecidableEq ι] {G : Game A O} {O' : ι → Type*}
    [∀ i, Preorder (O' i)] {u : (i : ι) → O → O' i} {a : (i : ι) → A i}
    (ha : G.IsStrongNashEquilibrium u a) : G.IsNashEquilibrium u a := by
  intro i s
  by_cases h : s = a i
  · simp [h]
  · have ⟨j, hj, hj'⟩ := ha (Function.update a i s) (by simp [h])
    replace hj : j = i := by grind
    rwa [hj] at hj'

end Equilibria

end Game

end GameTheory
