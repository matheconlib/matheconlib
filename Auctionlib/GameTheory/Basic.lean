module

public import Auctionlib.ForMathlib.ProbabilityMeasure

/-!
# Basic game-theoretic concepts

WIP.

In this file we set up basic game-theoretic concepts. We focus on normal-form games so far, i.e.
games that are simply given by a function assigning outcomes to combinations of strategies instead
detailed descriptions in terms of turns and states. Even so, there are still a lot of things to
consider for finding the right implementation:
* Do we want games to include utility functions for each player or just a type of outcomes?
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
* Should we go with a bundled or an unbundled approach? Currently we use the latter, but it seems
  that for many types like the type of strategies and the type of joint strategies we will need
  to set up type synonyms anyway to work with e.g. weak dominance of strategies as a preorder
  without conflicting with existing preorders on the strategy types.

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
* `G.Measurable`: typeclass stating that the action spaces and outcome space of `G` are measurable
  spaces, and that the outcome function `G.outcome` is measurable
* `G.toMixed`: the game whose pure strategies are the mixed strategies of `G`, and whose outcome
  space is the space of probability distributions on the outcome space of `G`. This enables us to
  use the same API for pure and mixed strategies, by treating mixed strategies as pure strategies
  of `G.toMixed`.
* `G.toMixed'`: a variant of `G.toMixed` for when the outcome space of `G` is already a space of
  probability distributions.
* When `G` is measurable, `G.toMixed` and `G.toMixed'` are as well.
-/

@[expose] public section

namespace GameTheory

/-- A deterministic normal-form game, given by a type `ι` of players, a type `A i` of pure
strategies for each player `i`, a type `O` of outcomes and a function that assigns
each combination `a : (i : ι) → A i` of strategies an outcome. We implement this
using an unbundled approach, so only the outcome-assigning function is actually
part of the structure. -/
structure Game {ι : Type*} (A : ι → Type*) (O : Type*) where
  outcome (a : (i : ι) → A i) : O

/-- We say that a payoff structure on a type `O` with respect to `ι` is simply an `ι`-indexed family
of payoff functions `O → ℝ`. Usually `O` will be the type of outcomes of a game with players `ι`. -/
structure PayoffStructure (O : Type*) (ι : Type*) where
  payoff (i : ι) : O → ℝ

variable {ι : Type*} {A : ι → Type*} {O : Type*}

namespace Game

section Strategies

set_option linter.unusedVariables false in
/-- A type synonym for the type `A i` of pure strategies available to player `i` in the game
`G : Game A O`, equipped with the preorder given by weak dominance with respect to the payoff
structure `P`. -/
def Strategy (G : Game A O) (P : PayoffStructure O ι) (i : ι) := A i

namespace Strategy

instance (G : Game A O) (P : PayoffStructure O ι) (i : ι) :
    LE (G.Strategy P i) where
  le s s' := ∀ (a a' : (i : ι) → A i), a i = s → a' i = s' → (∀ j ≠ i, a j = a' j) →
    P.payoff i (G.outcome a) ≤ P.payoff i (G.outcome a')

protected lemma le_def {G : Game A O} {P : PayoffStructure O ι} {i : ι} {s s' : G.Strategy P i} :
    s ≤ s' ↔ ∀ (a a' : (i : ι) → A i), a i = s → a' i = s' → (∀ j ≠ i, a j = a' j) →
      P.payoff i (G.outcome a) ≤ P.payoff i (G.outcome a') :=
  Iff.rfl

protected lemma le_iff [DecidableEq ι] {G : Game A O} {P : PayoffStructure O ι} {i : ι}
    {s s' : G.Strategy P i} :
    s ≤ s' ↔ ∀ (a a' : (i : ι) → A i), a i = s → a' = Function.update a i s' →
      P.payoff i (G.outcome a) ≤ P.payoff i (G.outcome a') := by
  simp only [Strategy.le_def, Function.eq_update_iff, and_imp, eq_comm]

protected lemma le_iff' [DecidableEq ι] {G : Game A O} {P : PayoffStructure O ι} {i : ι}
    {s s' : G.Strategy P i} :
    s ≤ s' ↔ ∀ a : (i : ι) → A i, P.payoff i (G.outcome (Function.update a i s)) ≤
      P.payoff i (G.outcome (Function.update a i s')) := by
  rw [Strategy.le_iff]
  refine ⟨fun h a ↦ h _ _ (by simp) (by simp), fun h a a' ha ha' ↦ ?_⟩
  rw [Function.eq_update_self_iff.2 ha, ha']
  exact h a

instance (G : Game A O) (P : PayoffStructure O ι) (i : ι) :
    Preorder (G.Strategy P i) where
  le_refl s a a' hai hai' h := Eq.le <| by congr; grind
  le_trans s s' s'' := by
    classical
    simp_rw [Strategy.le_iff']
    grind

/-- A strategy strictly dominates another iff it weakly dominates it and there is at least one
scenario in which it is strictly better. -/
protected lemma lt_iff [DecidableEq ι] {G : Game A O} (P : PayoffStructure O ι) (i : ι)
    {s s' : G.Strategy P i} :
    s < s' ↔ s ≤ s' ∧ ∃ a : (i : ι) → A i, P.payoff i (G.outcome (Function.update a i s)) <
      P.payoff i (G.outcome (Function.update a i s')) := by
    refine lt_iff_le_not_ge.trans <| and_congr_right fun h ↦ ?_
    simp only [Strategy.le_iff', not_forall, lt_iff_le_not_ge, Strategy.le_iff'.1 h, true_and]

/-- A strategy is called weakly dominant iff it weakly dominates every strategy. -/
def IsDominant {G : Game A O} {P : PayoffStructure O ι} {i : ι} (s : G.Strategy P i) :=
  IsTop s

/-- A strategy is called strictly dominant iff it strictly dominates every other strategy. -/
def IsStrictlyDominant {G : Game A O} {P : PayoffStructure O ι} {i : ι} (s : G.Strategy P i) :=
  ∀ s' ≠ s, s' < s

lemma IsStrictlyDominant.isDominant {G : Game A O} {P : PayoffStructure O ι} {i : ι}
    {s : G.Strategy P i} (hs : s.IsStrictlyDominant) : s.IsDominant := by
  intro s'
  by_cases h : s' = s
  · exact h.le
  · exact (hs _ h).le

end Strategy

end Strategies

section Equilibria

/-- A family of strategies `a i` is called a Nash equilibrium with respect to a family
of utility functions `u i` if no player can benefit from changing their strategy. -/
def IsNashEquilibrium [DecidableEq ι] (G : Game A O) (P : PayoffStructure O ι)
    (a : (i : ι) → A i) :=
  ∀ i (s : A i), P.payoff i (G.outcome (Function.update a i s)) ≤ P.payoff i (G.outcome a)

/-- A family of strategies `a i` is called a strict Nash equilibrium with respect to a family
of utility functions `u i` if every player would suffer a loss when changing their strategy. -/
def IsStrictNashEquilibrium [DecidableEq ι] (G : Game A O) (P : PayoffStructure O ι)
    (a : (i : ι) → A i) :=
  ∀ i, ∀ s ≠ a i, P.payoff i (G.outcome (Function.update a i s)) < P.payoff i (G.outcome a)

/-- Every strict Nash equilibrium is a Nash equilibrium. -/
lemma IsStrictNashEquilibrium.isNashEquilibrium [DecidableEq ι] {G : Game A O}
    {P : PayoffStructure O ι} {a : (i : ι) → A i} (ha : G.IsStrictNashEquilibrium P a) :
    G.IsNashEquilibrium P a := by
  intro i s
  by_cases h : s = a i
  · simp [h]
  · exact (ha i s h).le

/-- Any family of weakly dominant strategies is a nash equilibrium. Note however that the
corresponding statement for strictly dominant strategies and strict nash equilibria isn't true. -/
lemma isNashEquilibrium_of_isDominant [DecidableEq ι] {G : Game A O} {P : PayoffStructure O ι}
    {a : (i : ι) → A i} (ha : ∀ i, Strategy.IsDominant (G := G) (P := P) (a i)) :
    G.IsNashEquilibrium P a :=
  fun i s ↦ ha i s _ _ (by simp) rfl (by grind)

/-- A family of strategies `a i` is called a strong Nash equilibrium if every other strategy leaves
at least one player who changed their strategy no better off than they were before, i.e. if it is
impossible for a coalition to form that strictly benefits each of its members. -/
def IsStrongNashEquilibrium (G : Game A O) (P : PayoffStructure O ι)
    (a : (i : ι) → A i) :=
  ∀ a' ≠ a, ∃ i, a i ≠ a' i ∧ P.payoff i (G.outcome a') ≤ P.payoff i (G.outcome a)

/-- Every strong Nash equilibrium is a Nash equilibrium. -/
lemma IsStrongNashEquilibrium.isNashEquilibrium [DecidableEq ι] {G : Game A O}
    {P : PayoffStructure O ι} {a : (i : ι) → A i}
    (ha : G.IsStrongNashEquilibrium P a) : G.IsNashEquilibrium P a := by
  intro i s
  by_cases h : s = a i
  · simp [h]
  · have ⟨j, hj, hj'⟩ := ha (Function.update a i s) (by simp [h])
    replace hj : j = i := by grind
    rwa [hj] at hj'

end Equilibria

end Game

section Measurable

open MeasureTheory

open scoped ProbabilityTheory

variable [∀ i, MeasurableSpace (A i)] [MeasurableSpace O]

namespace Game

/-- We call a game measurable if its action spaces and outcome space are measurable spaces, and
the outcome function `G.outcome : ((i : ι) → A i) → O` is measurable. -/
protected class Measurable (G : Game A O) where
  measurable_outcome : Measurable G.outcome

export Measurable (measurable_outcome)

/-- For any measurable game `G` with pure strategy spaces `A i` and outcome space `O`, this is a
game whose pure strategy spaces are the spaces `ProbabilityMeasure (A i)` of mixed strategies of
`G`, and whose outcome space is the space `ProbabilityMeasure O` of probability distributions on
`O`. This enables us to talk about pure and mixed strategies using the same API: a mixed strategy
for `G` is simply a pure strategy for `G.toMixed`.

Note that when `G` is already a nondeterministic game in the sense that it is of the form
`Game A (ProbabilityMeasure O)`, `G.toMixed` has the outcome type
`ProbabilityMeasure (ProbabilityMeasure O)`; you can avoid that by using `toMixed'` instead,
which takes games of the form `Game A (ProbabilityMeasure O)` to games of the form
`Game (fun i ↦ ProbabilityMeasure (A i)) (ProbabilityMeasure O)`.

TODO: find a more standard name for this. -/
@[simps]
noncomputable def toMixed (G : Game A O) [G.Measurable] [Fintype ι] :
    Game (fun i ↦ ProbabilityMeasure (A i)) (ProbabilityMeasure O) where
  outcome a := (ProbabilityMeasure.pi a).map G.measurable_outcome.aemeasurable

/-- For any measurable game `G` with pure strategy spaces `A i` and outcome space `O`, this is a
game whose pure strategy spaces are the spaces `ProbabilityMeasure (A i)` or mixed strategies of
`G`, and whose outcome space is the space `ProbabilityMeasure O` of probability distributions on
`O`. This enables us to talk about pure and mixed strategies using the same API: a mixed strategy
for `G` is simply a pure strategy for `G.toMixed`. -/
@[simps]
noncomputable def toMixed' (G : Game A (ProbabilityMeasure O)) [G.Measurable] [Fintype ι] :
    Game (fun i ↦ ProbabilityMeasure (A i)) (ProbabilityMeasure O) where
  outcome := ProbabilityMeasure.join ∘ G.toMixed.outcome

instance (G : Game A O) [G.Measurable] [Fintype ι] : G.toMixed.Measurable where
  measurable_outcome := (ProbabilityMeasure.measurable_map G.measurable_outcome).comp
    ProbabilityMeasure.measurable_pi

instance (G : Game A (ProbabilityMeasure O)) [G.Measurable] [Fintype ι] :
    G.toMixed'.Measurable where
  measurable_outcome :=
    (ProbabilityMeasure.measurable_join (α := O)).comp G.toMixed.measurable_outcome

end Game

namespace PayoffStructure

/-- We call a payoff structure measurable if its domain is a measurable space and the payoff
functions it consists of are all measurable. -/
protected class Measurable (P : PayoffStructure O ι) where
  measurable_payoff i : Measurable (P.payoff i)

/-- We call a payoff structure bounded if each payoff function is bounded. -/
protected class Bounded (P : PayoffStructure O ι) where
  isBounded_payoff_range i : Bornology.IsBounded (Set.range (P.payoff i))

export PayoffStructure.Measurable (measurable_payoff)

export PayoffStructure.Bounded (isBounded_payoff_range)

/-- The payoff structure on `ProbabilityMeasure O` induced by a payoff
structure on `O` via taking expected values. -/
noncomputable def toExpected (P : PayoffStructure O ι) :
    PayoffStructure (ProbabilityMeasure O) ι where
  payoff i μ := μ[P.payoff i]

instance (P : PayoffStructure O ι) [P.Measurable] [P.Bounded] : P.toExpected.Measurable where
  measurable_payoff i :=
    ProbabilityMeasure.measurable_integral (P.measurable_payoff i) (P.isBounded_payoff_range i)

instance (P : PayoffStructure O ι) [P.Bounded] : P.toExpected.Bounded where
  isBounded_payoff_range i := by
    have h := P.isBounded_payoff_range i
    simp_rw [isBounded_iff_forall_norm_le, Set.forall_mem_range] at h ⊢
    refine h.imp fun C hC μ ↦ ?_
    simpa using norm_integral_le_of_norm_le_const (μ := μ) <| .of_forall hC

end PayoffStructure

end Measurable

section Continuous

variable [∀ i, TopologicalSpace (A i)] [TopologicalSpace O]

namespace Game

/-- We call a game continuous if its action spaces and outcome space are topological spaces, and
the outcome function `G.outcome : ((i : ι) → A i) → O` is continuous. -/
protected class Continuous (G : Game A O) where
  continuous_outcome : Continuous G.outcome

export Continuous (continuous_outcome)

instance Continuous.instMeasurable [∀ i, MeasurableSpace (A i)] [MeasurableSpace O] [Countable ι]
    [∀ i, OpensMeasurableSpace (A i)] [∀ i, SecondCountableTopology (A i)] [BorelSpace O]
    (G : Game A O) [G.Continuous] : G.Measurable where
  measurable_outcome := continuous_outcome.measurable

instance [∀ i, MeasurableSpace (A i)] [MeasurableSpace O] [∀ i, OpensMeasurableSpace (A i)]
    [BorelSpace O] [∀ i, SecondCountableTopology (A i)]
    [∀ i, TopologicalSpace.PseudoMetrizableSpace (A i)] [Fintype ι] (G : Game A O)
    [G.Continuous] : G.toMixed.Continuous where
  continuous_outcome := (MeasureTheory.ProbabilityMeasure.continuous_map G.continuous_outcome).comp
      MeasureTheory.ProbabilityMeasure.continuous_pi

end Game

namespace PayoffStructure

/-- We call a payoff structure continuous if its domain is a topological space and the payoff
functions it consists of are all continuous. -/
protected class Continuous (P : PayoffStructure O ι) where
  continuous_payoff i : Continuous (P.payoff i)

export Continuous (continuous_payoff)

instance Continuous.instMeasurable [MeasurableSpace O] [OpensMeasurableSpace O]
    (P : PayoffStructure O ι) [P.Continuous] : P.Measurable where
  measurable_payoff i := (continuous_payoff i).measurable

instance (P : PayoffStructure O ι) [MeasurableSpace O] [OpensMeasurableSpace O] [CompactSpace O]
    [P.Continuous] : P.toExpected.Continuous where
  continuous_payoff i := MeasureTheory.ProbabilityMeasure.continuous_integral_continuousMap <|
    ContinuousMap.mk _ <| P.continuous_payoff i

end PayoffStructure

end Continuous

end GameTheory
