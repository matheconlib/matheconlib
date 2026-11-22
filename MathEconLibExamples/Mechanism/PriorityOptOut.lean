/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Choice.FiniteOption
public import MathEconLib.GameTheory.Strategic.OutcomeIncentives
public import MathEconLib.Preferences.Basic
public import Mathlib.Basic.Real.Basic

/-!
# Ordinal priority allocation with opt-out

Two agents report strict rankings of two objects and the outside option. The first agent chooses
from both objects; the second chooses from the objects left by the first. Both menus always include
opt-out and are independent of the choosing agent's report. Truthful reporting is dominant under
the fixed true ordinal ranking, by the public outcome-game incentive API and finite-menu selector.

The six rankings allow opt-out at every position. Numerical ranks only encode these finite orders;
the dominance proof uses their ordinal best-choice property. No transfers, prior, matching stability
claim or new participation predicate is introduced.
-/

@[expose] public section

namespace MathEconLibExamples.Mechanism.PriorityOptOut

open MathEconLib MathEconLib.GameTheory MathEconLib.Preferences
open MathEconLib.Choice.ChoiceFunction

/-- The fixed priority order is first agent, then second agent. -/
inductive Agent
  | first
  | second
  deriving DecidableEq

/-- Each agent can receive at most one of the two physical objects. -/
inductive Object
  | a
  | b
  deriving DecidableEq

instance : Fintype Object := ⟨{.a, .b}, by intro o; cases o <;> simp⟩

/-- All strict rankings, named from best to worst; `None` denotes opt-out. -/
inductive Ranking
  | abNone
  | aNoneB
  | baNone
  | bNoneA
  | noneAB
  | noneBA
  deriving DecidableEq

/-- Ordinal positions are 2 for best, 1 for middle, and 0 for worst. -/
def rank : Ranking → Option Object → Fin 3
  | .abNone, some .a => 2
  | .abNone, some .b => 1
  | .abNone, none => 0
  | .aNoneB, some .a => 2
  | .aNoneB, some .b => 0
  | .aNoneB, none => 1
  | .baNone, some .a => 1
  | .baNone, some .b => 2
  | .baNone, none => 0
  | .bNoneA, some .a => 0
  | .bNoneA, some .b => 2
  | .bNoneA, none => 1
  | .noneAB, some .a => 1
  | .noneAB, some .b => 0
  | .noneAB, none => 2
  | .noneBA, some .a => 0
  | .noneBA, some .b => 1
  | .noneBA, none => 2

theorem rank_injective (r : Ranking) : Function.Injective (rank r) := by
  cases r <;> decide

/-- The reported strict order, with larger alternatives preferred. -/
@[instance_reducible] def preference (r : Ranking) : LinearOrder (Option Object) :=
  LinearOrder.lift' (rank r) (rank_injective r)

/-- The same ranking through the existing ordinal preference interface. -/
def ordinalPreference (r : Ranking) : Preference (Option Object) :=
  Preference.ofPreorder (preference r).toPreorder

/-- Strict ordinal comparison agrees with strict comparison of ordinal positions. -/
theorem ordinalPreference_lt_iff (r : Ranking) (x y : Option Object) :
    (ordinalPreference r).lt x y ↔ rank r x < rank r y :=
  (lt_iff_le_not_ge : rank r x < rank r y ↔
    rank r x ≤ rank r y ∧ ¬rank r y ≤ rank r x).symm

/-- True types and reports use the same full product of strict rankings. -/
abbrev Reports := Agent → Ranking

/-- The first agent chooses its reported favorite, including the possibility of exit. -/
def firstChoice (r : Reports) : Option Object :=
  bestOption (preference (r .first)) Finset.univ

/-- Objects available to each agent; choosing opt-out consumes no physical object. -/
def menu (r : Reports) : Agent → Finset Object
  | .first => Finset.univ
  | .second => Finset.univ.filter (fun o ↦ some o ≠ firstChoice r)

/-- Each agent chooses its reported best available object or opt-out. -/
def allocation (r : Reports) (i : Agent) : Option Object :=
  bestOption (preference (r i)) (menu r i)

/-- An agent's feasible menu does not change when only that agent changes its report. -/
theorem menu_update_self (r : Reports) (i : Agent) (s : Ranking) :
    menu (Function.update r i s) i = menu r i := by
  cases i <;> simp [menu, firstChoice]
  rfl

/-- The outcome-only game has no dummy transfers or numerical payoff requirement. -/
def game : OutcomeGame Agent (fun _ ↦ Ranking) (Agent → Option Object) where
  outcome := allocation

/-- Evaluate assigned alternatives using true rankings, held fixed under report changes. -/
def comparison (i : Agent) (θ : Reports) (x y : Agent → Option Object) : Prop :=
  (ordinalPreference (θ i)).le (x i) (y i)

/-- Intended play reports the true ranking. -/
def truthful (_ : Agent) : Ranking → Ranking := id

/-- Truth is dominant at every opponent report, directly under the true ordinal comparison. -/
theorem truthful_isDominantStrategyWith : game.IsDominantStrategyWith comparison truthful := by
  apply (game.isDominantStrategyWith_iff comparison truthful).2
  intro θ i r
  change (preference (θ i)).le (bestOption (preference (r i)) (menu r i))
    (bestOption (preference ((Function.update r i (θ i)) i))
      (menu (Function.update r i (θ i)) i))
  simp only [Function.update_self, menu_update_self]
  exact le_bestOption (preference (θ i)) (menu r i)
    (bestOption_mem (preference (r i)) (menu r i))

/-- Opt-out belongs to every feasible menu, under every report profile. -/
theorem optOut_available (r : Reports) (i : Agent) : none ∈ optionMenu (menu r i) :=
  none_mem_optionMenu (menu r i)

/-- The allocation is a member of the agent's actual feasible menu. -/
theorem allocation_mem (r : Reports) (i : Agent) :
    allocation r i ∈ optionMenu (menu r i) :=
  bestOption_mem (preference (r i)) (menu r i)

/-- A physical object allocated to the first agent cannot also go to the second. -/
theorem no_double_assignment (r : Reports) (o : Object)
    (hfirst : allocation r .first = some o) : allocation r .second ≠ some o := by
  intro hsecond
  have hmem : o ∈ menu r .second :=
    some_mem_optionMenu.mp (hsecond ▸ allocation_mem r .second)
  exact (Finset.mem_filter.mp hmem).2 hfirst.symm

/-- If the first agent exits, both physical objects remain available to the second. -/
theorem menu_when_first_exits (r : Reports) (h : firstChoice r = none) :
    menu r .second = Finset.univ := by
  simp [menu, h]

/-- Truthful choice weakly exceeds exit; this is a comparison, not a new IR predicate. -/
theorem optOut_le_truthful (θ : Reports) (i : Agent) :
    (ordinalPreference (θ i)).le none (allocation θ i) :=
  le_bestOption (preference (θ i)) (menu θ i) (optOut_available θ i)

/-- The public dominance-to-Nash implication applies to this same ordinal client. -/
theorem truthful_isExPostNashWith : game.IsExPostNashWith comparison truthful :=
  truthful_isDominantStrategyWith.isExPostNashWith

/-- Real-valued ordinal positions, with opt-out's actual position retained. -/
def rankUtility (i : Agent) (θ : Reports) (x : Agent → Option Object) : ℝ :=
  (rank (θ i) (x i)).val

/-- The ranking utility exactly preserves and reflects the true weak comparison. -/
theorem comparison_iff_rankUtility (i : Agent) (θ : Reports)
    (x y : Agent → Option Object) :
    comparison i θ x y ↔ rankUtility i θ x ≤ rankUtility i θ y := by
  change (rank (θ i) (x i)).val ≤ (rank (θ i) (y i)).val ↔
    ((rank (θ i) (x i)).val : ℝ) ≤ ((rank (θ i) (y i)).val : ℝ)
  exact Nat.cast_le.symm

/-- The utility game uses exactly the same outcome rule and fixed true ranking. -/
def utilityGame (θ : Reports) : StrategicGame Agent (fun _ ↦ Ranking) ℝ :=
  StrategicGame.ofOutcome game { payoff := fun i ↦ rankUtility i θ }

/-- The named representation bridge identifies ordinal and utility-game dominance. -/
theorem ordinal_iff_utility_dominant :
    game.IsDominantStrategyWith comparison truthful ↔
      ∀ θ i, StrategicGame.Strategy.IsDominant (G := utilityGame θ) (i := i)
        (truthful i (θ i)) :=
  game.isDominantStrategyWith_iff_isDominant_of_representation comparison rankUtility
    comparison_iff_rankUtility truthful

/-- The same truthful strategy is dominant in every fixed-true-type utility game. -/
theorem truthful_isDominant :
    ∀ θ i, StrategicGame.Strategy.IsDominant (G := utilityGame θ) (i := i)
      (truthful i (θ i)) :=
  ordinal_iff_utility_dominant.mp truthful_isDominantStrategyWith

/-- Apply the named public dominance result to any report profile at fixed true rankings. -/
theorem report_le_truthful (θ r : Reports) (i : Agent) :
    comparison i θ (allocation r) (allocation (Function.update r i (θ i))) :=
  (game.isDominantStrategyWith_iff comparison truthful).mp truthful_isDominantStrategyWith θ i r

/-- Both agents truly prefer A to exit and exit to B. -/
def trueProfile : Reports := fun _ ↦ .aNoneB

/-- Only the first agent falsely reports B above A above exit. -/
def falseProfile : Reports := Function.update trueProfile .first .baNone

/-- The first agent truthfully takes A. -/
theorem truthful_first : allocation trueProfile .first = some .a := by
  decide

/-- The second agent exits after its favorite A is taken. -/
theorem truthful_second_exits : allocation trueProfile .second = none := by
  decide

/-- B remains physically available to the second agent, despite its decision to exit. -/
theorem leftover_available : some Object.b ∈ optionMenu (menu trueProfile .second) := by
  decide

/-- Under the second agent's true ranking, the leftover B is strictly worse than exit. -/
theorem leftover_below_exit :
    (ordinalPreference (trueProfile .second)).lt (some .b) none := by
  simp only [ordinalPreference_lt_iff]
  decide

/-- The first agent's specified false report assigns B to that agent. -/
theorem deviating_first : allocation falseProfile .first = some .b := by
  decide

/-- Dominance, applied to the specified false report, still evaluates the true ranking. -/
theorem first_deviation_le_truthful :
    comparison .first trueProfile (allocation falseProfile) (allocation trueProfile) := by
  have h := report_le_truthful trueProfile falseProfile .first
  simpa only [falseProfile, Function.update_idem, Function.update_eq_self] using h

/-- The false report's B is strictly worse than truthful A under the unchanged true ranking. -/
theorem first_deviation_lt_truthful :
    (ordinalPreference (trueProfile .first)).lt
      (allocation falseProfile .first) (allocation trueProfile .first) := by
  simp only [ordinalPreference_lt_iff]
  decide

/-- The false report's B is also strictly worse than exit under that same true ranking. -/
theorem first_deviation_lt_exit :
    (ordinalPreference (trueProfile .first)).lt (allocation falseProfile .first) none := by
  simp only [ordinalPreference_lt_iff]
  decide

/-- Substituting the report for the true ranking would reverse both strict comparisons. -/
theorem reported_ranking_reverses_comparisons :
    (ordinalPreference (falseProfile .first)).lt
      (allocation trueProfile .first) (allocation falseProfile .first) ∧
    (ordinalPreference (falseProfile .first)).lt none (allocation falseProfile .first) := by
  simp only [ordinalPreference_lt_iff]
  decide

/-- Opt-out's rank can be zero, one or two; it is not normalized away. -/
theorem optOut_rank_positions :
    rank .abNone none = 0 ∧ rank .aNoneB none = 1 ∧ rank .noneAB none = 2 := by
  decide

end MathEconLibExamples.Mechanism.PriorityOptOut
