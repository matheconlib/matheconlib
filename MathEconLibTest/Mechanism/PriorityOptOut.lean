/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib
public import MathEconLibExamples.Mechanism.PriorityOptOut

/-!
# Public ordinal priority-client regressions

Consume the single canonical example. The public dominance theorem compares arbitrary reports at
unchanged true rankings. The concrete false report is worse than truthful choice and exit, whereas
substituting the false ranking reverses both comparisons. Opt-out retains its actual ordinal rank.
-/

@[expose] public section

namespace MathEconLibTest.Mechanism.PriorityOptOut

open MathEconLib.GameTheory
open MathEconLibExamples.Mechanism.PriorityOptOut

example : game.IsDominantStrategyWith comparison truthful := truthful_isDominantStrategyWith

example (θ r : Reports) (i : Agent) :
    comparison i θ (allocation r) (allocation (Function.update r i (θ i))) :=
  report_le_truthful θ r i

example : game.IsExPostNashWith comparison truthful := truthful_isExPostNashWith

example (θ : Reports) (i : Agent) :
    StrategicGame.Strategy.IsDominant (G := utilityGame θ) (i := i) (truthful i (θ i)) :=
  truthful_isDominant θ i

example (r : Reports) (i : Agent) (s : Ranking) :
    menu (Function.update r i s) i = menu r i := menu_update_self r i s

example (r : Reports) (i : Agent) :
    none ∈ MathEconLib.Choice.ChoiceFunction.optionMenu (menu r i) := optOut_available r i

example (r : Reports) (o : Object) (h : allocation r .first = some o) :
    allocation r .second ≠ some o := no_double_assignment r o h

example : allocation trueProfile .first = some .a ∧ allocation trueProfile .second = none :=
  ⟨truthful_first, truthful_second_exits⟩

example : some Object.b ∈ MathEconLib.Choice.ChoiceFunction.optionMenu (menu trueProfile .second) :=
  leftover_available

example : comparison .first trueProfile (allocation falseProfile) (allocation trueProfile) :=
  first_deviation_le_truthful

-- The true ranking rejects preferring the false-report allocation to either truth or exit.
example : ¬comparison .first trueProfile (allocation trueProfile) (allocation falseProfile) :=
  first_deviation_lt_truthful.2

example : ¬(ordinalPreference (trueProfile .first)).le none (allocation falseProfile .first) :=
  first_deviation_lt_exit.2

-- Using the reported ranking instead would incorrectly reverse both comparisons.
example : comparison .first falseProfile (allocation trueProfile) (allocation falseProfile) :=
  reported_ranking_reverses_comparisons.1.1

example : (ordinalPreference (falseProfile .first)).le none (allocation falseProfile .first) :=
  reported_ranking_reverses_comparisons.2.1

example : rank .abNone none = 0 ∧ rank .aNoneB none = 1 ∧ rank .noneAB none = 2 :=
  optOut_rank_positions

example (θ : Reports) (i : Agent) (x y : Agent → Option Object) :
    comparison i θ x y ↔ rankUtility i θ x ≤ rankUtility i θ y :=
  comparison_iff_rankUtility i θ x y

end MathEconLibTest.Mechanism.PriorityOptOut
