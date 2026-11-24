/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

import MathEconLibExamples.GeneralEquilibrium.PureExchange.Linear

/-!
# Pure-exchange example regressions

The canonical two-household example supplies the preference and all regularity proofs.
These checks retain exact clearing and nonunique full-budget demand without copying that model.
-/

set_option linter.privateModule false

open scoped BigOperators
open MathEconLib.RevealedPreference MathEconLib.GeneralEquilibrium.PureExchange
open MathEconLib.GeneralEquilibrium.PureExchange.Examples.Linear

example :
    ∃ (p : Bundle 2) (x : Fin 2 → Orthant 2),
      IsWalrasianEquilibrium endowment (fun _ => sumPreference) p x ∧
      (∑ k, p k) = 1 ∧ (∀ k, 0 < p k) ∧
      (∀ i, dot p (x i).val = 1) ∧ (∀ k, ∑ i, (x i).val k = 2) :=
  exists_equilibrium

example :
    leftChoice ≠ rightChoice ∧
      leftChoice ∈ demand sumPreference (1 : Bundle 2) halfPrice ∧
      rightChoice ∈ demand sumPreference (1 : Bundle 2) halfPrice ∧
      sumPreference.le leftChoice rightChoice ∧ sumPreference.le rightChoice leftChoice :=
  distinct_tied_demand

example : ¬ (demand sumPreference (1 : Bundle 2) halfPrice).Subsingleton :=
  demand_not_subsingleton
