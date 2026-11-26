/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

import MathEconLibExamples.RevealedEquilibrium

/-!
# Revealed-equilibrium example regressions

These checks apply the canonical numerical examples. The separate `Equilibrium`
module pins the public API using only the revealed-preference umbrella.
-/

set_option linter.privateModule false

open MathEconLib.RevealedPreference MathEconLib.RevealedPreference.Equilibrium

open MathEconLibExamples.RevealedEquilibrium

example : HasRegularEquilibriumRationalization rationalMarket :=
  rational_has_regular_equilibrium

example : AllocationFeasible refutableMarket refutableAllocation ∧
    ¬ HasIncreasingEquilibriumRationalization refutableMarket :=
  ⟨refutable_allocation_feasible, refutable_no_increasing_equilibrium⟩

example : ¬ HasAfriatAllocation refutableMarket := refutable_no_afriat_allocation

example : GeneralizedAxiomOfRevealedEquilibrium rationalMarket :=
  rational_satisfies_generalized_axiom

example : ¬ GeneralizedAxiomOfRevealedEquilibrium refutableMarket :=
  refutable_fails_generalized_axiom

example (t : Fin 2) :
    IsMaxOn (weightedWelfare rationalUtility (fun _ => 1))
      (resourceFeasibleSet (rationalMarket.resources t)) (fun i => rationalAllocation i t) ∧
      ParetoEfficient (rationalMarket.resources t) rationalUtility
        (fun i => rationalAllocation i t) :=
  rational_weightedWelfare_and_pareto t

example :
    (∀ i, StrictlyIncreasing (totalGoodsUtility i)) ∧
    (∀ t, ParetoEfficient (refutableMarket.resources t) totalGoodsUtility
      (fun i => refutableAllocation i t)) ∧ ¬ GARE refutableMarket :=
  ⟨totalGoodsUtility_strictlyIncreasing, refutable_pareto_at_every_observation_but_not_gare⟩
