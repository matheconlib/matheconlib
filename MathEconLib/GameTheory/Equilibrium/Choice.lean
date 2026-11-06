/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Choice.Value
public import MathEconLib.GameTheory.Equilibrium.Problem

/-!
# Equilibrium as value-induced choice

Each deviator chooses from the incumbent state and its admissible deviations. Including the
incumbent also covers deviation relations that exclude staying put. The choice correspondence
requires greatest feasible rewards, including when rewards are only partially ordered.
-/

public section

namespace MathEconLib.GameTheory

open Choice

variable {I S V : Type*} [Preorder V]

/-- Equilibrium is greatest-value choice from the incumbent and the allowed deviations.
No reflexivity of the deviation relation is required. -/
theorem EquilibriumProblem.isEquilibrium_iff_mem_ofValue (P : EquilibriumProblem S I V) (s : S) :
    P.IsEquilibrium s ↔
      ∀ i, s ∈ ChoiceFunction.ofValue (P.value i) (insert s {t | P.deviation i s t}) := by
  simp [ChoiceFunction.mem_ofValue, isMaxOn_iff, EquilibriumProblem.isEquilibrium_iff]

end MathEconLib.GameTheory
