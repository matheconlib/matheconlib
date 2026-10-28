/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Choice.Maximizers
public import MathEconLib.Mechanism.Core.SolutionConcepts

/-!
# Welfare efficiency and optimal choice

The existing efficiency predicate is choice from the maximizers of total value over all outcomes.
The induced preference permits distinct tied outcomes. Welfare excludes transfers, as in
`QuasilinearEnvironment.totalValue`; this bridge adds no incentive or participation condition.
-/

@[expose] public section

namespace MathEconLib.Mechanism.DirectMechanism

open Choice Preferences

universe uI uT uO

variable {I : Type uI} {T : I → Type uT} {O : Type uO}

/-- Efficiency selects a total-value maximizer at each truthful type profile, allowing ties.
All outcomes are feasible in the existing `IsEfficient` definition. -/
theorem isEfficient_iff_mem_maximizers [Fintype I]
    (E : QuasilinearEnvironment I T O) (M : DirectMechanism I T O) :
    IsEfficient E M ↔ ∀ θ,
      M.outcome θ ∈ maximizers (Preference.ofUtility (E.totalValue θ)) Set.univ := by
  simp only [IsEfficient, mem_maximizers_ofUtility, Set.mem_univ, true_and]

end MathEconLib.Mechanism.DirectMechanism
