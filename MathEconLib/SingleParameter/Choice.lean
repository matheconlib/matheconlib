/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Choice.Maximizers
public import MathEconLib.SingleParameter.IC

/-!
# Incentive compatibility and optimal choice

Universal IC selects a feasible maximizer of each type's payoff. The payoff-induced preorder
retains tied actions; it does not impose a priority among them. Replacing the strategy by another
feasible strategy with the same payoff preserves universal IC on the original type interval.
Allocation and payment rules remain those of the original problem.
-/

@[expose] public section

namespace MathEconLib.SingleParameterProblem

open Choice

universe u

variable {Action : Type u}

/-- Universal IC is equivalent to selecting a feasible payoff maximizer for every admissible type.
No finiteness, attainment, or tie-breaking assumption is added. -/
theorem hasUniversalIC_iff_mem_maximizers (P : SingleParameterProblem Action) (S : Set Action) :
    P.HasUniversalIC S ↔ ∀ v ∈ P.typeInterval,
      P.strategy v ∈ maximizers (Preorder.lift (P.payoff v)) S := by
  constructor
  · intro h v hv
    exact ⟨h.strategyInS v hv, h.universalIC v hv⟩
  · intro h
    exact ⟨fun v hv ↦ (h v hv).1, fun v hv ↦ (h v hv).2⟩

/-- Any feasible, payoff-preserving replacement strategy remains universally IC.
Payoff equality is required only for types in the original interval. It does not imply that the
replacement preserves allocation, payment, or seller revenue separately. -/
theorem HasUniversalIC.withStrategy {P : SingleParameterProblem Action} {S : Set Action}
    (h : P.HasUniversalIC S) (strategy : ℝ → Action)
    (hfeasible : ∀ v ∈ P.typeInterval, strategy v ∈ S)
    (hsame : ∀ v ∈ P.typeInterval,
      P.payoff v (strategy v) = P.payoff v (P.strategy v)) :
    (P.withStrategy strategy).HasUniversalIC S :=
  ⟨hfeasible, fun v hv a ha ↦
    (h.universalIC v hv a ha).trans (hsame v hv).symm.le⟩

end MathEconLib.SingleParameterProblem
