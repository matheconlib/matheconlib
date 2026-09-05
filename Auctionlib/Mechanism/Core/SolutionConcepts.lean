/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Auctionlib.Mechanism.Core.Comap
public import Auctionlib.Mechanism.Core.Environment
public import Mathlib.Order.Filter.Extr

/-!
# Incentives, participation, efficiency, and budget balance

Dominant-strategy incentive compatibility requires truthful reporting to maximize each agent's
utility at every true type profile, whatever the other agents report. Ex-post individual
rationality requires nonnegative utility when everyone reports truthfully, with outside utility
normalized to zero. Efficiency requires the outcome at each truthful profile to maximize total
value over the outcome space.

These properties evaluate a direct mechanism using the valuations in a quasilinear environment,
which may depend on the full true type profile. Strong budget balance and no deficit constrain
aggregate transfers at every action profile, for direct or indirect mechanisms.

## Main definitions

* `DirectMechanism.IsDSIC`: truthful reporting weakly dominates every own report.
* `DirectMechanism.IsExPostIR`: truthful participation gives every agent nonnegative utility.
* `DirectMechanism.IsEfficient`: truthful outcomes maximize total value.
* `Mechanism.IsBudgetBalanced`: aggregate signed transfers are zero at every action profile.
* `Mechanism.IsNoDeficit`: aggregate signed transfers are nonpositive at every action profile.

## Main statements

* `DirectMechanism.isEfficient_iff`: efficiency is equivalent to weakly exceeding the total value
  of every alternative outcome at each truthful profile.
* `Mechanism.isBudgetBalanced_iff_revenue_eq_zero`: strong budget balance is equivalent to zero
  designer revenue at every action profile.
* `Mechanism.isNoDeficit_iff_revenue_nonneg`: no deficit is equivalent to nonnegative designer
  revenue at every action profile.
* `Mechanism.IsBudgetBalanced.isNoDeficit`: strong budget balance implies no deficit.

## Tags

mechanism design, incentive compatibility, individual rationality, efficiency, budget balance
-/

@[expose] public section

set_option linter.dupNamespace false

universe uI uΘ uA uO

namespace Auctionlib.Mechanism

variable {I : Type uI} {Θ : I → Type uΘ} {A : I → Type uA} {O : Type uO}

namespace DirectMechanism

variable (E : QuasilinearEnvironment I Θ O) (M : DirectMechanism I Θ O)

/-- Dominant-strategy incentive compatibility of the reporting mechanism `M` under valuations `E`.
For every agent and full true type profile `θ`, reporting `θ i` gives at least as much utility as
any own report, at any fixed profile of the other agents' reports. The entire true profile `θ` is
held fixed in the comparison, allowing values to depend on other agents' types. -/
def IsDSIC [DecidableEq I] : Prop :=
  ∀ i (θ r : Profile Θ),
    E.utility M i θ r ≤ E.utility M i θ (Function.update r i (θ i))

/-- Ex-post individual rationality of the reporting mechanism `M` under valuations `E`. At every
true type profile, every agent has nonnegative utility when all agents report truthfully, with
outside utility normalized to zero. -/
def IsExPostIR : Prop := ∀ i θ, 0 ≤ E.utility M i θ θ

/-- Efficiency of the reporting mechanism `M` under valuations `E`: at every true type profile, the
outcome selected when everyone reports truthfully maximizes total value over all outcomes in `O`.
Total value is the sum of agents' values, excluding transfers. -/
def IsEfficient [Fintype I] : Prop :=
  ∀ θ, IsMaxOn (E.totalValue θ) Set.univ (M.outcome θ)

/-- Efficiency expressed as the welfare comparison with every alternative outcome. -/
theorem isEfficient_iff [Fintype I] :
    IsEfficient E M ↔ ∀ θ o, E.totalValue θ o ≤ E.totalValue θ (M.outcome θ) := by
  simp only [IsEfficient, isMaxOn_iff, Set.mem_univ, forall_const]

end DirectMechanism

namespace Mechanism

variable (M : Mechanism I A O)

/-- Strong budget balance: agents' signed transfers sum to zero at every action profile. -/
def IsBudgetBalanced [Fintype I] : Prop := ∀ a, ∑ i, M.transfer i a = 0

/-- No deficit: the designer never pays out on net at any action profile. -/
def IsNoDeficit [Fintype I] : Prop := ∀ a, ∑ i, M.transfer i a ≤ 0

/-- Strong budget balance holds exactly when the designer's revenue is zero at every action
profile. -/
theorem isBudgetBalanced_iff_revenue_eq_zero [Fintype I] :
    M.IsBudgetBalanced ↔ ∀ a, M.revenue a = 0 := by
  simp only [IsBudgetBalanced, revenue, neg_eq_zero]

/-- No deficit holds exactly when the designer's revenue is nonnegative at every action profile. -/
theorem isNoDeficit_iff_revenue_nonneg [Fintype I] :
    M.IsNoDeficit ↔ ∀ a, 0 ≤ M.revenue a := by
  simp only [IsNoDeficit, revenue, neg_nonneg]

/-- A budget-balanced mechanism never runs a deficit. -/
theorem IsBudgetBalanced.isNoDeficit [Fintype I] (h : M.IsBudgetBalanced) :
    M.IsNoDeficit := fun a => le_of_eq (h a)

end Mechanism

end Auctionlib.Mechanism

end
