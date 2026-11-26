/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLibExamples.Choice.Optimality

/-!
# Indifference and feasibility regressions

Use the worked example to check distinct optimal choices and the necessity of replacement
feasibility. Empty type intervals retain the existing vacuous IC semantics.
-/

@[expose] public section

namespace MathEconLibTest.Choice.Optimality

open MathEconLib.Preferences
open MathEconLib MathEconLib.Choice MathEconLib.SingleParameterProblem
open MathEconLib.Mechanism MathEconLibExamples.Choice.Optimality

/-- At equality, the two IC rules make different participation decisions. -/
theorem cutoff_choices_differ (lo hi price : ℝ) :
    (postedPriceProblem lo hi price).strategy price ≠ strictPurchase price price := by
  simp [strictPurchase, postedPriceProblem_strategy_of_price_le]

/-- Both decisions remain in the same correspondence at the cutoff. -/
theorem cutoff_both_maximize (price : ℝ) (a : PurchaseDecision) :
    a ∈ maximizers (Preference.ofUtility ((postedPriceProblem price price price).payoff price))
      Set.univ := by
  apply (mem_maximizers_ofUtility _).mpr
  refine ⟨Set.mem_univ _, ?_⟩
  intro b _
  cases a <;> cases b <;>
    simp [postedPriceProblem, PurchaseDecision.allocation, PurchaseDecision.payment]

/-- Buying is IC on a menu that allows only buying. -/
theorem buyOnly_hasUniversalIC :
    (postedPriceProblem 0 0 0).HasUniversalIC {PurchaseDecision.buy} := by
  refine ⟨?_, ?_⟩
  · intro v hv
    have hv0 : v = 0 := le_antisymm hv.2 hv.1
    simp [hv0, postedPriceProblem_strategy_of_price_le]
  · intro v hv a _
    exact (inferInstance : (postedPriceProblem 0 0 0).HasUniversalIC Set.univ).universalIC
      v hv a (Set.mem_univ _)

/-- Equal payoff cannot replace feasibility: declining is excluded from the buy-only menu. -/
theorem buyOnly_replacement_not_IC :
    ¬ ((postedPriceProblem 0 0 0).withStrategy (strictPurchase 0)).HasUniversalIC
      {PurchaseDecision.buy} := by
  intro h
  have hf := h.strategyInS 0 (by constructor <;> exact le_rfl)
  simp [withStrategy, strictPurchase] at hf

/-- The welfare bridge keeps two distinct efficient outcomes. -/
theorem distinct_efficient_outcomes :
    DirectMechanism.IsEfficient splitEnvironment (constantOutcome false) ∧
      DirectMechanism.IsEfficient splitEnvironment (constantOutcome true) ∧
      (constantOutcome false).outcome (fun _ ↦ ()) ≠
        (constantOutcome true).outcome (fun _ ↦ ()) :=
  ⟨constantOutcome_isEfficient false, constantOutcome_isEfficient true, Bool.false_ne_true⟩

/-- An empty type interval makes even IC on the empty action menu vacuous. -/
theorem empty_type_interval {Action : Type*} (P : SingleParameterProblem Action)
    (h : P.highestType < P.lowestType) : P.HasUniversalIC ∅ :=
  (hasUniversalIC_iff_mem_maximizers P ∅).mpr fun _ hv ↦
    False.elim ((not_le_of_gt h) (hv.1.trans hv.2))

end MathEconLibTest.Choice.Optimality
