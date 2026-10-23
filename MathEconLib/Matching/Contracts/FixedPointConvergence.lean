/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
import MathEconLib.Matching.Contracts.StableOrder
import MathEconLib.ForMathlib.Order.IterateFixedPoint
import Mathlib.Data.Fintype.Powerset

/-!
# Fixed-point convergence in contracts markets

Specialize finite-lattice convergence to the contracts deferred-acceptance operator.
Finiteness belongs to the convergence theorems, not to the market definition.
-/

namespace MathEconLib.Matching

open Function OrderDual

universe u v w

variable {B : Type u} {S : Type v} {X : Type w}

namespace Market

variable (M : Market B S X)

/-! ### Deferred acceptance as iteration

`⊤ = (univ, toDual ∅)`: all contracts available to sellers, none to buyers.
This is the initial state of generalized seller-proposing deferred acceptance;
on a finite contract type its iterates reach the greatest fixed point.
Dually, iteration from `⊥ = (∅, toDual univ)` reaches the least fixed point.
With IRC, these fixed points carry the seller-optimal and buyer-optimal stable
outcomes, respectively.

Both convergence statements specialize the order-theoretic iteration lemmas.
They assert an existential stopping time. The classical simultaneous proposal
process and its executable finite refinement are developed separately in
`Classical/Marriage/DeferredAcceptance` and `Classical/Marriage/DeferredAcceptanceComputable`. -/

/-- Generalized seller-proposing deferred acceptance reaches the greatest
fixed point in finitely many steps. IRC is needed to interpret its outcome
as a seller-optimal stable outcome. -/
theorem exists_iterate_deferredAcceptanceOperator_top (hsub : M.Substitutable) [Finite X] :
    ∃ n, M.deferredAcceptanceOperator^[n] (Set.univ, toDual (∅ : Set X)) =
      OrderHom.gfp (M.deferredAcceptanceOrderHom hsub) := by
  classical
  let := Fintype.ofFinite X
  obtain ⟨n, hn⟩ := OrderHom.exists_iterate_top_eq_gfp (M.deferredAcceptanceOrderHom hsub)
  refine ⟨n, ?_⟩
  -- `⊤ = (univ, toDual ∅)` and
  -- `⇑(M.deferredAcceptanceOrderHom hsub) = M.deferredAcceptanceOperator` are definitional.
  have htop : ((Set.univ, toDual (∅ : Set X)) : Set X × (Set X)ᵒᵈ) = ⊤ := rfl
  rw [htop]
  exact hn

/-- Generalized buyer-proposing deferred acceptance reaches the least fixed point. -/
theorem exists_iterate_deferredAcceptanceOperator_bot (hsub : M.Substitutable) [Finite X] :
    ∃ n, M.deferredAcceptanceOperator^[n] (∅, toDual (Set.univ : Set X)) =
      OrderHom.lfp (M.deferredAcceptanceOrderHom hsub) := by
  classical
  let := Fintype.ofFinite X
  obtain ⟨n, hn⟩ := OrderHom.exists_iterate_bot_eq_lfp (M.deferredAcceptanceOrderHom hsub)
  refine ⟨n, ?_⟩
  have hbot : ((∅, toDual (Set.univ : Set X)) : Set X × (Set X)ᵒᵈ) = ⊥ := rfl
  rw [hbot]
  exact hn

/-- Outcome-level convergence to the seller-optimal stable endpoint.
The underlying fixed-point convergence theorem needs no IRC assumption. -/
theorem exists_iterate_outcomeOf_eq_sellerOptimal (hsub : M.Substitutable)
    (hcons : M.Consistent) [Finite X] :
    ∃ n, M.outcomeOf (M.deferredAcceptanceOperator^[n] (Set.univ, toDual (∅ : Set X)))
      = M.sellerOptimal hsub hcons := by
  obtain ⟨n, hn⟩ := M.exists_iterate_deferredAcceptanceOperator_top hsub
  exact ⟨n, congrArg M.outcomeOf hn⟩

theorem exists_iterate_outcomeOf_eq_buyerOptimal (hsub : M.Substitutable)
    (hcons : M.Consistent) [Finite X] :
    ∃ n, M.outcomeOf (M.deferredAcceptanceOperator^[n] (∅, toDual (Set.univ : Set X)))
      = M.buyerOptimal hsub hcons := by
  obtain ⟨n, hn⟩ := M.exists_iterate_deferredAcceptanceOperator_bot hsub
  exact ⟨n, congrArg M.outcomeOf hn⟩

/-- Lattice form: iteration from `⊤` reaches the state of
`sellerOptimalOutcome`, the top element of the fixed-point lattice. -/
theorem exists_iterate_deferredAcceptanceOperator_top_eq_state (hsub : M.Substitutable)
    (hcons : M.Consistent) [Finite X] :
    ∃ n, M.deferredAcceptanceOperator^[n] (Set.univ, toDual (∅ : Set X)) =
      (M.sellerOptimalOutcome hsub hcons).state := by
  obtain ⟨n, hn⟩ := M.exists_iterate_deferredAcceptanceOperator_top hsub
  exact ⟨n, hn.trans (M.state_sellerOptimalOutcome hsub hcons).symm⟩

theorem exists_iterate_deferredAcceptanceOperator_bot_eq_state (hsub : M.Substitutable)
    (hcons : M.Consistent) [Finite X] :
    ∃ n, M.deferredAcceptanceOperator^[n] (∅, toDual (Set.univ : Set X)) =
      (M.buyerOptimalOutcome hsub hcons).state := by
  obtain ⟨n, hn⟩ := M.exists_iterate_deferredAcceptanceOperator_bot hsub
  exact ⟨n, hn.trans (M.state_buyerOptimalOutcome hsub hcons).symm⟩

end Market

end MathEconLib.Matching
