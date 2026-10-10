import MathEconLib.Matching.Contracts.Order
import MathEconLib.ForMathlib.Order.IterateFixedPoint
import Mathlib.Data.Fintype.Powerset

/-!
# Finite deferred-acceptance iteration

Specialize finite-lattice convergence to the generalized DA operator.
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
`Classical/DeferredAcceptance` and `Classical/DeferredAcceptanceFinite`. -/

/-- Generalized seller-proposing deferred acceptance reaches the greatest
fixed point in finitely many steps. IRC is needed to interpret its outcome
as a seller-optimal stable outcome. -/
theorem exists_iterate_daFun_top (hsub : M.Substitutable) [Finite X] :
    ∃ n, M.daFun^[n] (Set.univ, toDual (∅ : Set X)) =
      OrderHom.gfp (M.daHom hsub) := by
  classical
  letI := Fintype.ofFinite X
  obtain ⟨n, hn⟩ := OrderHom.exists_iterate_top_eq_gfp (M.daHom hsub)
  refine ⟨n, ?_⟩
  -- `⊤ = (univ, toDual ∅)` and `⇑(M.daHom hsub) = M.daFun` are definitional.
  have htop : ((Set.univ, toDual (∅ : Set X)) : Set X × (Set X)ᵒᵈ) = ⊤ := rfl
  rw [htop]
  exact hn

/-- Generalized buyer-proposing deferred acceptance reaches the least fixed point. -/
theorem exists_iterate_daFun_bot (hsub : M.Substitutable) [Finite X] :
    ∃ n, M.daFun^[n] (∅, toDual (Set.univ : Set X)) =
      OrderHom.lfp (M.daHom hsub) := by
  classical
  letI := Fintype.ofFinite X
  obtain ⟨n, hn⟩ := OrderHom.exists_iterate_bot_eq_lfp (M.daHom hsub)
  refine ⟨n, ?_⟩
  have hbot : ((∅, toDual (Set.univ : Set X)) : Set X × (Set X)ᵒᵈ) = ⊥ := rfl
  rw [hbot]
  exact hn

/-- Outcome-level convergence to the named `sellerOptimal` endpoint.
Its stability and optimality follow when IRC is also imposed. -/
theorem exists_iterate_outcomeOf_eq_sellerOptimal (hsub : M.Substitutable)
    [Finite X] :
    ∃ n, M.outcomeOf (M.daFun^[n] (Set.univ, toDual (∅ : Set X)))
      = M.sellerOptimal hsub := by
  obtain ⟨n, hn⟩ := M.exists_iterate_daFun_top hsub
  exact ⟨n, congrArg M.outcomeOf hn⟩

theorem exists_iterate_outcomeOf_eq_buyerOptimal (hsub : M.Substitutable)
    [Finite X] :
    ∃ n, M.outcomeOf (M.daFun^[n] (∅, toDual (Set.univ : Set X)))
      = M.buyerOptimal hsub := by
  obtain ⟨n, hn⟩ := M.exists_iterate_daFun_bot hsub
  exact ⟨n, congrArg M.outcomeOf hn⟩

/-- Lattice form: iteration from `⊤` reaches the state of
`sellerOptimalOutcome`, the top element of the fixed-point lattice. -/
theorem exists_iterate_daFun_top_eq_state (hsub : M.Substitutable)
    [Finite X] :
    ∃ n, M.daFun^[n] (Set.univ, toDual (∅ : Set X)) =
      (M.sellerOptimalOutcome hsub).state := by
  obtain ⟨n, hn⟩ := M.exists_iterate_daFun_top hsub
  exact ⟨n, hn.trans (M.state_sellerOptimalOutcome hsub).symm⟩

theorem exists_iterate_daFun_bot_eq_state (hsub : M.Substitutable)
    [Finite X] :
    ∃ n, M.daFun^[n] (∅, toDual (Set.univ : Set X)) =
      (M.buyerOptimalOutcome hsub).state := by
  obtain ⟨n, hn⟩ := M.exists_iterate_daFun_bot hsub
  exact ⟨n, hn.trans (M.state_buyerOptimalOutcome hsub).symm⟩

end Market

end MathEconLib.Matching
