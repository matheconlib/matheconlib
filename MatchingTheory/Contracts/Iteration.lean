import MatchingTheory.Contracts.Order
import MatchingTheory.Order.IterateFixedPoint
import Mathlib.Data.Fintype.Powerset

/-!
# Finite deferred-acceptance iteration

Specialize finite-lattice convergence to the generalized DA operator.
Finiteness belongs to the convergence theorems, not to the market definition.
-/

open Function OrderDual

universe u v w

variable {B : Type u} {S : Type v} {X : Type w}

namespace Market

variable (M : Market B S X)

/-! ### Deferred acceptance as iteration

`⊤ = (univ, toDual ∅)`: all contracts available to sellers, none to buyers.
That is the classical initial state of *seller*-proposing deferred acceptance,
and by the orientation convention above it converges to the seller-optimal
state.  Dually `⊥ = (∅, toDual univ)` runs the buyer-proposing algorithm.

Both convergence statements specialize the order-theoretic iteration lemmas.
They assert an existential stopping time; executable choice and iteration
remain separate implementation obligations. -/

/-- Seller-proposing deferred acceptance: under substitutability, iterating
from `(univ, ∅) = ⊤` computes the seller-optimal state in finitely many
steps. -/
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

/-- Buyer-proposing deferred acceptance. -/
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

/-- The algorithmic form of Theorem 2.2, outcome level: seller-proposing
deferred acceptance terminates at the seller-optimal *outcome*. -/
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

/-- Lattice form: the iterates of `⊤` reach `state (sellerOptimalOutcome)`.
Stated through `sellerOptimalOutcome` rather than `⊤` per the orientation
convention, so that downstream files never spell `gfp` either. -/
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
