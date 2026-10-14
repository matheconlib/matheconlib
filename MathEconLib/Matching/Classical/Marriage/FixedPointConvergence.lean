import MathEconLib.Matching.Classical.Marriage.Optimality
import MathEconLib.Matching.Contracts.FixedPointConvergence

/-!
# Fixed-point convergence in marriage markets

Top and bottom iteration of the contracts deferred-acceptance operator
specialize to marriage markets. Finite convergence identifies their outcomes
with the man- and woman-optimal stable matchings. The classical
deferred-acceptance algorithm and its executable refinement are in
`Classical.Marriage.DeferredAcceptance` and `Classical.Marriage.DeferredAcceptanceComputable`.
-/

namespace MathEconLib.Matching

open Function OrderDual

universe u v

namespace MarriageMarket

variable {M : Type u} {W : Type v}
variable (mkt : MarriageMarket M W)
variable [Fintype M] [Fintype W]

/-! ## Deferred acceptance

The following semantic state sequence iterates the generalized contracts
operator from its top state:

* all man–woman contracts are initially available to men;
* no contracts are initially available to women.

The terminal matching is the matching carried by the greatest fixed point.
-/

set_option linter.unusedVariables false in
/-- Initial state of man-proposing deferred acceptance.

The market parameter is intentionally explicit even though the state itself
does not depend on preferences. This preserves the downstream API
`mkt.manProposingInitialState`. -/
abbrev manProposingInitialState (mkt : MarriageMarket M W) :
    Set (M × W) × (Set (M × W))ᵒᵈ :=
  (Set.univ, toDual (∅ : Set (M × W)))

/-- The state after `n` iterations of the generalized man-proposing operator. -/
noncomputable def deferredAcceptanceState (n : ℕ) :
    Set (M × W) × (Set (M × W))ᵒᵈ :=
  mkt.toContractsMarket.deferredAcceptanceOperator^[n] mkt.manProposingInitialState

/-- The outcome carried by the state after `n` rounds. -/
noncomputable def deferredAcceptanceOutcome (n : ℕ) : Set (M × W) :=
  mkt.toContractsMarket.outcomeOf (mkt.deferredAcceptanceState n)

/-- The man-optimal endpoint specification for generalized deferred acceptance.
`exists_deferredAcceptanceOutcome_eq_graph` proves that the generalized state
iteration eventually carries this matching. The classical proposal algorithm
`galeShapley` and its agreement theorem are in `Classical.Marriage.DeferredAcceptance`;
this definition itself is the optimal endpoint, not an iteration procedure. -/
noncomputable def deferredAcceptance : M ≃. W :=
  mkt.manOptimalMatching

theorem deferredAcceptance_eq_manOptimalMatching :
    mkt.deferredAcceptance = mkt.manOptimalMatching :=
  rfl

theorem stable_deferredAcceptance :
    mkt.IsStableMatching mkt.deferredAcceptance :=
  mkt.stable_manOptimalMatching

theorem deferredAcceptance_manOptimal
    {ν : M ≃. W} (hν : mkt.IsStableMatching ν) (m : M) :
    mkt.leM m (ν m) (mkt.deferredAcceptance m) :=
  mkt.le_manOptimalMatching hν m

/-- The generalized deferred-acceptance state iteration terminates at the
state carrying the man-optimal outcome. -/
theorem exists_deferredAcceptanceState_eq_terminal :
    ∃ n,
      mkt.deferredAcceptanceState n =
        (mkt.toContractsMarket.sellerOptimalOutcome
          mkt.substitutable_toContractsMarket mkt.consistent_toContractsMarket).state := by
  simpa [deferredAcceptanceState, manProposingInitialState] using
    mkt.toContractsMarket.exists_iterate_deferredAcceptanceOperator_top_eq_state
      mkt.substitutable_toContractsMarket mkt.consistent_toContractsMarket

/-- Outcome-level termination of deferred acceptance. -/
theorem exists_deferredAcceptanceOutcome_eq_graph :
    ∃ n,
      mkt.deferredAcceptanceOutcome n =
        mkt.graphOf mkt.deferredAcceptance := by
  obtain ⟨n, hn⟩ :=
    mkt.toContractsMarket.exists_iterate_outcomeOf_eq_sellerOptimal
      mkt.substitutable_toContractsMarket mkt.consistent_toContractsMarket
  refine ⟨n, ?_⟩
  simpa [deferredAcceptanceOutcome, deferredAcceptanceState,
    manProposingInitialState, deferredAcceptance,
    graphOf_manOptimalMatching] using hn

/-- Some finite contracts deferred-acceptance iterate carries the stable man-optimal matching. -/
theorem exists_deferredAcceptanceOutcome_stable :
    ∃ n,
      mkt.deferredAcceptanceOutcome n =
          mkt.graphOf mkt.deferredAcceptance ∧
        mkt.toContractsMarket.Stable (mkt.deferredAcceptanceOutcome n) := by
  obtain ⟨n, hn⟩ := mkt.exists_deferredAcceptanceOutcome_eq_graph
  refine ⟨n, hn, ?_⟩
  rw [hn]
  exact (mkt.isStableMatching_iff_stable_graphOf
    mkt.deferredAcceptance).mp mkt.stable_deferredAcceptance

/-! ### The symmetric generalized iteration

These are set-valued iterates of the contracts operator, with an
existential convergence theorem. The classical proposal implementation is
provided separately in `Classical.Marriage.DeferredAcceptance`.
-/

set_option linter.unusedVariables false in
/-- Initial state of woman-proposing generalized deferred acceptance. -/
abbrev womanProposingInitialState (mkt : MarriageMarket M W) :
    Set (M × W) × (Set (M × W))ᵒᵈ :=
  (∅, toDual (Set.univ : Set (M × W)))

/-- The `n`th contracts deferred-acceptance state starting from the buyer-proposing end. -/
noncomputable def womanProposingDeferredAcceptanceState (n : ℕ) :
    Set (M × W) × (Set (M × W))ᵒᵈ :=
  mkt.toContractsMarket.deferredAcceptanceOperator^[n] mkt.womanProposingInitialState

/-- The contracts carried by the `n`th woman-proposing generalized state. -/
noncomputable def womanProposingDeferredAcceptanceOutcome (n : ℕ) : Set (M × W) :=
  mkt.toContractsMarket.outcomeOf (mkt.womanProposingDeferredAcceptanceState n)

/-- The woman-optimal endpoint specification for generalized deferred acceptance.
`exists_womanProposingDeferredAcceptanceOutcome_eq_graph` proves that the
generalized state iteration eventually carries this matching. The classical
proposal algorithm `womanGaleShapley` and its agreement theorem are in
`Classical.Marriage.DeferredAcceptance`; this definition specifies the optimal endpoint. -/
noncomputable def womanProposingDeferredAcceptance : M ≃. W :=
  mkt.womanOptimalMatching

theorem womanProposingDeferredAcceptance_eq_womanOptimalMatching :
    mkt.womanProposingDeferredAcceptance = mkt.womanOptimalMatching := rfl

theorem stable_womanProposingDeferredAcceptance :
    mkt.IsStableMatching mkt.womanProposingDeferredAcceptance :=
  mkt.stable_womanOptimalMatching

theorem womanProposingDeferredAcceptance_womanOptimal
    {ν : M ≃. W} (hν : mkt.IsStableMatching ν) (w : W) :
    mkt.leW w (ν.symm w) (mkt.womanProposingDeferredAcceptance.symm w) :=
  mkt.le_womanOptimalMatching hν w

theorem womanProposingDeferredAcceptance_manPessimal
    {ν : M ≃. W} (hν : mkt.IsStableMatching ν) (m : M) :
    mkt.leM m (mkt.womanProposingDeferredAcceptance m) (ν m) :=
  mkt.womanOptimalMatching_le hν m

theorem exists_womanProposingDeferredAcceptanceState_eq_terminal :
    ∃ n, mkt.womanProposingDeferredAcceptanceState n =
      (mkt.toContractsMarket.buyerOptimalOutcome
        mkt.substitutable_toContractsMarket mkt.consistent_toContractsMarket).state := by
  simpa [womanProposingDeferredAcceptanceState, womanProposingInitialState] using
    mkt.toContractsMarket.exists_iterate_deferredAcceptanceOperator_bot_eq_state
      mkt.substitutable_toContractsMarket mkt.consistent_toContractsMarket

theorem exists_womanProposingDeferredAcceptanceOutcome_eq_graph :
    ∃ n, mkt.womanProposingDeferredAcceptanceOutcome n =
      mkt.graphOf mkt.womanOptimalMatching := by
  obtain ⟨n, hn⟩ := mkt.toContractsMarket.exists_iterate_outcomeOf_eq_buyerOptimal
    mkt.substitutable_toContractsMarket mkt.consistent_toContractsMarket
  refine ⟨n, ?_⟩
  simpa [womanProposingDeferredAcceptanceOutcome, womanProposingDeferredAcceptanceState,
    womanProposingInitialState, graphOf_womanOptimalMatching] using hn

/-- Finite convergence, with both sides' extremal interpretations. -/
theorem exists_womanProposingDeferredAcceptanceOutcome_stable :
    ∃ n, mkt.womanProposingDeferredAcceptanceOutcome n =
          mkt.graphOf mkt.womanOptimalMatching ∧
      mkt.toContractsMarket.Stable (mkt.womanProposingDeferredAcceptanceOutcome n) ∧
      mkt.IsWomanOptimal mkt.womanOptimalMatching ∧
      mkt.IsManPessimal mkt.womanOptimalMatching := by
  obtain ⟨n, hn⟩ := mkt.exists_womanProposingDeferredAcceptanceOutcome_eq_graph
  refine ⟨n, hn, ?_, mkt.isWomanOptimal_womanOptimalMatching,
    mkt.isManPessimal_womanOptimalMatching⟩
  rw [hn]
  exact (mkt.isStableMatching_iff_stable_graphOf _).mp mkt.stable_womanOptimalMatching

end MarriageMarket

end MathEconLib.Matching
