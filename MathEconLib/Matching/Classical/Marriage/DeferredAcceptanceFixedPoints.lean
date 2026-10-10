import MathEconLib.Matching.Classical.Marriage.DeferredAcceptance

/-!
# Classical proposal outcomes and contracts fixed points

This module gives a second correctness route for the classical proposal
algorithm. Its elementary holding and first-rejection invariants certify the
canonical contracts state of a terminal proposal graph as the greatest fixed
point. Generalized stability and optimality then transfer to the classical
output. Side exchange gives the corresponding least-fixed-point outcome for
woman-proposing deferred acceptance.

The fixed-point proof does not invoke `stable_galeShapley`,
`isManOptimal_galeShapley`, or their direct terminal-state counterparts. The
two proof routes share elementary proposal invariants. Their agreement is at
the level of terminal outcomes; their intermediate states and round counts
need not agree.
-/

namespace MathEconLib.Matching

open Function OrderDual

universe u v

namespace MarriageMarket

variable {M : Type u} {W : Type v}
variable (mkt : MarriageMarket M W) [Fintype M] [Fintype W]

/-- The partners selected in a terminal proposal round are acceptable. -/
theorem individuallyRational_gsMatchingAt (R : Set (M × W))
    (hR : IsFixedPt mkt.gsStep R) :
    mkt.IndividuallyRational (mkt.gsMatchingAt R hR) :=
  ⟨fun m => mkt.none_le_bestM m _, fun w => mkt.none_le_bestW w _⟩

/-- A contract accepted by both sides on top of a reached terminal graph
already belongs to that graph. This is a direct consequence of the rejection
invariant, before applying any stability theorem. -/
theorem gsMatchingAt_accepts_only_graph (n : ℕ)
    (hn : IsFixedPt mkt.gsStep (mkt.gsRejected n))
    (p : M × W)
    (hB : p ∈ mkt.toContractsMarket.choiceB (mkt.toContractsMarket.buyer p)
      (insert p (mkt.graphOf (mkt.gsMatchingAt (mkt.gsRejected n) hn))))
    (hS : p ∈ mkt.toContractsMarket.choiceS (mkt.toContractsMarket.seller p)
      (insert p (mkt.graphOf (mkt.gsMatchingAt (mkt.gsRejected n) hn)))) :
    p ∈ mkt.graphOf (mkt.gsMatchingAt (mkt.gsRejected n) hn) := by
  classical
  rcases p with ⟨m, w⟩
  by_contra hnew
  have hIR := mkt.individuallyRational_gsMatchingAt (mkt.gsRejected n) hn
  have hnewM : mkt.gsMatchingAt (mkt.gsRejected n) hn m ≠ some w :=
    fun h => hnew (mkt.mem_graphOf.mpr h)
  have hnewW : (mkt.gsMatchingAt (mkt.gsRejected n) hn).symm w ≠ some m :=
    fun h => hnew (mkt.mem_graphOf_symm.mpr h)
  have hm := (mkt.mem_choiceM_insert_graphOf_iff (hIR.1 m) hnewM).mp hS
  have hw := (mkt.mem_choiceW_insert_graphOf_iff (hIR.2 w) hnewW).mp hB
  by_cases hR : (m, w) ∈ mkt.gsRejected n
  · letI := mkt.prefW w
    exact (lt_asymm (mkt.gs_rejected_below_holding n hR)) hw
  · letI := mkt.prefM m
    have hle : some w ≤ mkt.bestM m (mkt.gsRejected n)ᶜ :=
      mkt.le_bestM_of_mem (mkt.some_mem_menuM.mpr hR)
    exact (not_lt_of_ge hle) hm

/-- The reached terminal graph certifies a contracts fixed point directly. -/
theorem isFixedPt_stateOf_graphOf_gsMatchingAt (n : ℕ)
    (hn : IsFixedPt mkt.gsStep (mkt.gsRejected n)) :
    IsFixedPt mkt.toContractsMarket.deferredAcceptanceOperator
      (mkt.toContractsMarket.stateOf (mkt.graphOf (mkt.gsMatchingAt (mkt.gsRejected n) hn))) :=
  mkt.toContractsMarket.isFixedPt_stateOf_of_indRational_of_accepts
    mkt.substitutable_toContractsMarket mkt.consistent_toContractsMarket
    (mkt.individuallyRational_graphOf
      (mkt.individuallyRational_gsMatchingAt (mkt.gsRejected n) hn))
    (mkt.gsMatchingAt_accepts_only_graph n hn)

/-- The canonical contracts state carries exactly the terminal proposal graph. -/
theorem outcomeOf_stateOf_graphOf_gsMatchingAt (n : ℕ)
    (hn : IsFixedPt mkt.gsStep (mkt.gsRejected n)) :
    mkt.toContractsMarket.outcomeOf
        (mkt.toContractsMarket.stateOf (mkt.graphOf (mkt.gsMatchingAt (mkt.gsRejected n) hn))) =
      mkt.graphOf (mkt.gsMatchingAt (mkt.gsRejected n) hn) :=
  mkt.toContractsMarket.outcomeOf_stateOf_of_indRational_of_accepts
    (mkt.individuallyRational_graphOf
      (mkt.individuallyRational_gsMatchingAt (mkt.gsRejected n) hn))
    (mkt.gsMatchingAt_accepts_only_graph n hn)

/-- Stability of a reached terminal matching inherited directly from the
general fixed-point theorem, without the first-rejection comparison. -/
theorem stable_gsMatchingAt_via_fixedPoints (n : ℕ)
    (hn : IsFixedPt mkt.gsStep (mkt.gsRejected n)) :
    mkt.IsStableMatching (mkt.gsMatchingAt (mkt.gsRejected n) hn) := by
  apply (mkt.isStableMatching_iff_stable_graphOf _).mpr
  have h := mkt.toContractsMarket.stable_outcomeOf
    mkt.substitutable_toContractsMarket mkt.consistent_toContractsMarket
    (mkt.isFixedPt_stateOf_graphOf_gsMatchingAt n hn)
  rwa [mkt.outcomeOf_stateOf_graphOf_gsMatchingAt n hn] at h

/-- First rejection and the contracts order dictionary identify the certified
fixed point as the greatest one. Direct classical endpoint stability or
optimality is not used in this argument. -/
theorem stateOf_graphOf_gsMatchingAt_eq_gfp (n : ℕ)
    (hn : IsFixedPt mkt.gsStep (mkt.gsRejected n)) :
    mkt.toContractsMarket.stateOf (mkt.graphOf (mkt.gsMatchingAt (mkt.gsRejected n) hn)) =
      OrderHom.gfp (mkt.toContractsMarket.deferredAcceptanceOrderHom mkt.substitutable_toContractsMarket) := by
  have hfixed := mkt.isFixedPt_stateOf_graphOf_gsMatchingAt n hn
  apply le_antisymm (mkt.toContractsMarket.le_gfp_deferredAcceptanceOrderHom mkt.substitutable_toContractsMarket hfixed)
  apply mkt.toContractsMarket.le_of_sellerChosen_outcomeOf
    mkt.substitutable_toContractsMarket mkt.consistent_toContractsMarket
    (mkt.toContractsMarket.isFixedPt_gfp_deferredAcceptanceOrderHom mkt.substitutable_toContractsMarket) hfixed
  rw [mkt.outcomeOf_stateOf_graphOf_gsMatchingAt n hn]
  change mkt.toContractsMarket.SellerChosen
    (mkt.graphOf (mkt.gsMatchingAt (mkt.gsRejected n) hn))
    (mkt.toContractsMarket.sellerOptimal mkt.substitutable_toContractsMarket mkt.consistent_toContractsMarket)
  rw [← mkt.graphOf_manOptimalMatching]
  apply mkt.sellerChosen_graphOf_of_individuallyRationalM
    (mkt.individuallyRational_gsMatchingAt (mkt.gsRejected n) hn).1
  intro m
  exact mkt.gs_assignment_le_proposal
    (mkt.gs_rejected_not_mem_stable n mkt.stable_manOptimalMatching) m

/-- The terminal classical graph is the generalized seller-optimal outcome. -/
theorem graphOf_gsMatchingAt_eq_sellerOptimal_via_fixedPoints (n : ℕ)
    (hn : IsFixedPt mkt.gsStep (mkt.gsRejected n)) :
    mkt.graphOf (mkt.gsMatchingAt (mkt.gsRejected n) hn) =
      mkt.toContractsMarket.sellerOptimal mkt.substitutable_toContractsMarket mkt.consistent_toContractsMarket := by
  calc
    mkt.graphOf (mkt.gsMatchingAt (mkt.gsRejected n) hn) =
        mkt.toContractsMarket.outcomeOf
          (mkt.toContractsMarket.stateOf (mkt.graphOf (mkt.gsMatchingAt (mkt.gsRejected n) hn))) :=
      (mkt.outcomeOf_stateOf_graphOf_gsMatchingAt n hn).symm
    _ = mkt.toContractsMarket.outcomeOf
        (OrderHom.gfp (mkt.toContractsMarket.deferredAcceptanceOrderHom mkt.substitutable_toContractsMarket)) :=
      congrArg mkt.toContractsMarket.outcomeOf (mkt.stateOf_graphOf_gsMatchingAt_eq_gfp n hn)
    _ = _ := rfl

theorem graphOf_galeShapley_eq_sellerOptimal_via_fixedPoints :
    mkt.graphOf mkt.galeShapley =
      mkt.toContractsMarket.sellerOptimal mkt.substitutable_toContractsMarket mkt.consistent_toContractsMarket :=
  mkt.graphOf_gsMatchingAt_eq_sellerOptimal_via_fixedPoints
    mkt.galeShapleyRoundBound mkt.galeShapleyRoundBound_terminal

theorem stateOf_graphOf_galeShapley_eq_gfp :
    mkt.toContractsMarket.stateOf (mkt.graphOf mkt.galeShapley) =
      OrderHom.gfp (mkt.toContractsMarket.deferredAcceptanceOrderHom mkt.substitutable_toContractsMarket) :=
  mkt.stateOf_graphOf_gsMatchingAt_eq_gfp
    mkt.galeShapleyRoundBound mkt.galeShapleyRoundBound_terminal

/-- Outcome correspondence through the generalized fixed-point certificate. -/
theorem galeShapley_eq_deferredAcceptance_via_fixedPoints :
    mkt.galeShapley = mkt.deferredAcceptance := by
  apply mkt.graphOf_injective
  exact mkt.graphOf_galeShapley_eq_sellerOptimal_via_fixedPoints.trans
    mkt.graphOf_manOptimalMatching.symm

/-- The woman-proposing correspondence follows by exchanging the two sides
in the fixed-point argument. -/
theorem womanGaleShapley_eq_womanProposingDeferredAcceptance_via_fixedPoints :
    mkt.womanGaleShapley = mkt.womanProposingDeferredAcceptance := by
  have h := congrArg PEquiv.symm
    mkt.symm.galeShapley_eq_deferredAcceptance_via_fixedPoints
  simpa only [womanGaleShapley, deferredAcceptance, womanProposingDeferredAcceptance,
    manOptimalMatching_symm, PEquiv.symm_symm] using h

theorem graphOf_womanGaleShapley_eq_buyerOptimal_via_fixedPoints :
    mkt.graphOf mkt.womanGaleShapley =
      mkt.toContractsMarket.buyerOptimal mkt.substitutable_toContractsMarket mkt.consistent_toContractsMarket := by
  rw [mkt.womanGaleShapley_eq_womanProposingDeferredAcceptance_via_fixedPoints]
  exact mkt.graphOf_womanOptimalMatching

theorem stateOf_graphOf_womanGaleShapley_eq_lfp :
    mkt.toContractsMarket.stateOf (mkt.graphOf mkt.womanGaleShapley) =
      OrderHom.lfp (mkt.toContractsMarket.deferredAcceptanceOrderHom mkt.substitutable_toContractsMarket) := by
  rw [mkt.graphOf_womanGaleShapley_eq_buyerOptimal_via_fixedPoints]
  exact mkt.toContractsMarket.stateOf_outcomeOf mkt.substitutable_toContractsMarket mkt.consistent_toContractsMarket
    (mkt.toContractsMarket.isFixedPt_lfp_deferredAcceptanceOrderHom mkt.substitutable_toContractsMarket)

/-- Some generalized seller-proposing iterate carries the classical terminal
graph. This compares outcomes, without aligning the round indices. -/
theorem exists_generalized_round_eq_galeShapley_via_fixedPoints :
    ∃ n, mkt.deferredAcceptanceOutcome n = mkt.graphOf mkt.galeShapley := by
  rw [mkt.galeShapley_eq_deferredAcceptance_via_fixedPoints]
  exact mkt.exists_deferredAcceptanceOutcome_eq_graph

/-- The corresponding actual-iterate result for woman-proposing deferred acceptance. -/
theorem exists_generalized_woman_round_eq_womanGaleShapley_via_fixedPoints :
    ∃ n, mkt.womanProposingDeferredAcceptanceOutcome n =
      mkt.graphOf mkt.womanGaleShapley := by
  rw [mkt.womanGaleShapley_eq_womanProposingDeferredAcceptance_via_fixedPoints]
  exact mkt.exists_womanProposingDeferredAcceptanceOutcome_eq_graph

/-- Classical stability inherited from the contracts fixed-point theorem. -/
theorem stable_galeShapley_via_fixedPoints : mkt.IsStableMatching mkt.galeShapley :=
  mkt.stable_gsMatchingAt_via_fixedPoints mkt.galeShapleyRoundBound mkt.galeShapleyRoundBound_terminal

theorem isManOptimal_galeShapley_via_fixedPoints : mkt.IsManOptimal mkt.galeShapley := by
  rw [mkt.galeShapley_eq_deferredAcceptance_via_fixedPoints]
  exact mkt.isManOptimal_manOptimalMatching

theorem isWomanPessimal_galeShapley_via_fixedPoints :
    mkt.IsWomanPessimal mkt.galeShapley := by
  rw [mkt.galeShapley_eq_deferredAcceptance_via_fixedPoints]
  exact mkt.isWomanPessimal_manOptimalMatching

theorem stable_womanGaleShapley_via_fixedPoints :
    mkt.IsStableMatching mkt.womanGaleShapley := by
  apply (mkt.isStableMatching_symm mkt.womanGaleShapley).mp
  simpa only [womanGaleShapley, PEquiv.symm_symm] using
    mkt.symm.stable_galeShapley_via_fixedPoints

theorem isWomanOptimal_womanGaleShapley_via_fixedPoints :
    mkt.IsWomanOptimal mkt.womanGaleShapley := by
  rw [mkt.womanGaleShapley_eq_womanProposingDeferredAcceptance_via_fixedPoints]
  exact mkt.isWomanOptimal_womanOptimalMatching

theorem isManPessimal_womanGaleShapley_via_fixedPoints :
    mkt.IsManPessimal mkt.womanGaleShapley := by
  rw [mkt.womanGaleShapley_eq_womanProposingDeferredAcceptance_via_fixedPoints]
  exact mkt.isManPessimal_womanOptimalMatching

end MarriageMarket

end MathEconLib.Matching
