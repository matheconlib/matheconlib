import MatchingTheory.Classical.Marriage
import MatchingTheory.Order.IterateFiniteSet

/-!
# Classical deferred acceptance by simultaneous proposal rounds

This is the usual man-proposing Gale–Shapley algorithm, expressed by its set
of rejected pairs. In each round every man proposes to his best unrejected
acceptable woman; each woman retains her best acceptable proposal and rejects
the others. A held man repeats his proposal, so only rejected men advance.

The proof follows the classical argument: held proposals survive to the next
round, women's holdings improve, and a pair in any stable matching is never
rejected. These invariants give stability and man-optimality independently of
the contracts fixed-point proof. Uniqueness of the man-optimal matching then
identifies the terminal result with generalized deferred acceptance. The two
algorithms need not have the same intermediate states or number of rounds.

The definitions here use the existing set-valued preference-choice interface
and are noncomputable. They specify actual successive proposal rounds; they
do not define an algorithm to be its already-known optimal endpoint.
-/

open Function OrderDual

universe u v

namespace MarriageMarket

variable {M : Type u} {W : Type v}
variable (mkt : MarriageMarket M W) [Fintype M] [Fintype W]

/-- Current proposals: each man selects his best unrejected acceptable woman. -/
noncomputable def gsProposals (R : Set (M × W)) : Set (M × W) :=
  {p | some p.2 = mkt.bestM p.1 Rᶜ}

/-- Proposals retained by their recipients in the current round. -/
noncomputable def gsHeld (R : Set (M × W)) : Set (M × W) :=
  {p | p ∈ mkt.gsProposals R ∧
    some p.1 = mkt.bestW p.2 (mkt.gsProposals R)}

/-- Add every current rejection to the rejection history. -/
noncomputable def gsStep (R : Set (M × W)) : Set (M × W) :=
  R ∪ (mkt.gsProposals R \ mkt.gsHeld R)

/-- Rejection history after `n` simultaneous proposal rounds. -/
noncomputable def gsRejected (n : ℕ) : Set (M × W) :=
  mkt.gsStep^[n] ∅

@[simp] theorem gsRejected_zero : mkt.gsRejected 0 = ∅ := rfl

theorem gsRejected_succ (n : ℕ) :
    mkt.gsRejected (n + 1) = mkt.gsStep (mkt.gsRejected n) :=
  Function.iterate_succ_apply' _ _ _

theorem gs_subset_step (R : Set (M × W)) : R ⊆ mkt.gsStep R :=
  Set.subset_union_left

omit [Fintype M] in
theorem gs_proposal_not_rejected {R : Set (M × W)} {m : M} {w : W}
    (hp : (m, w) ∈ mkt.gsProposals R) : (m, w) ∉ R := by
  change some w = mkt.bestM m Rᶜ at hp
  have hmem := mkt.bestM_mem_menuM m Rᶜ
  rw [← hp] at hmem
  exact mkt.some_mem_menuM.mp hmem

/-- If the best proposal to a woman is a man, it is indeed a proposal. -/
theorem gs_bestW_mem {R : Set (M × W)} {m : M} {w : W}
    (h : mkt.bestW w (mkt.gsProposals R) = some m) :
    (m, w) ∈ mkt.gsProposals R := by
  have hmem := mkt.bestW_mem_menuW w (mkt.gsProposals R)
  rw [h] at hmem
  exact mkt.some_mem_menuW.mp hmem

/-- A man whose proposal is retained makes the same proposal next round. -/
theorem gs_held_proposes_next {R : Set (M × W)} {m : M} {w : W}
    (hh : (m, w) ∈ mkt.gsHeld R) :
    (m, w) ∈ mkt.gsProposals (mkt.gsStep R) := by
  letI := mkt.prefM m
  have hbest : some w = mkt.bestM m Rᶜ := hh.1
  have hnew : (m, w) ∉ mkt.gsStep R := by
    rintro (hR | ⟨_, hn⟩)
    · exact mkt.gs_proposal_not_rejected hh.1 hR
    · exact hn hh
  have hle : mkt.bestM m (mkt.gsStep R)ᶜ ≤ mkt.bestM m Rᶜ :=
    mkt.bestM_mono (fun _ hx hR => hx (Or.inl hR))
  have hge : some w ≤ mkt.bestM m (mkt.gsStep R)ᶜ :=
    mkt.le_bestM_of_mem (mkt.some_mem_menuM.mpr hnew)
  change some w = mkt.bestM m (mkt.gsStep R)ᶜ
  exact le_antisymm hge (by simpa only [← hbest] using hle)

/-- Women's best proposals weakly improve from one round to the next. -/
theorem gs_women_improve (R : Set (M × W)) (w : W) :
    mkt.leW w (mkt.bestW w (mkt.gsProposals R))
      (mkt.bestW w (mkt.gsProposals (mkt.gsStep R))) := by
  cases hbest : mkt.bestW w (mkt.gsProposals R) with
  | none => exact mkt.none_le_bestW w _
  | some m =>
      have hh : (m, w) ∈ mkt.gsHeld R :=
        ⟨mkt.gs_bestW_mem hbest, hbest.symm⟩
      exact mkt.le_bestW_of_mem
        (mkt.some_mem_menuW.mpr (mkt.gs_held_proposes_next hh))

/-- Every rejected man lies strictly below the woman's current best proposal.
This is the classical invariant that prevents a rejected pair from blocking
the terminal matching. -/
theorem gs_rejected_below_holding (n : ℕ) {m : M} {w : W}
    (hR : (m, w) ∈ mkt.gsRejected n) :
    mkt.ltW w (some m)
      (mkt.bestW w (mkt.gsProposals (mkt.gsRejected n))) := by
  letI := mkt.prefW w
  revert hR
  induction n with
  | zero => intro hR; exact False.elim hR
  | succ n ih =>
      intro hR
      rw [mkt.gsRejected_succ] at hR ⊢
      apply lt_of_lt_of_le _ (mkt.gs_women_improve (mkt.gsRejected n) w)
      rcases hR with hR | ⟨hp, hnh⟩
      · exact ih hR
      · have hle : some m ≤ mkt.bestW w (mkt.gsProposals (mkt.gsRejected n)) :=
          mkt.le_bestW_of_mem (mkt.some_mem_menuW.mpr hp)
        exact lt_of_le_of_ne hle (fun heq => hnh ⟨hp, heq⟩)

/-! ## The classical first-rejection argument -/

omit [Fintype M] in
/-- If a rejection history avoids a matching, each man's next proposal is at
least as good as his assignment in that matching. -/
theorem gs_assignment_le_proposal {R : Set (M × W)} {ν : M ≃. W}
    (hR : ∀ p ∈ R, p ∉ mkt.graphOf ν) (m : M) :
    mkt.leM m (ν m) (mkt.bestM m Rᶜ) := by
  cases hνm : ν m with
  | none => exact mkt.none_le_bestM m _
  | some w =>
      have hn : (m, w) ∉ R :=
        fun hr => hR (m, w) hr (mkt.mem_graphOf.mpr hνm)
      exact mkt.le_bestM_of_mem (mkt.some_mem_menuM.mpr hn)

/-- A single proposal round preserves the absence of stable pairs from the
rejection history. If a woman rejected her stable partner for another man,
that man and woman would block the alleged stable matching. -/
theorem gs_step_avoids_stable {R : Set (M × W)} {ν : M ≃. W}
    (hν : mkt.IsStableMatching ν)
    (hR : ∀ p ∈ R, p ∉ mkt.graphOf ν) :
    ∀ p ∈ mkt.gsStep R, p ∉ mkt.graphOf ν := by
  rintro ⟨m, w⟩ (hr | ⟨hp, hnh⟩) hpair
  · exact hR (m, w) hr hpair
  · have hνw : ν.symm w = some m := mkt.mem_graphOf_symm.mp hpair
    have hstrict : mkt.ltW w (some m) (mkt.bestW w (mkt.gsProposals R)) := by
      letI := mkt.prefW w
      have hle : some m ≤ mkt.bestW w (mkt.gsProposals R) :=
        mkt.le_bestW_of_mem (mkt.some_mem_menuW.mpr hp)
      exact lt_of_le_of_ne hle (fun heq => hnh ⟨hp, heq⟩)
    cases hbest : mkt.bestW w (mkt.gsProposals R) with
    | none =>
        letI := mkt.prefW w
        have hir : (none : Option M) ≤ some m := by
          have := hν.1.2 w
          simpa only [IndividuallyRationalForW, hνw] using this
        have hlt : some m < (none : Option M) := by
          simpa only [hbest] using hstrict
        exact (not_lt_of_ge hir) hlt
    | some m' =>
        have hp' : (m', w) ∈ mkt.gsProposals R := mkt.gs_bestW_mem hbest
        have hbestM : some w = mkt.bestM m' Rᶜ := hp'
        have hw : mkt.ltW w (ν.symm w) (some m') := by
          simpa only [hνw, hbest] using hstrict
        have hm : mkt.ltM m' (ν m') (some w) := by
          letI := mkt.prefM m'
          have hle : ν m' ≤ some w := by
            have := mkt.gs_assignment_le_proposal hR m'
            simpa only [← hbestM] using this
          apply lt_of_le_of_ne hle
          intro heq
          have he : m = m' :=
            mkt.graphOf_leftUnique ν hpair (mkt.mem_graphOf.mpr heq)
          subst m'
          letI := mkt.prefW w
          have hbad : some m < some m := by simpa only [hνw] using hw
          exact (lt_irrefl _) hbad
        exact hν.2.1 m' w ⟨hm, hw⟩

/-- No pair belonging to a stable matching is ever rejected. -/
theorem gs_rejected_not_mem_stable (n : ℕ) {ν : M ≃. W}
    (hν : mkt.IsStableMatching ν) :
    ∀ p ∈ mkt.gsRejected n, p ∉ mkt.graphOf ν := by
  induction n with
  | zero => intro p hp; exact False.elim hp
  | succ n ih =>
      rw [mkt.gsRejected_succ]
      exact mkt.gs_step_avoids_stable hν ih

/-! ## Termination and the terminal matching -/

/-- A terminal proposal round retains every proposal. -/
theorem gs_held_of_terminal {R : Set (M × W)}
    (hR : IsFixedPt mkt.gsStep R) {m : M} {w : W}
    (hp : (m, w) ∈ mkt.gsProposals R) : (m, w) ∈ mkt.gsHeld R := by
  classical
  by_contra hn
  have hmem : (m, w) ∈ mkt.gsStep R := Or.inr ⟨hp, hn⟩
  rw [hR] at hmem
  exact mkt.gs_proposal_not_rejected hp hmem

/-- At a terminal round the men's and women's selected partners are inverse
partial maps, hence constitute a classical matching. -/
noncomputable def gsMatchingAt (R : Set (M × W))
    (hR : IsFixedPt mkt.gsStep R) : M ≃. W where
  toFun m := mkt.bestM m Rᶜ
  invFun w := mkt.bestW w (mkt.gsProposals R)
  inv := by
    intro m w
    constructor
    · intro h
      have hp : some w = mkt.bestM m Rᶜ := mkt.gs_bestW_mem h
      exact hp.symm
    · intro h
      exact (mkt.gs_held_of_terminal hR h.symm).2.symm

@[simp] theorem gsMatchingAt_apply (R : Set (M × W))
    (hR : IsFixedPt mkt.gsStep R) (m : M) :
    mkt.gsMatchingAt R hR m = mkt.bestM m Rᶜ := rfl

@[simp] theorem gsMatchingAt_symm_apply (R : Set (M × W))
    (hR : IsFixedPt mkt.gsStep R) (w : W) :
    (mkt.gsMatchingAt R hR).symm w = mkt.bestW w (mkt.gsProposals R) := rfl

theorem graphOf_gsMatchingAt (R : Set (M × W))
    (hR : IsFixedPt mkt.gsStep R) :
    mkt.graphOf (mkt.gsMatchingAt R hR) = mkt.gsProposals R := by
  ext p
  change mkt.bestM p.1 Rᶜ = some p.2 ↔ some p.2 = mkt.bestM p.1 Rᶜ
  exact eq_comm

/-- Finitely many pairs imply that some rejection round is terminal. The
argument only uses inflationarity, not monotonicity of the rejection map. -/
theorem gs_exists_terminal :
    ∃ n, IsFixedPt mkt.gsStep (mkt.gsRejected n) := by
  obtain ⟨n, hn⟩ := Function.exists_iterate_succ_eq_of_inflationary
    mkt.gsStep mkt.gs_subset_step (∅ : Set (M × W))
  refine ⟨n, ?_⟩
  change mkt.gsStep (mkt.gsStep^[n] ∅) = mkt.gsStep^[n] ∅
  exact (Function.iterate_succ_apply' mkt.gsStep n ∅).symm.trans hn

/-- Every terminal round reached from the empty rejection history gives a
stable matching. This proof uses the classical holding invariant. -/
theorem stable_gsMatchingAt (n : ℕ)
    (hn : IsFixedPt mkt.gsStep (mkt.gsRejected n)) :
    mkt.IsStableMatching (mkt.gsMatchingAt (mkt.gsRejected n) hn) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro m
    exact mkt.none_le_bestM m _
  · intro w
    exact mkt.none_le_bestW w _
  · apply (mkt.unblocked_iff_no_blockingPair _).mpr
    intro m w hblock
    have hrej : (m, w) ∈ mkt.gsRejected n := by
      classical
      by_contra hnot
      letI := mkt.prefM m
      have hle : some w ≤ mkt.bestM m (mkt.gsRejected n)ᶜ :=
        mkt.le_bestM_of_mem (mkt.some_mem_menuM.mpr hnot)
      exact (not_lt_of_ge hle) hblock.1
    letI := mkt.prefW w
    have hlt := mkt.gs_rejected_below_holding n hrej
    exact (lt_asymm hlt) hblock.2

/-- The classical first-rejection invariant yields man-optimality. -/
theorem gsMatchingAt_manOptimal (n : ℕ)
    (hn : IsFixedPt mkt.gsStep (mkt.gsRejected n))
    {ν : M ≃. W} (hν : mkt.IsStableMatching ν) (m : M) :
    mkt.leM m (ν m) (mkt.gsMatchingAt (mkt.gsRejected n) hn m) :=
  mkt.gs_assignment_le_proposal (mkt.gs_rejected_not_mem_stable n hν) m

/-- Any terminal round reached by the algorithm has the same output. -/
theorem gsMatchingAt_eq_manOptimalMatching (n : ℕ)
    (hn : IsFixedPt mkt.gsStep (mkt.gsRejected n)) :
    mkt.gsMatchingAt (mkt.gsRejected n) hn = mkt.manOptimalMatching := by
  apply PEquiv.ext
  intro m
  letI := mkt.prefM m
  exact le_antisymm
    (mkt.le_manOptimalMatching (mkt.stable_gsMatchingAt n hn) m)
    (mkt.gsMatchingAt_manOptimal n hn mkt.stable_manOptimalMatching m)

/-- A uniform bound on simultaneous rejection updates: each nonstationary
update adds a previously unrejected pair. This is a fuel bound for the state
iteration, not a running-time bound or a count of individual proposals. -/
def gsStoppingTime (_mkt : MarriageMarket M W) : ℕ := Fintype.card (M × W)

theorem gs_stoppingTime_terminal :
    IsFixedPt mkt.gsStep (mkt.gsRejected mkt.gsStoppingTime) := by
  exact Function.isFixedPt_iterate_card_of_inflationary mkt.gsStep mkt.gs_subset_step

/-- The output of the classical man-proposing Gale–Shapley algorithm. -/
noncomputable def galeShapley : M ≃. W :=
  mkt.gsMatchingAt (mkt.gsRejected mkt.gsStoppingTime) mkt.gs_stoppingTime_terminal

theorem stable_galeShapley : mkt.IsStableMatching mkt.galeShapley :=
  mkt.stable_gsMatchingAt mkt.gsStoppingTime mkt.gs_stoppingTime_terminal

theorem galeShapley_manOptimal {ν : M ≃. W}
    (hν : mkt.IsStableMatching ν) (m : M) :
    mkt.leM m (ν m) (mkt.galeShapley m) :=
  mkt.gsMatchingAt_manOptimal mkt.gsStoppingTime mkt.gs_stoppingTime_terminal hν m

/-- The classical and contracts proofs compute the same man-optimal matching. -/
theorem galeShapley_eq_manOptimalMatching :
    mkt.galeShapley = mkt.manOptimalMatching :=
  mkt.gsMatchingAt_eq_manOptimalMatching mkt.gsStoppingTime mkt.gs_stoppingTime_terminal

/-- At the uniform stopping bound, the proposal graph is the contracts
seller-optimal outcome. This is an equality of terminal outcomes; it does not
assert that the classical and generalized iterations coincide round by round. -/
theorem gs_terminal_proposals_eq_sellerOptimal :
    mkt.gsProposals (mkt.gsRejected mkt.gsStoppingTime) =
      mkt.toMarket.sellerOptimal mkt.substitutable_toMarket := by
  calc mkt.gsProposals (mkt.gsRejected mkt.gsStoppingTime)
      = mkt.graphOf mkt.galeShapley :=
          (mkt.graphOf_gsMatchingAt _ mkt.gs_stoppingTime_terminal).symm
    _ = mkt.graphOf mkt.manOptimalMatching :=
      congrArg mkt.graphOf mkt.galeShapley_eq_manOptimalMatching
    _ = _ := mkt.graphOf_manOptimalMatching

/-- The named output of the classical algorithm agrees with the generalized
deferred-acceptance endpoint supplied by the marriage instance. -/
theorem galeShapley_eq_deferredAcceptance :
    mkt.galeShapley = mkt.deferredAcceptance :=
  mkt.galeShapley_eq_manOptimalMatching

/-- The generalized iteration eventually has the classical algorithm's
terminal graph as its outcome. No equality of intermediate rounds is needed. -/
theorem exists_generalized_round_eq_galeShapley :
    ∃ n, mkt.deferredAcceptanceOutcome n = mkt.graphOf mkt.galeShapley := by
  rw [mkt.galeShapley_eq_deferredAcceptance]
  exact mkt.exists_deferredAcceptanceOutcome_eq_graph

/-- Woman-proposing Gale–Shapley is the same proposal algorithm with the two
sides exchanged, then transported back to an `M ≃. W` matching. -/
noncomputable def womanGaleShapley : M ≃. W :=
  mkt.symm.galeShapley.symm

theorem womanGaleShapley_eq_womanOptimalMatching :
    mkt.womanGaleShapley = mkt.womanOptimalMatching := by
  simp only [womanGaleShapley, galeShapley_eq_manOptimalMatching,
    manOptimalMatching_symm, PEquiv.symm_symm]

/-- The woman-proposing classical algorithm agrees with its generalized
deferred-acceptance endpoint. -/
theorem womanGaleShapley_eq_womanProposingDeferredAcceptance :
    mkt.womanGaleShapley = mkt.womanProposingDeferredAcceptance :=
  mkt.womanGaleShapley_eq_womanOptimalMatching

/-- The buyer-proposing generalized iteration eventually carries the graph
computed by the woman-proposing classical algorithm. -/
theorem exists_generalized_woman_round_eq_womanGaleShapley :
    ∃ n, mkt.womanProposingDeferredAcceptanceOutcome n =
      mkt.graphOf mkt.womanGaleShapley := by
  rw [mkt.womanGaleShapley_eq_womanOptimalMatching]
  exact mkt.exists_womanProposingDeferredAcceptanceOutcome_eq_graph

theorem stable_womanGaleShapley : mkt.IsStableMatching mkt.womanGaleShapley := by
  rw [mkt.womanGaleShapley_eq_womanOptimalMatching]
  exact mkt.stable_womanOptimalMatching

theorem womanGaleShapley_womanOptimal {ν : M ≃. W}
    (hν : mkt.IsStableMatching ν) (w : W) :
    mkt.leW w (ν.symm w) (mkt.womanGaleShapley.symm w) := by
  rw [mkt.womanGaleShapley_eq_womanOptimalMatching]
  exact mkt.le_womanOptimalMatching hν w

theorem galeShapley_eq_womanPessimalMatching :
    mkt.galeShapley = mkt.womanPessimalMatching :=
  mkt.galeShapley_eq_manOptimalMatching.trans
    mkt.manOptimalMatching_eq_womanPessimalMatching

theorem womanGaleShapley_eq_manPessimalMatching :
    mkt.womanGaleShapley = mkt.manPessimalMatching :=
  mkt.womanGaleShapley_eq_womanOptimalMatching.trans
    mkt.womanOptimalMatching_eq_manPessimalMatching

end MarriageMarket
