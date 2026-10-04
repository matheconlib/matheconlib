import MatchingTheory.Classical.DeferredAcceptance

/-!
# Executable finite Gale–Shapley deferred acceptance

The semantic algorithm in `DeferredAcceptance` uses sets and noncomputable
preference-induced choice. Here menus, proposals, and rejections are finite
sets. Each agent's supplied `LinearOrder` decides comparisons, and explicit
`DecidableEq` instances decide finite membership; the algorithm uses no
classical choice.

`gsRejectedFinset n` performs exactly `n` simultaneous proposal rounds.
`galeShapleyFinset` evaluates the held contracts at the rejection state
reached after `card (M × W)` rounds.
The coercion theorems identify every finite state with the corresponding
semantic state, so the correctness proof applies to the executable function.

This implementation deliberately uses simple exhaustive menus. Its purpose
is a transparent executable refinement, not the usual optimized running-time
bound for preference lists and proposal queues.
-/

open Function

universe u v

namespace MarriageMarket

variable {M : Type u} {W : Type v}
variable (mkt : MarriageMarket M W)
variable [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]

set_option linter.unusedVariables false in
/-- A man's finite menu, including the outside option. -/
def menuMFinset (mkt : MarriageMarket M W) (m : M)
    (Y : Finset (M × W)) : Finset (Option W) :=
  Finset.univ.filter fun o => o = none ∨ ∃ w, o = some w ∧ (m, w) ∈ Y

set_option linter.unusedVariables false in
/-- A woman's finite menu, including the outside option. -/
def menuWFinset (mkt : MarriageMarket M W) (w : W)
    (Y : Finset (M × W)) : Finset (Option M) :=
  Finset.univ.filter fun o => o = none ∨ ∃ m, o = some m ∧ (m, w) ∈ Y

omit [Fintype M] in
theorem menuMFinset_nonempty (m : M) (Y : Finset (M × W)) :
    (mkt.menuMFinset m Y).Nonempty := by
  exact ⟨none, by simp [menuMFinset]⟩

omit [Fintype W] in
theorem menuWFinset_nonempty (w : W) (Y : Finset (M × W)) :
    (mkt.menuWFinset w Y).Nonempty := by
  exact ⟨none, by simp [menuWFinset]⟩

/-- Computable best option according to the man's supplied order. -/
def bestMFinset (m : M) (Y : Finset (M × W)) : Option W := by
  letI := mkt.prefM m
  exact (mkt.menuMFinset m Y).max' (mkt.menuMFinset_nonempty m Y)

/-- Computable best option according to the woman's supplied order. -/
def bestWFinset (w : W) (Y : Finset (M × W)) : Option M := by
  letI := mkt.prefW w
  exact (mkt.menuWFinset w Y).max' (mkt.menuWFinset_nonempty w Y)

omit [Fintype M] in
theorem menuMFinset_eq_menuM (m : M) (Y : Finset (M × W)) :
    mkt.menuMFinset m Y = mkt.menuM m (Y : Set (M × W)) := by
  classical
  ext o
  simp [menuMFinset, menuM]

omit [Fintype W] in
theorem menuWFinset_eq_menuW (w : W) (Y : Finset (M × W)) :
    mkt.menuWFinset w Y = mkt.menuW w (Y : Set (M × W)) := by
  classical
  ext o
  simp [menuWFinset, menuW]

omit [Fintype M] in
@[simp] theorem bestMFinset_eq_bestM (m : M) (Y : Finset (M × W)) :
    mkt.bestMFinset m Y = mkt.bestM m (Y : Set (M × W)) := by
  classical
  simp only [bestMFinset, bestM, menuMFinset_eq_menuM]

omit [Fintype W] in
@[simp] theorem bestWFinset_eq_bestW (w : W) (Y : Finset (M × W)) :
    mkt.bestWFinset w Y = mkt.bestW w (Y : Set (M × W)) := by
  classical
  simp only [bestWFinset, bestW, menuWFinset_eq_menuW]

/-- Each man proposes to his best partner who has not rejected him.
Choosing `none` produces no proposal. -/
def gsProposalsFinset (R : Finset (M × W)) : Finset (M × W) :=
  Finset.univ.filter fun p =>
    some p.2 = mkt.bestMFinset p.1 (Finset.univ \ R)

/-- Each woman holds her best acceptable proposal, if any. -/
def gsHeldFinset (R : Finset (M × W)) : Finset (M × W) :=
  (mkt.gsProposalsFinset R).filter fun p =>
    some p.1 = mkt.bestWFinset p.2 (mkt.gsProposalsFinset R)

/-- Add every unheld proposal to the rejected contracts. -/
def gsStepFinset (R : Finset (M × W)) : Finset (M × W) :=
  R ∪ (mkt.gsProposalsFinset R \ mkt.gsHeldFinset R)

/-- The executable rejection state after `n` simultaneous rounds. -/
def gsRejectedFinset (n : ℕ) : Finset (M × W) :=
  (mkt.gsStepFinset)^[n] ∅

private theorem coe_univ_sdiff (R : Finset (M × W)) :
    ((Finset.univ \ R : Finset (M × W)) : Set (M × W)) =
      (R : Set (M × W))ᶜ := by
  ext p
  simp

@[simp] theorem coe_gsProposalsFinset (R : Finset (M × W)) :
    (mkt.gsProposalsFinset R : Set (M × W)) =
      mkt.gsProposals (R : Set (M × W)) := by
  classical
  ext p
  change p ∈ mkt.gsProposalsFinset R ↔
    some p.2 = mkt.bestM p.1 (R : Set (M × W))ᶜ
  simp only [gsProposalsFinset, Finset.mem_filter, Finset.mem_univ,
    true_and, bestMFinset_eq_bestM, coe_univ_sdiff]

@[simp] theorem coe_gsHeldFinset (R : Finset (M × W)) :
    (mkt.gsHeldFinset R : Set (M × W)) =
      mkt.gsHeld (R : Set (M × W)) := by
  classical
  have hp (p : M × W) : p ∈ mkt.gsProposalsFinset R ↔
      p ∈ mkt.gsProposals (R : Set (M × W)) := by
    change p ∈ (mkt.gsProposalsFinset R : Set (M × W)) ↔ _
    rw [coe_gsProposalsFinset]
  ext p
  simp [gsHeldFinset, gsHeld, hp]

@[simp] theorem coe_gsStepFinset (R : Finset (M × W)) :
    (mkt.gsStepFinset R : Set (M × W)) =
      mkt.gsStep (R : Set (M × W)) := by
  classical
  ext p
  simp [gsStepFinset, gsStep]

/-- Every executable rejection state agrees with the semantic algorithm. -/
@[simp] theorem coe_gsRejectedFinset (n : ℕ) :
    (mkt.gsRejectedFinset n : Set (M × W)) = mkt.gsRejected n := by
  induction n with
  | zero =>
      simp [gsRejectedFinset, gsRejected]
  | succ n ih =>
      simp only [gsRejectedFinset, gsRejected, Function.iterate_succ_apply']
      rw [coe_gsStepFinset]
      exact congrArg mkt.gsStep ih

/-- Execute a bounded number of rejection rounds, then evaluate the held
contracts at the resulting state. -/
def galeShapleyFinsetWithFuel (n : ℕ) : Finset (M × W) :=
  mkt.gsHeldFinset (mkt.gsRejectedFinset n)

@[simp] theorem coe_galeShapleyFinsetWithFuel (n : ℕ) :
    (mkt.galeShapleyFinsetWithFuel n : Set (M × W)) =
      mkt.gsHeld (mkt.gsRejected n) := by
  simp only [galeShapleyFinsetWithFuel, coe_gsHeldFinset, coe_gsRejectedFinset]

/-- Run Gale–Shapley for the number of possible contracts. -/
def galeShapleyFinset : Finset (M × W) :=
  mkt.galeShapleyFinsetWithFuel (Fintype.card (M × W))

theorem coe_galeShapleyFinset :
    (mkt.galeShapleyFinset : Set (M × W)) =
      mkt.gsHeld (mkt.gsRejected (Fintype.card (M × W))) := by
  exact mkt.coe_galeShapleyFinsetWithFuel _

/-- A terminal finite state has inverse partner selections. -/
theorem gs_inverseFinset {R : Finset (M × W)}
    (hR : IsFixedPt mkt.gsStep (R : Set (M × W))) (m : M) (w : W) :
    mkt.bestWFinset w (mkt.gsProposalsFinset R) = some m ↔
      mkt.bestMFinset m (Finset.univ \ R) = some w := by
  rw [bestWFinset_eq_bestW, bestMFinset_eq_bestM,
    coe_gsProposalsFinset, coe_univ_sdiff]
  constructor
  · intro h
    have hp : some w = mkt.bestM m (R : Set (M × W))ᶜ :=
      mkt.gs_bestW_mem h
    exact hp.symm
  · intro h
    exact (mkt.gs_held_of_terminal hR h.symm).2.symm

/-- Executable Gale–Shapley with a `PEquiv` result. Both partner maps are
computed from finite menus; the inverse proof is erased during execution. -/
def galeShapleyComputable : M ≃. W where
  toFun m := mkt.bestMFinset m
    (Finset.univ \ mkt.gsRejectedFinset (Fintype.card (M × W)))
  invFun w := mkt.bestWFinset w
    (mkt.gsProposalsFinset (mkt.gsRejectedFinset (Fintype.card (M × W))))
  inv := by
    intro m w
    apply mkt.gs_inverseFinset
    rw [coe_gsRejectedFinset]
    exact mkt.gs_stoppingTime_terminal

/-- Executable and semantic Gale–Shapley produce the same partial equivalence. -/
theorem galeShapleyComputable_eq_galeShapley :
    mkt.galeShapleyComputable = mkt.galeShapley := by
  apply PEquiv.ext
  intro m
  change mkt.bestMFinset m
      (Finset.univ \ mkt.gsRejectedFinset (Fintype.card (M × W))) =
    mkt.bestM m (mkt.gsRejected mkt.gsStoppingTime)ᶜ
  simp only [bestMFinset_eq_bestM, coe_univ_sdiff, coe_gsRejectedFinset,
    gsStoppingTime]

/-- The executable algorithm computes the generalized man-optimal endpoint. -/
theorem galeShapleyComputable_eq_manOptimalMatching :
    mkt.galeShapleyComputable = mkt.manOptimalMatching :=
  mkt.galeShapleyComputable_eq_galeShapley.trans
    mkt.galeShapley_eq_manOptimalMatching

theorem galeShapleyComputable_eq_deferredAcceptance :
    mkt.galeShapleyComputable = mkt.deferredAcceptance :=
  mkt.galeShapleyComputable_eq_galeShapley.trans
    mkt.galeShapley_eq_deferredAcceptance

theorem galeShapleyComputable_eq_womanPessimalMatching :
    mkt.galeShapleyComputable = mkt.womanPessimalMatching :=
  mkt.galeShapleyComputable_eq_galeShapley.trans
    mkt.galeShapley_eq_womanPessimalMatching

theorem stable_galeShapleyComputable :
    mkt.IsStableMatching mkt.galeShapleyComputable := by
  rw [mkt.galeShapleyComputable_eq_galeShapley]
  exact mkt.stable_galeShapley

theorem galeShapleyComputable_manOptimal {ν : M ≃. W}
    (hν : mkt.IsStableMatching ν) (m : M) :
    mkt.leM m (ν m) (mkt.galeShapleyComputable m) := by
  rw [mkt.galeShapleyComputable_eq_galeShapley]
  exact mkt.galeShapley_manOptimal hν m

/-- The finite graph returned by the algorithm is the man-optimal graph. -/
theorem galeShapleyFinset_eq_graphOf_manOptimalMatching :
    (mkt.galeShapleyFinset : Set (M × W)) =
      mkt.graphOf mkt.manOptimalMatching := by
  rw [coe_galeShapleyFinset]
  have hh : mkt.gsHeld (mkt.gsRejected mkt.gsStoppingTime) =
      mkt.gsProposals (mkt.gsRejected mkt.gsStoppingTime) := by
    apply Set.Subset.antisymm
    · intro p hp
      exact hp.1
    · rintro ⟨m, w⟩ hp
      exact mkt.gs_held_of_terminal mkt.gs_stoppingTime_terminal hp
  change mkt.gsHeld (mkt.gsRejected mkt.gsStoppingTime) = _
  rw [hh, mkt.gs_terminal_proposals_eq_sellerOptimal,
    mkt.graphOf_manOptimalMatching]

/-- Executable woman-proposing Gale–Shapley, transported from the market with
the two sides exchanged. -/
def womanGaleShapleyComputable : M ≃. W :=
  mkt.symm.galeShapleyComputable.symm

theorem womanGaleShapleyComputable_eq_womanGaleShapley :
    mkt.womanGaleShapleyComputable = mkt.womanGaleShapley := by
  unfold womanGaleShapleyComputable womanGaleShapley
  rw [mkt.symm.galeShapleyComputable_eq_galeShapley]

theorem womanGaleShapleyComputable_eq_womanProposingDeferredAcceptance :
    mkt.womanGaleShapleyComputable = mkt.womanProposingDeferredAcceptance :=
  mkt.womanGaleShapleyComputable_eq_womanGaleShapley.trans
    mkt.womanGaleShapley_eq_womanProposingDeferredAcceptance

/-- The executable woman-proposing algorithm computes the woman-optimal,
man-pessimal stable matching. -/
theorem womanGaleShapleyComputable_eq_womanOptimalMatching :
    mkt.womanGaleShapleyComputable = mkt.womanOptimalMatching :=
  mkt.womanGaleShapleyComputable_eq_womanGaleShapley.trans
    mkt.womanGaleShapley_eq_womanOptimalMatching

theorem womanGaleShapleyComputable_eq_manPessimalMatching :
    mkt.womanGaleShapleyComputable = mkt.manPessimalMatching :=
  mkt.womanGaleShapleyComputable_eq_womanGaleShapley.trans
    mkt.womanGaleShapley_eq_manPessimalMatching

theorem stable_womanGaleShapleyComputable :
    mkt.IsStableMatching mkt.womanGaleShapleyComputable := by
  rw [mkt.womanGaleShapleyComputable_eq_womanOptimalMatching]
  exact mkt.stable_womanOptimalMatching

theorem womanGaleShapleyComputable_womanOptimal {ν : M ≃. W}
    (hν : mkt.IsStableMatching ν) (w : W) :
    mkt.leW w (ν.symm w) (mkt.womanGaleShapleyComputable.symm w) := by
  rw [mkt.womanGaleShapleyComputable_eq_womanOptimalMatching]
  exact mkt.le_womanOptimalMatching hν w

end MarriageMarket
