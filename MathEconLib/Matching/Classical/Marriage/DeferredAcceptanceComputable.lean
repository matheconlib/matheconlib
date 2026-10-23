/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
import MathEconLib.Matching.Classical.Marriage.DeferredAcceptanceFixedPoints
import MathEconLib.Choice.FiniteOption

/-!
# Executable finite Gale–Shapley deferred acceptance

The semantic algorithm in `DeferredAcceptance` uses sets and noncomputable
preference-induced choice. Here menus, proposals, and rejections are finite
sets. Each agent's supplied `LinearOrder` decides comparisons, and explicit
`DecidableEq` instances decide finite membership; the algorithm uses no
classical choice.

`gsRejectedFinset n` performs exactly `n` simultaneous rejection updates.
`galeShapleyFinset` evaluates the held contracts at the rejection state
reached after `card (M × W)` rounds.
The coercion theorems identify every finite state with the corresponding
semantic state. Both the direct classical correctness proof and the separate
contracts-inherited proof therefore apply to the executable function.

Partner menus are extracted from the supplied finite contracts, and their
maxima use the general finite-option selection interface. Each rejection
round still enumerates potential proposals. This is a transparent executable
refinement, without a claim about optimized preference-list running time.
-/

namespace MathEconLib.Matching

open MathEconLib.Choice

open Function

universe u v

namespace MarriageMarket

variable {M : Type u} {W : Type v}
variable (mkt : MarriageMarket M W)
variable [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]

/-- Partners represented in a man's supplied finite contract menu. -/
def partnersMFinset (m : M) (Y : Finset (M × W)) : Finset W :=
  (Y.filter fun p => p.1 = m).image Prod.snd

/-- Partners represented in a woman's supplied finite contract menu. -/
def partnersWFinset (w : W) (Y : Finset (M × W)) : Finset M :=
  (Y.filter fun p => p.2 = w).image Prod.fst

omit [Fintype M] [Fintype W] in
@[simp] theorem mem_partnersMFinset {m : M} {w : W} {Y : Finset (M × W)} :
    w ∈ partnersMFinset m Y ↔ (m, w) ∈ Y := by
  constructor
  · intro hw
    obtain ⟨⟨m', w'⟩, hp, he⟩ := Finset.mem_image.mp hw
    obtain ⟨hY, hm⟩ := Finset.mem_filter.mp hp
    dsimp only at hm he
    cases hm
    cases he
    exact hY
  · intro hY
    exact Finset.mem_image.mpr
      ⟨(m, w), Finset.mem_filter.mpr ⟨hY, rfl⟩, rfl⟩

omit [Fintype M] [Fintype W] in
@[simp] theorem mem_partnersWFinset {m : M} {w : W} {Y : Finset (M × W)} :
    m ∈ partnersWFinset w Y ↔ (m, w) ∈ Y := by
  constructor
  · intro hm
    obtain ⟨⟨m', w'⟩, hp, he⟩ := Finset.mem_image.mp hm
    obtain ⟨hY, hw⟩ := Finset.mem_filter.mp hp
    dsimp only at hw he
    cases hw
    cases he
    exact hY
  · intro hY
    exact Finset.mem_image.mpr
      ⟨(m, w), Finset.mem_filter.mpr ⟨hY, rfl⟩, rfl⟩

set_option linter.unusedVariables false in
/-- A man's finite menu, including the outside option. -/
def menuMFinset (mkt : MarriageMarket M W) (m : M)
    (Y : Finset (M × W)) : Finset (Option W) :=
  ChoiceFunction.optionMenu (partnersMFinset m Y)

set_option linter.unusedVariables false in
/-- A woman's finite menu, including the outside option. -/
def menuWFinset (mkt : MarriageMarket M W) (w : W)
    (Y : Finset (M × W)) : Finset (Option M) :=
  ChoiceFunction.optionMenu (partnersWFinset w Y)

omit [Fintype M] [Fintype W] in
theorem menuMFinset_nonempty (m : M) (Y : Finset (M × W)) :
    (mkt.menuMFinset m Y).Nonempty := by
  exact ⟨none, by simp [menuMFinset]⟩

omit [Fintype W] [Fintype M] in
theorem menuWFinset_nonempty (w : W) (Y : Finset (M × W)) :
    (mkt.menuWFinset w Y).Nonempty := by
  exact ⟨none, by simp [menuWFinset]⟩

/-- Computable best option according to the man's supplied order. -/
def bestMFinset (m : M) (Y : Finset (M × W)) : Option W :=
  ChoiceFunction.bestOption (mkt.prefM m) (partnersMFinset m Y)

/-- Computable best option according to the woman's supplied order. -/
def bestWFinset (w : W) (Y : Finset (M × W)) : Option M :=
  ChoiceFunction.bestOption (mkt.prefW w) (partnersWFinset w Y)

omit [Fintype M] in
theorem menuMFinset_eq_menuM (m : M) (Y : Finset (M × W)) :
    mkt.menuMFinset m Y = mkt.menuM m (Y : Set (M × W)) := by
  classical
  ext o
  cases o <;> simp [menuMFinset, menuM]

omit [Fintype W] in
theorem menuWFinset_eq_menuW (w : W) (Y : Finset (M × W)) :
    mkt.menuWFinset w Y = mkt.menuW w (Y : Set (M × W)) := by
  classical
  ext o
  cases o <;> simp [menuWFinset, menuW]

omit [Fintype M] in
@[simp] theorem bestMFinset_eq_bestM (m : M) (Y : Finset (M × W)) :
    mkt.bestMFinset m Y = mkt.bestM m (Y : Set (M × W)) := by
  classical
  let := mkt.prefM m
  apply le_antisymm
  · apply mkt.le_bestM_of_mem
    rw [← mkt.menuMFinset_eq_menuM m Y]
    exact ChoiceFunction.bestOption_mem (mkt.prefM m) _
  · apply ChoiceFunction.le_bestOption (mkt.prefM m)
    change mkt.bestM m (Y : Set (M × W)) ∈ mkt.menuMFinset m Y
    rw [mkt.menuMFinset_eq_menuM]
    exact mkt.bestM_mem_menuM m _

omit [Fintype W] in
@[simp] theorem bestWFinset_eq_bestW (w : W) (Y : Finset (M × W)) :
    mkt.bestWFinset w Y = mkt.bestW w (Y : Set (M × W)) := by
  classical
  let := mkt.prefW w
  apply le_antisymm
  · apply mkt.le_bestW_of_mem
    rw [← mkt.menuWFinset_eq_menuW w Y]
    exact ChoiceFunction.bestOption_mem (mkt.prefW w) _
  · apply ChoiceFunction.le_bestOption (mkt.prefW w)
    change mkt.bestW w (Y : Set (M × W)) ∈ mkt.menuWFinset w Y
    rw [mkt.menuWFinset_eq_menuW]
    exact mkt.bestW_mem_menuW w _

/-- Each man proposes to his best partner who has not rejected him.
Choosing `none` produces no proposal. -/
def gsProposalsFinset (R : Finset (M × W)) : Finset (M × W) :=
  Finset.univ.filter fun p =>
    some p.2 = mkt.bestMFinset p.1 (Finset.univ \ R)

/-- Each woman selects her best acceptable contract from the supplied proposals. -/
def gsHoldProposalsFinset (P : Finset (M × W)) : Finset (M × W) :=
  P.filter fun p => some p.1 = mkt.bestWFinset p.2 P

/-- Each woman holds her best acceptable proposal, if any. -/
def gsHeldFinset (R : Finset (M × W)) : Finset (M × W) :=
  mkt.gsHoldProposalsFinset (mkt.gsProposalsFinset R)

/-- Add every unheld proposal to the rejected contracts. -/
def gsStepFinset (R : Finset (M × W)) : Finset (M × W) :=
  let P := mkt.gsProposalsFinset R
  R ∪ (P \ mkt.gsHoldProposalsFinset P)

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
  simp [gsHeldFinset, gsHoldProposalsFinset, gsHeld, hp]

@[simp] theorem coe_gsStepFinset (R : Finset (M × W)) :
    (mkt.gsStepFinset R : Set (M × W)) =
      mkt.gsStep (R : Set (M × W)) := by
  classical
  change ((R ∪ (mkt.gsProposalsFinset R \ mkt.gsHeldFinset R) :
    Finset (M × W)) : Set (M × W)) = _
  ext p
  simp [gsStep]

/-- Every executable rejection state agrees with the semantic algorithm. -/
@[simp] theorem coe_gsRejectedFinset (n : ℕ) :
    (mkt.gsRejectedFinset n : Set (M × W)) = mkt.gsRejected n := by
  have hstep : Function.Semiconj (fun R : Finset (M × W) => (R : Set (M × W)))
      mkt.gsStepFinset mkt.gsStep := mkt.coe_gsStepFinset
  simpa only [gsRejectedFinset, gsRejected, Finset.coe_empty] using
    hstep.iterate_right n (∅ : Finset (M × W))

/-- Return the held contracts after `n` rejection updates.
The supplied fuel may stop before stabilization. `galeShapleyFinset`
uses a bound proved sufficient for a terminal state. -/
def galeShapleyFinsetWithFuel (n : ℕ) : Finset (M × W) :=
  mkt.gsHeldFinset (mkt.gsRejectedFinset n)

@[simp] theorem coe_galeShapleyFinsetWithFuel (n : ℕ) :
    (mkt.galeShapleyFinsetWithFuel n : Set (M × W)) =
      mkt.gsHeld (mkt.gsRejected n) := by
  simp only [galeShapleyFinsetWithFuel, coe_gsHeldFinset, coe_gsRejectedFinset]

/-- Run `Fintype.card (M × W)` rejection updates and return the held
contracts. This fuel bound guarantees a terminal rejection state. -/
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
  exact (mkt.gsMatchingAt (R : Set (M × W)) hR).inv m w

/-- Executable Gale–Shapley with a `PEquiv` result. Both partner maps are
computed from the same final rejection state and proposal set; the inverse
proof is erased during execution. -/
def galeShapleyComputable : M ≃. W :=
  let R := mkt.gsRejectedFinset (Fintype.card (M × W))
  let P := mkt.gsProposalsFinset R
  { toFun := fun m => mkt.bestMFinset m (Finset.univ \ R)
    invFun := fun w => mkt.bestWFinset w P
    inv := by
      intro m w
      apply mkt.gs_inverseFinset
      change IsFixedPt mkt.gsStep
        (mkt.gsRejectedFinset (Fintype.card (M × W)) : Set (M × W))
      rw [coe_gsRejectedFinset]
      exact mkt.galeShapleyRoundBound_terminal }

/-- Executable and semantic Gale–Shapley produce the same partial equivalence. -/
theorem galeShapleyComputable_eq_galeShapley :
    mkt.galeShapleyComputable = mkt.galeShapley := by
  apply PEquiv.ext
  intro m
  change mkt.bestMFinset m
      (Finset.univ \ mkt.gsRejectedFinset (Fintype.card (M × W))) =
    mkt.bestM m (mkt.gsRejected mkt.galeShapleyRoundBound)ᶜ
  simp only [bestMFinset_eq_bestM, coe_univ_sdiff, coe_gsRejectedFinset,
    galeShapleyRoundBound]

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

theorem isManOptimal_galeShapleyComputable :
    mkt.IsManOptimal mkt.galeShapleyComputable := by
  rw [mkt.galeShapleyComputable_eq_galeShapley]
  exact mkt.isManOptimal_galeShapley

theorem isWomanPessimal_galeShapleyComputable :
    mkt.IsWomanPessimal mkt.galeShapleyComputable := by
  rw [mkt.galeShapleyComputable_eq_galeShapley]
  exact mkt.isWomanPessimal_galeShapley

theorem galeShapleyComputable_womanPessimal {ν : M ≃. W}
    (hν : mkt.IsStableMatching ν) (w : W) :
    mkt.leW w (mkt.galeShapleyComputable.symm w) (ν.symm w) := by
  rw [mkt.galeShapleyComputable_eq_galeShapley]
  exact mkt.galeShapley_womanPessimal hν w

/-- The finite graph and executable partial equivalence represent the same
semantic terminal matching. -/
theorem galeShapleyFinset_eq_graphOf_galeShapley :
    (mkt.galeShapleyFinset : Set (M × W)) =
      mkt.graphOf mkt.galeShapley := by
  rw [coe_galeShapleyFinset]
  exact (mkt.graphOf_gsMatchingAt_eq_held
    (mkt.gsRejected mkt.galeShapleyRoundBound) mkt.galeShapleyRoundBound_terminal).symm

theorem galeShapleyFinset_eq_graphOf_galeShapleyComputable :
    (mkt.galeShapleyFinset : Set (M × W)) =
      mkt.graphOf mkt.galeShapleyComputable := by
  rw [mkt.galeShapleyComputable_eq_galeShapley]
  exact mkt.galeShapleyFinset_eq_graphOf_galeShapley

/-- The finite graph returned by the algorithm is the man-optimal graph. -/
theorem galeShapleyFinset_eq_graphOf_manOptimalMatching :
    (mkt.galeShapleyFinset : Set (M × W)) =
      mkt.graphOf mkt.manOptimalMatching := by
  rw [mkt.galeShapleyFinset_eq_graphOf_galeShapley,
    mkt.galeShapley_eq_manOptimalMatching]

/-- Executable woman-proposing Gale–Shapley, obtained from the market with
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
  rw [mkt.womanGaleShapleyComputable_eq_womanGaleShapley]
  exact mkt.stable_womanGaleShapley

theorem womanGaleShapleyComputable_womanOptimal {ν : M ≃. W}
    (hν : mkt.IsStableMatching ν) (w : W) :
    mkt.leW w (ν.symm w) (mkt.womanGaleShapleyComputable.symm w) := by
  rw [mkt.womanGaleShapleyComputable_eq_womanGaleShapley]
  exact mkt.womanGaleShapley_womanOptimal hν w

theorem isWomanOptimal_womanGaleShapleyComputable :
    mkt.IsWomanOptimal mkt.womanGaleShapleyComputable := by
  rw [mkt.womanGaleShapleyComputable_eq_womanGaleShapley]
  exact mkt.isWomanOptimal_womanGaleShapley

theorem isManPessimal_womanGaleShapleyComputable :
    mkt.IsManPessimal mkt.womanGaleShapleyComputable := by
  rw [mkt.womanGaleShapleyComputable_eq_womanGaleShapley]
  exact mkt.isManPessimal_womanGaleShapley

theorem womanGaleShapleyComputable_manPessimal {ν : M ≃. W}
    (hν : mkt.IsStableMatching ν) (m : M) :
    mkt.leM m (mkt.womanGaleShapleyComputable m) (ν m) := by
  rw [mkt.womanGaleShapleyComputable_eq_womanGaleShapley]
  exact mkt.womanGaleShapley_manPessimal hν m

/-! ## Correctness inherited from generalized deferred acceptance

The executable-to-semantic refinement above is shared by both proof routes.
These statements use the fixed-point correspondence and inherited economic
results; the earlier correctness statements retain the direct classical route.
-/

theorem galeShapleyComputable_eq_deferredAcceptance_via_fixedPoints :
    mkt.galeShapleyComputable = mkt.deferredAcceptance :=
  mkt.galeShapleyComputable_eq_galeShapley.trans
    mkt.galeShapley_eq_deferredAcceptance_via_fixedPoints

theorem womanGaleShapleyComputable_eq_womanProposingDeferredAcceptance_via_fixedPoints :
    mkt.womanGaleShapleyComputable = mkt.womanProposingDeferredAcceptance :=
  mkt.womanGaleShapleyComputable_eq_womanGaleShapley.trans
    mkt.womanGaleShapley_eq_womanProposingDeferredAcceptance_via_fixedPoints

theorem stable_galeShapleyComputable_via_fixedPoints :
    mkt.IsStableMatching mkt.galeShapleyComputable := by
  rw [mkt.galeShapleyComputable_eq_galeShapley]
  exact mkt.stable_galeShapley_via_fixedPoints

theorem isManOptimal_galeShapleyComputable_via_fixedPoints :
    mkt.IsManOptimal mkt.galeShapleyComputable := by
  rw [mkt.galeShapleyComputable_eq_galeShapley]
  exact mkt.isManOptimal_galeShapley_via_fixedPoints

theorem isWomanPessimal_galeShapleyComputable_via_fixedPoints :
    mkt.IsWomanPessimal mkt.galeShapleyComputable := by
  rw [mkt.galeShapleyComputable_eq_galeShapley]
  exact mkt.isWomanPessimal_galeShapley_via_fixedPoints

theorem stable_womanGaleShapleyComputable_via_fixedPoints :
    mkt.IsStableMatching mkt.womanGaleShapleyComputable := by
  rw [mkt.womanGaleShapleyComputable_eq_womanGaleShapley]
  exact mkt.stable_womanGaleShapley_via_fixedPoints

theorem isWomanOptimal_womanGaleShapleyComputable_via_fixedPoints :
    mkt.IsWomanOptimal mkt.womanGaleShapleyComputable := by
  rw [mkt.womanGaleShapleyComputable_eq_womanGaleShapley]
  exact mkt.isWomanOptimal_womanGaleShapley_via_fixedPoints

theorem isManPessimal_womanGaleShapleyComputable_via_fixedPoints :
    mkt.IsManPessimal mkt.womanGaleShapleyComputable := by
  rw [mkt.womanGaleShapleyComputable_eq_womanGaleShapley]
  exact mkt.isManPessimal_womanGaleShapley_via_fixedPoints

end MarriageMarket

end MathEconLib.Matching
