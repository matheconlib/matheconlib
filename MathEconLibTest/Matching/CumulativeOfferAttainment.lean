/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/

import MathEconLib.Matching

/-!
# Attainment boundaries for cumulative offers

The same countable carrier gives a finite unoffered menu, a tie with the outside
option, and two infinite menus without a refined optimum. Only the infinite menu
with weak maximizers still permits a relational proposal.
-/

namespace MathEconLibTest.Matching.CumulativeOfferAttainment

open MathEconLib.Choice MathEconLib.Choice.ChoiceFunction MathEconLib.Preferences
open MathEconLib.Matching.CumulativeOffer
open CumulativeOfferProcess

private def natSeller (_ : ℕ) : Unit := ()

private def process (utility : Option ℕ → ℕ) : CumulativeOfferProcess Unit Unit ℕ where
  buyer _ := ()
  seller := natSeller
  choiceB _ := ⟨fun _ ↦ ∅, fun _ ↦ Set.empty_subset _⟩
  pref _ := CompletePreference.ofUtility (fun o ↦ utility (o.map Subtype.val))

private abbrev increasing := process (fun o ↦ o.elim 0 Nat.succ)
private abbrev tied := process (fun o ↦ o.elim 0 (fun _ ↦ 1))
private abbrev outsideTie := process (fun _ ↦ 0)

private theorem noHeld (utility : Option ℕ → ℕ) (A : Set ℕ) (s : Unit) :
    (process utility).NoHeldContract A s := by
  rintro x ⟨b, hx⟩
  exact hx.elim

private theorem increasing_eligible (A : Set ℕ) (h0 : 0 ∉ A) : increasing.Eligible A () :=
  ⟨noHeld _ A (), ⟨0, rfl⟩, h0, Nat.zero_le _, Nat.not_le_of_gt (Nat.succ_pos _)⟩

private theorem increasing_noWeakBest (s : Unit) (x : increasing.Own s) :
    x ∉ maximizers (increasing.contractPreference s) (increasing.remaining ∅ s) := by
  intro hx
  cases s
  let y : increasing.Own () := ⟨x.val + 1, rfl⟩
  have hy : y ∈ increasing.remaining ∅ () :=
    ⟨by simp, Nat.zero_le _, Nat.not_le_of_gt (Nat.succ_pos _)⟩
  exact Nat.not_succ_le_self _ (hx.2 hy)

private theorem tied_weakBest (x : tied.Own ()) :
    x ∈ maximizers (tied.contractPreference ()) (tied.remaining ∅ ()) :=
  ⟨⟨by simp, Nat.zero_le _, Nat.not_le_of_gt Nat.one_pos⟩,
    fun {_} _ ↦ (le_rfl : (1 : ℕ) ≤ 1)⟩

private theorem noOptimumOfEmpty (P : CumulativeOfferProcess Unit Unit ℕ)
    (h : P.Eligible ∅ ()) (hempty :
      ofOptionLinearOrder (P.proposalOrder inferInstance ()) (P.unofferedOwnMenu ∅ ()) = ∅) :
    ¬ HasBundleOptimum (P.proposalOrder inferInstance ()) optionBundle
      (P.unofferedOwnMenu ∅ ()) := by
  intro hatt
  have hout := (ofOptionLinearOrder_eq_empty_iff_of_hasBundleOptimum _ hatt).mp hempty
  exact (P.outsideOptionOptimal_tieBreak_iff ∅ () (P.proposalPriority ())
    (fun _ ↦ le_top)).mp hout h.2

-- The single unoffered contract attains even though the contract type is infinite.
example : ∃ x, increasing.seller x = () ∧ increasing.ValidBatch {n | n ≠ 0} {x} := by
  let A : Set ℕ := {n | n ≠ 0}
  have hfin : (increasing.unofferedOwnMenu A ()).Finite := by
    apply (Set.finite_singleton (⟨0, rfl⟩ : increasing.Own ())).subset
    intro x hx
    apply Set.mem_singleton_iff.mpr
    apply Subtype.ext
    by_contra hne
    exact hx hne
  exact (increasing_eligible A (by simp [A])).exists_validSingleton_of_hasBundleOptimum
    increasing (increasing.proposalPriority ()) (fun _ ↦ le_top)
    (increasing.hasBundleOptimum_unofferedOwnMenu_of_finite
      (increasing.proposalOrder inferInstance ()) hfin)

-- When every contract ties with the outside option, declining is attained and terminal.
example : outsideTie.Terminal ∅ ∧
    OutsideOptionOptimal (outsideTie.proposalOrder inferInstance ())
      (outsideTie.unofferedOwnMenu ∅ ()) ∧
    HasBundleOptimum (outsideTie.proposalOrder inferInstance ()) optionBundle
      (outsideTie.unofferedOwnMenu ∅ ()) := by
  have decline (s : Unit) :
      OutsideOptionOptimal (outsideTie.proposalOrder inferInstance s)
        (outsideTie.unofferedOwnMenu ∅ s) := by
    intro x _
    exact (outsideTie.tieBreak_some_le_none_iff (outsideTie.proposalPriority s)
      (fun _ ↦ le_top) x).mpr (le_rfl : (0 : ℕ) ≤ 0)
  exact ⟨(outsideTie.terminal_iff_sellerDeclines outsideTie.proposalPriority
    (fun _ _ ↦ le_top) ∅).mpr (fun s _ ↦ decline s), decline (),
    (decline ()).hasBundleOptimum⟩

-- Strictly increasing utility gives no weak maximizer and no valid proposal.
example : ¬ increasing.Terminal ∅ ∧ (∀ Q, ¬ increasing.ValidBatch ∅ Q) ∧
    ¬ HasBundleOptimum (increasing.proposalOrder inferInstance ()) optionBundle
      (increasing.unofferedOwnMenu ∅ ()) := by
  have h := increasing_eligible ∅ (by simp)
  refine ⟨fun ht ↦ ht () h, ?_, noOptimumOfEmpty increasing h ?_⟩
  · intro Q hQ
    obtain ⟨x, hx⟩ := hQ.1
    obtain ⟨s, y, _, _, hy⟩ := hQ.2.1 x hx
    exact increasing_noWeakBest s y hy
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact increasing_noWeakBest () x
      ((increasing.mem_tieBreak_optionChoice_iff ∅ () (increasing.proposalPriority ())
        (fun _ ↦ le_top) x).mp hx).1

-- Tied acceptable contracts admit weak steps, while their priorities have no greatest element.
example : ¬ tied.Terminal ∅ ∧ tied.ValidBatch ∅ {0} ∧
    ¬ HasBundleOptimum (tied.proposalOrder inferInstance ()) optionBundle
      (tied.unofferedOwnMenu ∅ ()) := by
  let zero : tied.Own () := ⟨0, rfl⟩
  have h : tied.Eligible ∅ () := ⟨noHeld _ ∅ (), zero, (tied_weakBest zero).1⟩
  refine ⟨fun ht ↦ ht () h, (tied.validBatch_singleton_iff ∅ 0).mpr
    ⟨(), zero, rfl, h.1, tied_weakBest zero⟩, noOptimumOfEmpty tied h ?_⟩
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  let y : tied.Own () := ⟨x.val + 1, rfl⟩
  have hle := ((tied.mem_tieBreak_optionChoice_iff ∅ () (tied.proposalPriority ())
    (fun _ ↦ le_top) x).mp hx).2 y (tied_weakBest y)
  exact Nat.not_succ_le_self _ (WithTop.coe_le_coe.mp hle)

-- A client of the matching umbrella can compare the two selectors.
example {B S X : Type*} [Finite X] (P : CumulativeOfferProcess B S X)
    (priority : LinearOrder X) (A : Set X) (s : S) (h : P.Eligible A s) :
    Subtype.val '' ofOptionLinearOrder (P.proposalOrder priority s) (P.unofferedOwnMenu A s) =
      {P.selectOffer priority A s h} :=
  P.ofOptionLinearOrder_proposalOrder_eq_singleton_selectOffer priority A s h

end MathEconLibTest.Matching.CumulativeOfferAttainment
