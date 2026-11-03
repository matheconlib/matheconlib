/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
module

public import MathEconLib.ForMathlib.Order.IterateFixedPoint
public import Mathlib.Data.Set.Card

/-!
# A finite bound for inflationary set iteration

An inflationary update on subsets of a finite type reaches a fixed point
within `Fintype.card X` updates from the empty set. Each nonstationary step
adds an element, so no monotonicity of the update map is required. This
provides a computable fuel bound for proposal/rejection algorithms.
-/

@[expose] public section

open Function

/-- An inflationary set update that is not stationary strictly increases
natural cardinality on a finite carrier. -/
theorem Function.ncard_lt_apply_of_inflationary {X : Type*} [Finite X]
    (f : Set X → Set X) (hf : ∀ A, A ⊆ f A) {A : Set X}
    (hne : ¬ IsFixedPt f A) : A.ncard < (f A).ncard := by
  apply lt_of_le_of_ne (Set.ncard_le_ncard (hf A) (Set.toFinite _))
  intro heq
  apply hne
  exact (Set.eq_of_subset_of_ncard_le (hf A) heq.ge (Set.toFinite _)).symm

/-- After at most one update per element, an inflationary iteration from
`∅` has stabilized. The update need not be monotone as a function of sets. -/
theorem Function.isFixedPt_iterate_card_of_inflationary {X : Type*}
    [Fintype X] (f : Set X → Set X) (hf : ∀ A, A ⊆ f A) :
    IsFixedPt f (f^[Fintype.card X] ∅) := by
  have hgrow : ∀ n : ℕ, ¬ IsFixedPt f (f^[n] ∅) →
      n + 1 ≤ (f^[n + 1] ∅).ncard := by
    intro n
    induction n with
    | zero =>
        intro hnot
        have hlt := Function.ncard_lt_apply_of_inflationary f hf hnot
        simpa using Nat.succ_le_of_lt hlt
    | succ n ih =>
        intro hnot
        have hprev : ¬ IsFixedPt f (f^[n] ∅) := by
          intro hfix
          apply hnot
          change f (f^[n + 1] ∅) = f^[n + 1] ∅
          simpa only [Function.iterate_succ_apply'] using congrArg f hfix
        have hlt := Function.ncard_lt_apply_of_inflationary f hf hnot
        have hbound := Nat.succ_le_of_lt (lt_of_le_of_lt (ih hprev) hlt)
        simpa only [Function.iterate_succ_apply'] using hbound
  by_contra hnot
  have hlarge := hgrow (Fintype.card X) hnot
  have hsmall : (f^[Fintype.card X + 1] ∅).ncard ≤ Fintype.card X := by
    simpa only [Nat.card_eq_fintype_card] using
      Set.ncard_le_card (f^[Fintype.card X + 1] ∅)
  exact Nat.not_succ_le_self _ (hlarge.trans hsmall)
