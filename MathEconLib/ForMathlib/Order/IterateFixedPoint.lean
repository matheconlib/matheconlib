/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
module

public import Mathlib.Order.FixedPoints
public import Mathlib.Order.Iterate
public import Mathlib.Order.OrderIsoNat
public import Mathlib.Data.Fintype.Card

/-!
# Finite convergence to extremal fixed points

A monotone self-map of a finite complete lattice reaches its greatest fixed
point from the top and its least fixed point from the bottom. No market or
choice-theoretic definitions enter these results. These are existence
statements for a stopping index, not an executable fixed-point solver.
-/

@[expose] public section

open Function OrderDual

/-- A monotone sequence in a finite partial order has consecutive equal terms.
This specializes Mathlib's monotone chain condition and is shared by both
kinds of iteration below. -/
theorem Monotone.exists_succ_eq_of_finite {L : Type*}
    [PartialOrder L] [Finite L] {f : ℕ → L} (hf : Monotone f) :
    ∃ n, f (n + 1) = f n := by
  obtain ⟨n, hn⟩ :=
    WellFoundedGT.monotone_chain_condition (⟨f, hf⟩ : ℕ →o L)
  exact ⟨n, (hn (n + 1) (Nat.le_succ n)).symm⟩

/-- The decreasing-sequence form is the same theorem on the order dual. -/
theorem Antitone.exists_succ_eq_of_finite {L : Type*}
    [PartialOrder L] [Finite L] {f : ℕ → L} (hf : Antitone f) :
    ∃ n, f (n + 1) = f n :=
  Monotone.exists_succ_eq_of_finite (L := Lᵒᵈ) hf

/-- A monotone self-map of a finite complete lattice reaches its greatest
fixed point by iterating from `⊤`.

This result is independent of matching theory. -/
theorem OrderHom.exists_iterate_top_eq_gfp {L : Type*} [CompleteLattice L]
    [Finite L] (f : L →o L) :
    ∃ n, (f : L → L)^[n] ⊤ = OrderHom.gfp f := by
  have hanti : Antitone (fun n : ℕ => (f : L → L)^[n] (⊤ : L)) :=
    f.monotone.antitone_iterate_of_map_le le_top
  obtain ⟨k, hk⟩ := hanti.exists_succ_eq_of_finite
  have hfix : IsFixedPt (f : L → L) ((f : L → L)^[k] ⊤) :=
    (Function.iterate_succ_apply' (f : L → L) k ⊤).symm.trans hk
  refine ⟨k, le_antisymm (f.isGreatest_gfp.2 hfix) ?_⟩
  calc
    OrderHom.gfp f = (f : L → L)^[k] (OrderHom.gfp f) :=
      (Function.iterate_fixed f.isFixedPt_gfp k).symm
    _ ≤ (f : L → L)^[k] ⊤ := f.monotone.iterate k le_top

/-- Iteration from `⊥` reaches the least fixed point, by applying
the top-iteration theorem to the order dual. -/
theorem OrderHom.exists_iterate_bot_eq_lfp {L : Type*} [CompleteLattice L]
    [Finite L] (f : L →o L) :
    ∃ n, (f : L → L)^[n] ⊥ = OrderHom.lfp f := by
  exact OrderHom.exists_iterate_top_eq_gfp (L := Lᵒᵈ) f.dual

/-- An inflationary self-map of a finite partial order has a stationary
iterate from any initial state. Unlike monotone fixed-point theorems, this
requires no comparison between the images of two different states. -/
theorem Function.exists_iterate_succ_eq_of_inflationary {L : Type*}
    [PartialOrder L] [Finite L] (f : L → L)
    (hf : ∀ x, x ≤ f x) (a : L) :
    ∃ n, f^[n + 1] a = f^[n] a := by
  have hmono : Monotone (fun n : ℕ => f^[n] a) :=
    fun _ _ h => Function.monotone_iterate_of_id_le hf h a
  exact hmono.exists_succ_eq_of_finite
