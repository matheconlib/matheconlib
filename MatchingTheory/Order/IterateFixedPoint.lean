import Mathlib.Order.FixedPoints
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Finite convergence to extremal fixed points

A monotone self-map of a finite complete lattice reaches its greatest fixed
point from the top and its least fixed point from the bottom. No market or
choice-theoretic definitions enter these results. These are existence
statements for a stopping index, not an executable fixed-point solver.
-/

open Function OrderDual

/-- A monotone sequence in a finite partial order has consecutive equal terms.
This is the common finite-chain argument behind both kinds of iteration below. -/
theorem Monotone.exists_succ_eq_of_finite {L : Type*}
    [PartialOrder L] [Finite L] {f : ℕ → L} (hf : Monotone f) :
    ∃ n, f (n + 1) = f n := by
  obtain ⟨m, n, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite f
  rcases lt_trichotomy m n with hlt | heq' | hlt
  · refine ⟨m, le_antisymm ?_ (hf (Nat.le_succ m))⟩
    exact (hf (Nat.succ_le_of_lt hlt)).trans heq.ge
  · exact (hne heq').elim
  · refine ⟨n, le_antisymm ?_ (hf (Nat.le_succ n))⟩
    exact (hf (Nat.succ_le_of_lt hlt)).trans heq.le

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
  classical
  -- the iterates are antitone
  have hstep : ∀ n : ℕ, (f : L → L)^[n + 1] ⊤ ≤ (f : L → L)^[n] ⊤ := by
    intro n
    induction n with
    | zero => exact le_top
    | succ k ih =>
        calc (f : L → L)^[k + 1 + 1] (⊤ : L)
            = f ((f : L → L)^[k + 1] ⊤) := Function.iterate_succ_apply' _ _ _
          _ ≤ f ((f : L → L)^[k] ⊤) := f.monotone ih
          _ = (f : L → L)^[k + 1] ⊤ := (Function.iterate_succ_apply' _ _ _).symm
  have hanti : Antitone (fun n : ℕ => (f : L → L)^[n] (⊤ : L)) :=
    antitone_nat_of_succ_le hstep
  have hge : ∀ k : ℕ, OrderHom.gfp f ≤ (f : L → L)^[k] ⊤ := by
    intro k
    induction k with
    | zero => exact le_top
    | succ j ih =>
        calc OrderHom.gfp f = f (OrderHom.gfp f) := f.isGreatest_gfp.1.symm
          _ ≤ f ((f : L → L)^[j] ⊤) := f.monotone ih
          _ = (f : L → L)^[j + 1] ⊤ := (Function.iterate_succ_apply' _ _ _).symm
  obtain ⟨k, hk⟩ := hanti.exists_succ_eq_of_finite
  refine ⟨k, le_antisymm ?_ (hge k)⟩
  have hfix : IsFixedPt (f : L → L) ((f : L → L)^[k] ⊤) :=
    (Function.iterate_succ_apply' (f : L → L) k ⊤).symm.trans hk
  exact f.isGreatest_gfp.2 hfix

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
  have hstep (n : ℕ) : f^[n] a ≤ f^[n + 1] a := by
    rw [Function.iterate_succ_apply']
    exact hf _
  have hmono : Monotone (fun n : ℕ => f^[n] a) :=
    monotone_nat_of_le_succ hstep
  exact hmono.exists_succ_eq_of_finite
