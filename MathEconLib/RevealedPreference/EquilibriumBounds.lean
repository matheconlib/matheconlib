/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

/-!
# A common point for finite open and closed bounds

A finite family of real lower and upper bounds has a common point whenever
every lower bound is compatible with every upper bound. A pair involving an
open endpoint must be strictly ordered. This includes empty families and
coincident closed endpoints, as required by finite linear elimination.
-/

@[expose] public section

set_option autoImplicit false

namespace MathEconLib.RevealedPreference.Equilibrium.FiniteLinearSystem

/-- A weak comparison, made strict when its flag is true. -/
def Rel (strict : Bool) (a b : ℝ) : Prop := a ≤ b ∧ (strict = true → a < b)

/-- A strictly satisfied comparison satisfies either strictness flag. -/
theorem rel_of_lt (strict : Bool) {a b : ℝ} (h : a < b) : Rel strict a b :=
  ⟨h.le, fun _ => h⟩

/-- Pairwise compatibility of finite lower and upper bounds provides a common
point satisfying every open or closed endpoint constraint. -/
theorem exists_between_finite_bounds (lower upper : Finset (ℝ × Bool))
    (h : ∀ l ∈ lower, ∀ u ∈ upper, Rel (l.2 || u.2) l.1 u.1) :
    ∃ z : ℝ, (∀ l ∈ lower, Rel l.2 l.1 z) ∧ (∀ u ∈ upper, Rel u.2 z u.1) := by
  classical
  by_cases hl : lower.Nonempty
  · obtain ⟨l, hlmem, hlmax⟩ := lower.exists_max_image Prod.fst hl
    by_cases hu : upper.Nonempty
    · obtain ⟨u, humem, humin⟩ := upper.exists_min_image Prod.fst hu
      have hlu := h l hlmem u humem
      by_cases heq : l.1 = u.1
      · refine ⟨l.1, ?_, ?_⟩
        · intro a ha
          refine ⟨hlmax a ha, fun hs => ?_⟩
          have hstrict := (h a ha u humem).2 (by simp [hs])
          exact hstrict.trans_le heq.symm.le
        · intro b hb
          refine ⟨heq.le.trans (humin b hb), fun hs => ?_⟩
          exact (h l hlmem b hb).2 (by simp [hs])
      · obtain ⟨z, hlz, hzu⟩ := exists_between (lt_of_le_of_ne hlu.1 heq)
        exact ⟨z, fun a ha => rel_of_lt _ ((hlmax a ha).trans_lt hlz),
          fun b hb => rel_of_lt _ (hzu.trans_le (humin b hb))⟩
    · refine ⟨l.1 + 1, fun a ha => rel_of_lt _ ?_, ?_⟩
      · have := hlmax a ha
        linarith
      · intro b hb
        exact (hu ⟨b, hb⟩).elim
  · by_cases hu : upper.Nonempty
    · obtain ⟨u, _, humin⟩ := upper.exists_min_image Prod.fst hu
      refine ⟨u.1 - 1, ?_, fun b hb => rel_of_lt _ ?_⟩
      · intro a ha
        exact (hl ⟨a, ha⟩).elim
      · have := humin b hb
        linarith
    · exact ⟨0, fun a ha => (hl ⟨a, ha⟩).elim, fun b hb => (hu ⟨b, hb⟩).elim⟩

end MathEconLib.RevealedPreference.Equilibrium.FiniteLinearSystem
