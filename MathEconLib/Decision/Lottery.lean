/-
Copyright (c) 2026 Ritik Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ritik Jain
-/
module

public import MathEconLib.Probability.FinDist.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Degenerate and binary lotteries

A lottery over a finite set of prizes `Z` is a distribution `FinDist Z`; the probability of `z`
under `p` is `p.pmf z`. `FinDist.pure z` is the sure lottery `[z]` and `FinDist.mixture α p q`
the compound lottery `α · p ⊕ (1 − α) · q`.

## Main definitions

* `degenerate`, `binary`: the lotteries `[z]` and `α · a ⊕ (1 − α) · b`.

## Main statements

* `degenerate_subset_binary`: every degenerate lottery is binary.
* `exists_mixture_pure_eq_mixture`: for `β < α`, two binary lotteries over the same prizes are
  mixtures, with probability `α − β`, of `[a]` and `[b]` with one common lottery.

## References

* M. J. Osborne, A. Rubinstein, *Models in Microeconomic Theory* (2023), Sections 3.1 and 3.2
-/

@[expose] public section

namespace MathEconLib.Decision

open MathEconLib.Probability

universe u

variable {Z : Type u} [Fintype Z] [DecidableEq Z] {p : FinDist Z}

/-- The degenerate lotteries `[z]`. -/
def degenerate : Set (FinDist Z) := Set.range FinDist.pure

/-- The lotteries `α · a ⊕ (1 − α) · b` over two prizes `a`, `b` (which may coincide). -/
def binary : Set (FinDist Z) :=
  Set.range fun x : unitInterval × Z × Z =>
    FinDist.mixture x.1 (FinDist.pure x.2.1) (FinDist.pure x.2.2)

theorem mem_degenerate : p ∈ degenerate ↔ ∃ z, FinDist.pure z = p := Iff.rfl

@[simp]
theorem pure_mem_degenerate (z : Z) : FinDist.pure z ∈ (degenerate : Set (FinDist Z)) :=
  ⟨z, rfl⟩

theorem mem_binary :
    p ∈ binary ↔ ∃ (α : unitInterval) (a b : Z),
      FinDist.mixture α (FinDist.pure a) (FinDist.pure b) = p :=
  ⟨fun ⟨x, hx⟩ => ⟨x.1, x.2.1, x.2.2, hx⟩, fun ⟨α, a, b, h⟩ => ⟨(α, a, b), h⟩⟩

@[simp]
theorem mixture_mem_binary (α : unitInterval) (a b : Z) :
    FinDist.mixture α (FinDist.pure a) (FinDist.pure b) ∈ (binary : Set (FinDist Z)) :=
  ⟨(α, a, b), rfl⟩

theorem degenerate_subset_binary : (degenerate : Set (FinDist Z)) ⊆ binary := by
  rintro _ ⟨z, rfl⟩
  exact ⟨(1, z, z), FinDist.mixture_one _ _⟩

/-- For `β < α`, `α · a ⊕ (1 − α) · b` and `β · a ⊕ (1 − β) · b` mix `[a]` and `[b]`, with
probability `α − β`, with one common lottery. -/
theorem exists_mixture_pure_eq_mixture (a b : Z) {α β : unitInterval} (hβα : (β : ℝ) < α)
    (hα : (α : ℝ) - β < 1) :
    ∃ (t β' : unitInterval), (t : ℝ) = α - β ∧
      FinDist.mixture α (FinDist.pure a) (FinDist.pure b) = FinDist.mixture t (FinDist.pure a)
        (FinDist.mixture β' (FinDist.pure a) (FinDist.pure b)) ∧
      FinDist.mixture β (FinDist.pure a) (FinDist.pure b) = FinDist.mixture t (FinDist.pure b)
        (FinDist.mixture β' (FinDist.pure a) (FinDist.pure b)) := by
  have h1 : (0 : ℝ) < 1 - (α - β) := by linarith
  refine ⟨⟨α - β, Set.mem_Icc.2 ⟨by linarith, by linarith [α.2.2, β.2.1]⟩⟩,
    ⟨β / (1 - (α - β)), Set.mem_Icc.2 ⟨div_nonneg β.2.1 h1.le,
      (div_le_one h1).2 (by linarith [α.2.2])⟩⟩, rfl, ?_, ?_⟩ <;>
  · refine FinDist.ext _ _ fun z => ?_
    simp only [FinDist.mixture_pmf]
    field_simp
    ring

end MathEconLib.Decision

/-! ### Worked examples -/

section Examples

open MathEconLib.Probability MathEconLib.Decision

example : (FinDist.mixture ⟨0.6, by norm_num, by norm_num⟩ (FinDist.pure (0 : Fin 3))
      (FinDist.pure 2)).pmf 0 = 0.6 ∧
    (FinDist.mixture ⟨0.6, by norm_num, by norm_num⟩ (FinDist.pure (0 : Fin 3))
      (FinDist.pure 2)).pmf 1 = 0 := by
  simp only [FinDist.mixture_pmf, FinDist.pure_pmf]
  norm_num

example (b : Fin 3) :
    FinDist.mixture ⟨0.6, by norm_num, by norm_num⟩ (FinDist.pure b) (FinDist.pure b) =
      FinDist.pure b :=
  FinDist.mixture_self _ _

example (α : unitInterval) (q : FinDist (Fin 3)) (hq : q.pmf 0 = 0.2) :
    (FinDist.mixture α (FinDist.mixture ⟨0.6, by norm_num, by norm_num⟩ (FinDist.pure 0)
      (FinDist.pure 2)) q).pmf 0 = α * 0.6 + (1 - α) * 0.2 := by
  simp only [FinDist.mixture_pmf, FinDist.pure_pmf, hq]
  norm_num

example (p q : FinDist (Fin 2)) : FinDist.mixture 0 p q = q := FinDist.mixture_zero p q

/-- A binary lottery has at most two prizes in its support. -/
example (p : FinDist (Fin 3)) (hp : p ∈ binary) : p.support.card ≤ 2 := by
  obtain ⟨α, a, b, rfl⟩ := mem_binary.1 hp
  calc (FinDist.mixture α (FinDist.pure a) (FinDist.pure b)).support.card
        ≤ ({a, b} : Finset (Fin 3)).card := by
        refine Finset.card_le_card fun z hz => ?_
        simp only [FinDist.support, Finset.mem_filter, Finset.mem_univ, true_and] at hz
        simp only [Finset.mem_insert, Finset.mem_singleton]
        by_contra h
        rw [not_or] at h
        simp only [FinDist.mixture_pmf, FinDist.pure_pmf, Ne.symm h.1, Ne.symm h.2, ite_false,
          mul_zero, add_zero, lt_self_iff_false] at hz
    _ ≤ 2 := Finset.card_le_two

end Examples
