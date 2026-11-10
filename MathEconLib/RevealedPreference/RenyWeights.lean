/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLib.RevealedPreference.RenyStrictness
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Tactic

/-!
# Positive, finite-mass margins for rational strong pairs

The countable rational-pair strictness device in Gonczarowski, Kominers, and
Shorrer (2025), "To infinity and beyond: A general framework for scaling
economic theories", Theoretical Economics 20, Theorem 8, prescribes positive
utility gaps before applying compactness. Here an injective natural-number
coding assigns dyadic gaps whose sum over every finite subfamily is at most
one half. Only finite geometric sums are used.

## References and Lean provenance

Yannai A. Gonczarowski, Scott Duke Kominers and Ran I. Shorrer (2025),
*To infinity and beyond: A general framework for scaling economic theories*,
Theoretical Economics **20**(2), 511–542, Theorem 8.
[DOI: 10.3982/TE5878](https://doi.org/10.3982/TE5878).

Ported from Victor H. Aguiar's Apache-2.0 Lean development
[WGARP Lean](https://github.com/vaguiarl/wgarp-lean), module `RenyWeights`.
-/

@[expose] public section

set_option autoImplicit false

namespace MathEconLib.RevealedPreference

open Finset

/-- The finite partial-sum identity for the margin schedule. -/
private theorem reny_dyadic_range_sum (n : ℕ) :
    ∑ k ∈ range n, (1 / 2 : ℝ) ^ (k + 2) =
      1 / 2 - (1 / 2 : ℝ) ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [sum_range_succ, ih]
    simp only [Nat.succ_add, pow_succ]
    ring

/-- Any finite selection of distinct dyadic margins has total mass at most
one half; a nonconsecutive selection needs no infinite-series argument. -/
private theorem reny_dyadic_finset_sum_le_half (S : Finset ℕ) :
    ∑ k ∈ S, (1 / 2 : ℝ) ^ (k + 2) ≤ 1 / 2 := by
  have hsub : S ⊆ range (S.sup id + 1) := by
    intro k hk
    exact mem_range.mpr (Nat.lt_succ_of_le (le_sup (f := id) hk))
  calc
    ∑ k ∈ S, (1 / 2 : ℝ) ^ (k + 2) ≤
        ∑ k ∈ range (S.sup id + 1), (1 / 2 : ℝ) ^ (k + 2) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = 1 / 2 - (1 / 2 : ℝ) ^ (S.sup id + 1 + 1) :=
      reny_dyadic_range_sum _
    _ ≤ 1 / 2 := sub_le_self _ (by positivity)

/-- Every countable index set admits positive weights with uniformly bounded
finite-subfamily mass. No enumeration without repetitions is assumed. -/
private theorem exists_positive_finiteSum_le_half (J : Type*) [Countable J] :
    ∃ w : J → ℝ, (∀ j, 0 < w j) ∧
      ∀ K : Finset J, ∑ j ∈ K, w j ≤ 1 / 2 := by
  classical
  obtain ⟨code, hcode⟩ := exists_injective_nat J
  refine ⟨fun j => (1 / 2 : ℝ) ^ (code j + 2), ?_, ?_⟩
  · intro j
    positivity
  · intro K
    calc
      ∑ j ∈ K, (1 / 2 : ℝ) ^ (code j + 2) =
          ∑ n ∈ K.image code, (1 / 2 : ℝ) ^ (n + 2) :=
        by
          symm
          apply sum_image
          intro a ha b hb h
          exact hcode h
      _ ≤ 1 / 2 := reny_dyadic_finset_sum_le_half _

/-- Positive rational-pair utility gaps can be fixed once and for all while
retaining the finite mass budget needed by finite-step normalization. -/
theorem exists_rationalStrongPair_margins (L : ℕ) :
    ∃ w : RationalStrongPair L → ℝ, (∀ ab, 0 < w ab) ∧
      ∀ K : Finset (RationalStrongPair L), ∑ ab ∈ K, w ab ≤ 1 / 2 :=
  exists_positive_finiteSum_le_half _

end MathEconLib.RevealedPreference
