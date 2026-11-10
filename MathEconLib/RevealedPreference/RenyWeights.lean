/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLib.RevealedPreference.RenyStrictness
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Positive, finite-mass margins for rational strong pairs

The countable rational-pair strictness device in Gonczarowski, Kominers, and
Shorrer (2025), "To infinity and beyond: A general framework for scaling
economic theories", Theoretical Economics 20, Theorem 8, prescribes positive
utility gaps before applying compactness. Mathlib's countable-set positive-weight
construction supplies gaps whose sum over every finite subfamily is at most
one half.

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

/-- Positive rational-pair utility gaps can be fixed once and for all while
retaining the finite mass budget needed by finite-step normalization. -/
theorem exists_rationalStrongPair_margins (L : ℕ) :
    ∃ w : RationalStrongPair L → ℝ, (∀ ab, 0 < w ab) ∧
      ∀ K : Finset (RationalStrongPair L), ∑ ab ∈ K, w ab ≤ 1 / 2 := by
  obtain ⟨w, hw, hsum⟩ :=
    (Set.to_countable (Set.univ : Set (RationalStrongPair L))).exists_pos_forall_sum_le
      (by norm_num : (0 : ℝ) < 1 / 2)
  exact ⟨w, hw, fun K => hsum K (Set.subset_univ _)⟩

end MathEconLib.RevealedPreference
