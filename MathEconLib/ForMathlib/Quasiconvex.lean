/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.Convex.Quasiconvex

/-!
# Quasiconcavity of extensions from a subset

Quasiconcavity on a subset depends only on the values of a function on that subset. In particular,
extending a function from a subtype preserves the same quasiconcavity condition regardless of the
values assigned outside its domain.

## Main statements

* `quasiconcaveOn_subtype_val_extend_iff`: Quasiconcavity of a subtype extension is independent of
  its default.

## Tags

quasiconcavity, function extension
-/

@[expose] public section

/-- Quasiconcavity on a subset does not depend on the values assigned outside it when extending a
function from the corresponding subtype. -/
lemma quasiconcaveOn_subtype_val_extend_iff {𝕜 E V : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
    [AddCommMonoid E] [SMul 𝕜 E] [LE V] {s : Set E} (f : s → V) (g₁ g₂ : E → V) :
    QuasiconcaveOn 𝕜 s (Subtype.val.extend f g₁) ↔
      QuasiconcaveOn 𝕜 s (Subtype.val.extend f g₂) := by
  unfold QuasiconcaveOn
  apply forall_congr'
  intro r
  have hsuperlevels : {x ∈ s | r ≤ Subtype.val.extend f g₁ x} =
      {x ∈ s | r ≤ Subtype.val.extend f g₂ x} := by
    ext x
    by_cases hx : x ∈ s
    · have h_extend₁ := Subtype.val_injective.extend_apply f g₁ ⟨x, hx⟩
      have h_extend₂ := Subtype.val_injective.extend_apply f g₂ ⟨x, hx⟩
      simp only [Set.mem_setOf_eq, h_extend₁, h_extend₂]
    · simp only [Set.mem_setOf_eq, hx, false_and]
  rw [hsuperlevels]
