/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/

module

public import MathEconLib.Preferences.Representation.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.EquivFin

/-!
# Natural-Number Representations of Finite Complete Preferences

This file shows that every complete preference on a finite type of alternatives has an ordinal
utility representation valued in `ℕ`. The utility counts the lower contour set,
`u x = #{z | z ≼[R] x}`, so better alternatives receive larger scores and indifferent alternatives
receive equal scores. Differences between these scores carry no economic meaning.

## Main Statements

* `CompletePreference.exists_isRepresentedBy_nat` — every complete preference on a finite type is
  represented by a natural-number utility.
* `CompletePreference.exists_nat_utility_isMaxOn` — a single natural-number utility identifies, on
  every menu, the alternatives at least as good as all others with the utility maximizers.

## Tags

preference, complete preference, ordinal utility, finite alternatives, maximization
-/

@[expose] public section

namespace MathEconLib

namespace Preferences.CompletePreference

variable {X : Type*}

/-- Every complete preference on a finite type is represented by a natural-number utility. -/
theorem exists_isRepresentedBy_nat [Finite X] (R : CompletePreference X) :
    ∃ u : X → ℕ, R.IsRepresentedBy u := by
  classical
  let : Fintype X := Fintype.ofFinite X
  let u : X → ℕ := fun x => (Finset.univ.filter fun z => z ≼[R] x).card
  refine ⟨u, fun x y => ?_⟩
  constructor
  · intro hxy
    apply Finset.card_le_card
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact R.le_trans hz hxy
  · intro huxy
    by_contra hnxy
    have hyx : y ≼[R] x := (R.total x y).resolve_left hnxy
    have hsub : Finset.univ.filter (fun z => z ≼[R] y) ⊆
        Finset.univ.filter (fun z => z ≼[R] x) := by
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact R.le_trans hz hyx
    have hx_in : x ∈ Finset.univ.filter (fun z => z ≼[R] x) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact R.le_refl x
    have hx_not : x ∉ Finset.univ.filter (fun z => z ≼[R] y) := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hnxy
    have hss : Finset.univ.filter (fun z => z ≼[R] y) ⊂
        Finset.univ.filter (fun z => z ≼[R] x) :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => hx_not (h.symm ▸ hx_in)⟩
    exact (not_lt_of_ge huxy) (Finset.card_lt_card hss)

/-- One natural-number utility identifies greatest alternatives with maximizers on every menu. -/
theorem exists_nat_utility_isMaxOn [Finite X] (R : CompletePreference X) :
    ∃ u : X → ℕ, ∀ (S : Set X) (a : X),
      (∀ x ∈ S, x ≼[R] a) ↔ IsMaxOn u S a := by
  obtain ⟨u, hu⟩ := R.exists_isRepresentedBy_nat
  exact ⟨u, fun _ _ => hu.forall_le_iff_isMaxOn⟩

end Preferences.CompletePreference

end MathEconLib

end
