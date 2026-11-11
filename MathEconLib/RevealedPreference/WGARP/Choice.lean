/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLib.RevealedPreference.WGARP.Characterization
public import MathEconLib.RevealedPreference.Choice

/-!
# Choice from numerical preferences

A numerical preference selects every available bundle whose comparison with every
available alternative is nonnegative. This gives an existing `Choice.ChoiceFunction`
without requiring transitivity. Rationalization is exactly observed membership on
the existing `budgetSet`; ties are retained and observed budgets have nonempty choice.

## References and provenance

The observation interface is adapted from Victor H. Aguiar's Apache-2.0
[WGARP Lean](https://github.com/vaguiarl/wgarp-lean), `ChoiceReviewBridge`.
The finite existence theorem uses the WGARP characterization and attribution in
`MathEconLib.RevealedPreference.WGARP.Characterization`.
-/

@[expose] public section

set_option autoImplicit false

namespace MathEconLib.RevealedPreference

variable {L : ℕ} {T : Type*}

/-- All available bundles weakly preferred to every available alternative. -/
def preferenceChoice (r : PreferenceFunction L) : Choice.ChoiceFunction (Bundle L) where
  toFun S := {x | x ∈ S ∧ ∀ y ∈ S, 0 ≤ r x y}
  choose_subset _ _ hx := hx.1

/-- Choice retains feasibility and every weak comparison, including ties. -/
@[simp] theorem mem_preferenceChoice (r : PreferenceFunction L)
    (S : Set (Bundle L)) (x : Bundle L) :
    x ∈ preferenceChoice r S ↔ x ∈ S ∧ ∀ y ∈ S, 0 ≤ r x y := Iff.rfl

/-- Utility differences recover the existing utility-maximizing choice rule. -/
@[simp] theorem preferenceChoice_sub (u : Utility L) :
    preferenceChoice (fun x y ↦ u x - u y) = utilityChoice u := by
  apply Choice.ChoiceFunction.ext
  intro S
  ext x
  simp only [mem_preferenceChoice, mem_utilityChoice, sub_nonneg, isMaxOn_iff]

/-- Rationalization by utility differences is ordinary utility rationalization. -/
@[simp] theorem preferenceRationalizes_sub_iff (D : Dataset L T) (u : Utility L) :
    PreferenceRationalizes D (fun x y ↦ u x - u y) ↔ UtilityRationalizes D u := by
  simp only [PreferenceRationalizes, UtilityRationalizes, sub_nonneg]

/-- Strict increase of utility differences in the first bundle is strict increase of utility. -/
@[simp] theorem strictlyIncreasingFirst_sub_iff (u : Utility L) :
    StrictlyIncreasingFirst (fun x y ↦ u x - u y) ↔ StrictlyIncreasing u := by
  rw [strictlyIncreasing_iff_strictMono]
  constructor
  · intro h z x hzx
    simpa only [sub_lt_sub_iff_right] using h z (strictDominates_iff_lt.mpr hzx)
  · intro h x z y hxz
    exact sub_lt_sub_right (h (strictDominates_iff_lt.mp hxz)) (u y)

/-- Numerical preference rationalization is observed membership in the choice rule. -/
theorem preferenceRationalizes_iff_mem_preferenceChoice
    (D : Dataset L T) (r : PreferenceFunction L) :
    PreferenceRationalizes D r ↔ ∀ t, D.choice t ∈ preferenceChoice r (budgetSet D t) := by
  constructor
  · intro h t
    exact ⟨affordable_choice D t, h t⟩
  · intro h t y hy
    exact (h t).2 y hy

/-- Finite WGARP observations belong to a regular numerical preference's choices. -/
theorem wgarp_iff_exists_regular_preferenceChoice [Finite T]
    (D : Dataset L T) :
    WGARP D ↔ ∃ r : PreferenceFunction L,
      ContinuousPreference r ∧ StrictlyIncreasingFirst r ∧ SignAsymmetric r ∧
        ∀ t, D.choice t ∈ preferenceChoice r (budgetSet D t) := by
  rw [wgarp_iff_hasRegularPreferenceRationalization]
  simp only [HasRegularPreferenceRationalization,
    preferenceRationalizes_iff_mem_preferenceChoice]

/-- Rationalization guarantees nonempty choice on every observed budget. -/
theorem preferenceChoice_budgetSet_nonempty (D : Dataset L T) (r : PreferenceFunction L)
    (h : PreferenceRationalizes D r) (t : T) :
    (preferenceChoice r (budgetSet D t)).Nonempty :=
  ⟨D.choice t, (preferenceRationalizes_iff_mem_preferenceChoice D r).mp h t⟩

end MathEconLib.RevealedPreference
