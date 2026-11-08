/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLib.RevealedPreference.Afriat
public import MathEconLib.Choice.Basic
public import MathEconLib.Choice.Maximizers

/-!
# Observed consumer choices and the general choice API

An observed consumption bundle is one alternative in an observed budget set.
Rationalization means membership among all feasible utility maximizers. The bridge
uses `Choice.maximizers` and the existing `Choice.ChoiceFunction` carrier; it does
not introduce a competing choice abstraction or a tie-breaking rule.

The resulting set-valued choice retains ties. Observed-budget attainment follows
from rationalization, while no attainment claim is made for arbitrary menus.
An element of a consumer menu is itself a commodity vector; it is not an individual
contract in the separate matching interpretation of `ChoiceFunction`.

## References and provenance

Ported and adapted from Victor H. Aguiar's Apache-2.0 development
[WGARP Lean](https://github.com/vaguiarl/wgarp-lean), `ChoiceReviewBridge`.
The observation-to-maximizer interpretation follows the design discussion in
[MathEconLib issue #201](https://github.com/matheconlib/matheconlib/issues/201).
The complete finite Afriat theorem and its bibliography are in
`MathEconLib.RevealedPreference.Afriat`.
-/

@[expose] public section

set_option autoImplicit false

namespace MathEconLib.RevealedPreference

variable {L : ℕ} {T : Type*}

/-- The nonnegative consumption bundles affordable at observation `t`. -/
def budgetSet (D : Dataset L T) (t : T) : Set (Bundle L) :=
  {y | Affordable D t y}

@[simp] theorem mem_budgetSet (D : Dataset L T) (t : T) (y : Bundle L) :
    y ∈ budgetSet D t ↔ Affordable D t y := Iff.rfl

/-- All utility maximizers, packaged in the library's existing choice carrier. -/
def utilityChoice (u : Utility L) : Choice.ChoiceFunction (Bundle L) where
  toFun := Choice.maximizers (Preferences.Preference.ofUtility u)
  choose_subset := Choice.maximizers_subset _

/-- Membership retains feasibility and all ties among utility maximizers. -/
@[simp] theorem mem_utilityChoice (u : Utility L) (S : Set (Bundle L)) (x : Bundle L) :
    x ∈ utilityChoice u S ↔ x ∈ S ∧ IsMaxOn u S x :=
  Choice.mem_maximizers_ofUtility u

/-- Consumer rationalization is observed membership in existing utility maximizers. -/
theorem utilityRationalizes_iff_mem_maximizers (D : Dataset L T) (u : Utility L) :
    UtilityRationalizes D u ↔
      ∀ t, D.choice t ∈
        Choice.maximizers (Preferences.Preference.ofUtility u) (budgetSet D t) := by
  constructor
  · intro h t
    exact (Choice.mem_maximizers_ofUtility u).mpr
      ⟨affordable_choice D t, isMaxOn_iff.mpr (h t)⟩
  · intro h t y hy
    exact isMaxOn_iff.mp ((Choice.mem_maximizers_ofUtility u).mp (h t)).2 y hy

/-- The same characterization through the existing `ChoiceFunction` carrier. -/
theorem utilityRationalizes_iff_mem_utilityChoice (D : Dataset L T) (u : Utility L) :
    UtilityRationalizes D u ↔ ∀ t, D.choice t ∈ utilityChoice u (budgetSet D t) :=
  utilityRationalizes_iff_mem_maximizers D u

/-- The finite Afriat utility induces a choice correspondence containing every observation. -/
theorem garp_iff_exists_regular_utilityChoice [Finite T] [Nonempty T]
    (D : Dataset L T) :
    GARP D ↔ ∃ u : Utility L,
      Continuous u ∧ ConcaveOn ℝ Set.univ u ∧ StrictlyIncreasing u ∧
        ∀ t, D.choice t ∈ utilityChoice u (budgetSet D t) := by
  rw [garp_iff_hasRegularUtilityRationalization]
  simp only [HasRegularUtilityRationalization, utilityRationalizes_iff_mem_utilityChoice]

/-- Rationalization certifies nonempty choice on each observed budget. -/
theorem utilityChoice_budgetSet_nonempty (D : Dataset L T) (u : Utility L)
    (h : UtilityRationalizes D u) (t : T) :
    (utilityChoice u (budgetSet D t)).Nonempty :=
  ⟨D.choice t, (utilityRationalizes_iff_mem_utilityChoice D u).mp h t⟩

end MathEconLib.RevealedPreference
