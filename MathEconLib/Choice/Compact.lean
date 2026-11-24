/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLib.Choice.Maximizers
public import Mathlib.Topology.Compactness.Compact

/-!
# Attainment on compact menus

A complete preference with closed upper contours attains a greatest alternative on each
nonempty compact menu in a topological space. The conclusion uses the shared `maximizers`
correspondence. No lower-contour continuity or utility representation is required.
-/

public section

namespace MathEconLib.Choice

open Preferences Set

/-- A nonempty compact menu has a maximizer under a complete preference with closed upper
contours. -/
theorem maximizers_nonempty_of_isCompact
    {X : Type*} [TopologicalSpace X]
    (R : CompletePreference X) {S : Set X} (hS : IsCompact S) (hne : S.Nonempty)
    (hclosed : ∀ x ∈ S, IsClosed {y | R.le x y}) :
    (maximizers R.toPreference S).Nonempty := by
  have : Nonempty S := hne.to_subtype
  let U : S → Set X := fun a => {y | R.le a.val y}
  have hdir : Directed (· ⊇ ·) U := by
    intro a b
    rcases R.total a.val b.val with hab | hba
    · exact ⟨b, fun _ hz => R.le_trans hab hz, subset_rfl⟩
    · exact ⟨a, subset_rfl, fun _ hz => R.le_trans hba hz⟩
  suffices h : (S ∩ ⋂ a, U a).Nonempty by
    obtain ⟨z, hz, hall⟩ := h
    exact ⟨z, hz, fun y hy => Set.mem_iInter.mp hall ⟨y, hy⟩⟩
  by_contra hn
  rw [Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty] at hn
  obtain ⟨a, ha⟩ := hS.elim_directed_family_closed U (fun a => hclosed a a.property) hn hdir
  exact Set.disjoint_left.mp ha a.property (R.le_refl a.val)

end MathEconLib.Choice
