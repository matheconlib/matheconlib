/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLib.Choice.Maximizers
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Attainment on compact menus

A complete preference with closed upper contours attains a greatest alternative on each
nonempty compact menu in a Hausdorff space. The conclusion uses the shared `maximizers`
correspondence. No lower-contour continuity or utility representation is required.
-/

public section

namespace MathEconLib.Choice

open Preferences Set

/-- A nonempty compact menu has a maximizer under a complete preference with closed upper
contours. -/
theorem maximizers_nonempty_of_isCompact
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (R : CompletePreference X) {S : Set X} (hS : IsCompact S) (hne : S.Nonempty)
    (hclosed : ∀ x ∈ S, IsClosed {y | R.le x y}) :
    (maximizers R.toPreference S).Nonempty := by
  let : Nonempty S := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  let C : S → Set X := fun a => S ∩ {x | R.le a.val x}
  have hdir : Directed (· ⊇ ·) C := by
    intro a b
    rcases R.total a.val b.val with hab | hba
    · exact ⟨b, fun z hz => ⟨hz.1, R.le_trans hab hz.2⟩, subset_rfl⟩
    · exact ⟨a, subset_rfl, fun z hz => ⟨hz.1, R.le_trans hba hz.2⟩⟩
  have hnonempty (a : S) : (C a).Nonempty := ⟨a.val, a.property, R.le_refl a.val⟩
  have hcompact (a : S) : IsCompact (C a) := hS.inter_right (hclosed a.val a.property)
  have hclose (a : S) : IsClosed (C a) := hS.isClosed.inter (hclosed a.val a.property)
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    C hdir hnonempty hcompact hclose
  have hxall : ∀ a : S, x ∈ C a := Set.mem_iInter.mp hx
  refine ⟨x, (hxall ⟨hne.choose, hne.choose_spec⟩).1, ?_⟩
  intro y hy
  exact (hxall ⟨y, hy⟩).2

end MathEconLib.Choice
