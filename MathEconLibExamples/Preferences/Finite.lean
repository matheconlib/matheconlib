/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Preferences

/-!
# Finite ordinal representation with ties

Four alternatives have scores 0, 1, 1, and 2. The finite representation theorem preserves the
indifference of alternatives 1 and 2 and makes both utility-maximizing on their two-item menu.
The all-menu result keeps feasibility explicit. Lower-contour scores 1, 3, 3, and 4 independently
check the construction used in the existence proof. These scores have only ordinal meaning.
-/

@[expose] public section

namespace MathEconLib.Preferences.Examples.Finite

open MathEconLib.Preferences
open scoped MathEconLib.Preferences

def score (x : Fin 4) : ℕ := if x = 0 then 0 else if x = 3 then 2 else 1

def tied : CompletePreference (Fin 4) := CompletePreference.ofUtility score

theorem explicit_representation : tied.IsRepresentedBy score :=
  Preference.isRepresentedBy_ofUtility score

-- Independent finite calculation of the contour scores used by the existence proof.
def lowerCount (x : Fin 4) : ℕ :=
  (Finset.univ.filter fun z : Fin 4 => score z ≤ score x).card

theorem exact_contour_scores :
    lowerCount 0 = 1 ∧ lowerCount 1 = 3 ∧ lowerCount 2 = 3 ∧ lowerCount 3 = 4 := by
  decide

theorem lower_count_representation : tied.IsRepresentedBy lowerCount := by
  change ∀ x y, score x ≤ score y ↔ lowerCount x ≤ lowerCount y
  decide

theorem tied_menu :
    (∀ x ∈ ({1, 2} : Set (Fin 4)), x ≼[tied] 1) ∧
    (∀ x ∈ ({1, 2} : Set (Fin 4)), x ≼[tied] 2) := by
  constructor <;> intro x hx <;>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx <;>
    rcases hx with rfl | rfl <;> change score _ ≤ score _ <;> decide

theorem finite_application :
    ∃ v : Fin 4 → ℕ, tied.IsRepresentedBy v ∧
      v 1 = v 2 ∧ v 0 < v 1 ∧
      IsMaxOn v ({1, 2} : Set (Fin 4)) 1 ∧ IsMaxOn v ({1, 2} : Set (Fin 4)) 2 := by
  obtain ⟨v, hv⟩ := tied.exists_isRepresentedBy_nat
  refine ⟨v, hv, ?_, ?_, hv.forall_le_iff_isMaxOn.mp tied_menu.1,
    hv.forall_le_iff_isMaxOn.mp tied_menu.2⟩
  · exact le_antisymm ((hv 1 2).mp (by change score 1 ≤ score 2; decide))
      ((hv 2 1).mp (by change score 2 ≤ score 1; decide))
  · exact lt_of_le_not_ge ((hv 0 1).mp (by change score 0 ≤ score 1; decide)) (fun h => (by
      change ¬score 1 ≤ score 0
      decide : ¬(1 : Fin 4) ≼[tied] 0) ((hv 1 0).mpr h))

theorem all_menu_application :
    ∃ v : Fin 4 → ℕ, ∀ (S : Set (Fin 4)) a,
      (a ∈ S ∧ ∀ x ∈ S, x ≼[tied] a) ↔ (a ∈ S ∧ IsMaxOn v S a) := by
  obtain ⟨v, hv⟩ := tied.exists_nat_utility_isMaxOn
  exact ⟨v, fun S a => and_congr_right (fun _ => hv S a)⟩

end MathEconLib.Preferences.Examples.Finite
