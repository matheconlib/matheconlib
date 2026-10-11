import MathEconLib.Choice.Conditions.General.FiniteValued
import MathEconLib.Choice.Conditions.General.IrrelevanceOfRejectedAlternatives
import MathEconLib.Choice.Conditions.General.LawOfAggregateDemand
import MathEconLib.Choice.Conditions.General.PathIndependence
import MathEconLib.Choice.Conditions.General.Substitutability
import MathEconLib.Choice.Conditions.General.UnitDemand

/-!
# Relationships between general choice conditions

This module combines conditions whose definitions and elementary properties
are in the neighboring topic modules:

* Substitutability and the law of aggregate demand imply IRC on finite menus,
  and hence consistency on a finite alternative type.
* Consistent unit-demand choice functions are substitutable and satisfy
  the law of aggregate demand, without requiring a finite alternative type.
* Path independence is equivalent to substitutability and consistency,
  without any finiteness assumption.

All results concern general choice functions. No matching market or partner
map is required. Relationships involving weak substitutability and completion
are in `MathEconLib.Choice.Conditions.Matching.Relationships`.

## References

Aizerman–Malishevski (1981); Chambers–Yenmez (2017); Plott (1973).
See the neighboring topic modules and
`MathEconLib.Choice.Conditions.General` for the matching-with-contracts
references and their finite-domain conventions.
-/

namespace MathEconLib.Choice

universe u

variable {α : Type u}

namespace ChoiceFunction

variable (C : ChoiceFunction α)

variable {C}

/-- Substitutability and the law of aggregate demand imply IRC whenever the
original menu is finite. Substitutability gives `C Y ⊆ C Z`, while the law of
aggregate demand gives the reverse cardinality inequality. -/
theorem Substitutable.consistent_on_finite_menu
    (hsub : C.Substitutable) (hload : C.SizeMonotone)
    {Y Z : Set α} (hY : Y.Finite) (hCY : C Y ⊆ Z) (hZY : Z ⊆ Y) :
    C Z = C Y := by
  have hchoice : C Y ⊆ C Z := fun _ hx =>
    (substitutable_iff_chernoff.mp hsub) hZY ⟨hx, hCY hx⟩
  have hcard : (C Z).ncard ≤ (C Y).ncard := hload hY hZY
  have hfin : (C Z).Finite :=
    hY.subset (fun _ hx => hZY (C.choose_subset Z hx))
  exact (Set.eq_of_subset_of_ncard_le hchoice hcard hfin).symm

/-- On a finite universe, substitutability and the law of aggregate demand
already imply consistency (IRC). -/
theorem Substitutable.consistent_of_sizeMonotone [Finite α]
    (hsub : C.Substitutable) (hload : C.SizeMonotone) :
    C.Consistent :=
  fun {_Y _Z} hCY hZY =>
    hsub.consistent_on_finite_menu hload (Set.toFinite _) hCY hZY

/-- Consistent unit-demand choice functions are substitutable. -/
theorem UnitDemand.substitutable
    (hunit : C.UnitDemand) (hcons : C.Consistent) :
    C.Substitutable := by
  intro x Y Z hYZ hx hxZ
  have hsubset : C (insert x Z) ⊆ insert x Y := by
    intro y hy
    have hyx : y = x := hunit _ hy hxZ
    simp [hyx]
  have hEq : C (insert x Y) = C (insert x Z) :=
    hcons hsubset (Set.insert_subset_insert hYZ)
  rw [hEq] at hx
  exact hx hxZ

/-- Consistent unit-demand choice functions satisfy the law of aggregate
demand. -/
theorem UnitDemand.sizeMonotone
    (hunit : C.UnitDemand) (hcons : C.Consistent) :
    C.SizeMonotone := by
  intro Y Z _hZfin hYZ
  rcases Set.eq_empty_or_nonempty (C Y) with hY | ⟨x, hx⟩
  · simp [hY]
  · have hZ : (C Z).Nonempty := by
      rcases Set.eq_empty_or_nonempty (C Z) with hZ | hZ
      · exfalso
        have h0 : C Z ⊆ Y := by
          rw [hZ]
          exact Set.empty_subset _
        have hEq := hcons h0 hYZ
        rw [hEq, hZ] at hx
        exact hx
      · exact hZ
    obtain ⟨z, hz⟩ := hZ
    rw [(hunit Y).eq_singleton_of_mem hx,
      (hunit Z).eq_singleton_of_mem hz]
    simp

/-- Substitutability + consistency imply path independence. Finiteness-free. -/
theorem Substitutable.pathIndependent
    (hsub : C.Substitutable) (hcons : C.Consistent) :
    C.PathIndependent := by
  intro Y Z
  have hch : C.Chernoff :=
    substitutable_iff_chernoff.mp hsub
  apply
    (hcons ?_
      (Set.union_subset_union_left _ (C.choose_subset Y))).symm
  intro x hx
  rcases C.choose_subset _ hx with hxY | hxZ
  · exact Set.mem_union_left _
      (hch Set.subset_union_left ⟨hx, hxY⟩)
  · exact Set.mem_union_right _ hxZ

/-- Path independence implies consistency — even without finiteness. -/
theorem PathIndependent.consistent
    (hpi : C.PathIndependent) :
    C.Consistent := by
  intro Y Z hCY hZY
  have e1 : C Y ∪ Z = Z :=
    Set.union_eq_self_of_subset_left hCY
  have e2 : Y ∪ Z = Y :=
    Set.union_eq_self_of_subset_right hZY
  calc
    C Z = C (C Y ∪ Z) := by rw [e1]
    _ = C (Y ∪ Z) := (hpi Y Z).symm
    _ = C Y := by rw [e2]

/-- Path independence implies substitutability — even without finiteness — via the
Chernoff condition. -/
theorem PathIndependent.substitutable
    (hpi : C.PathIndependent) :
    C.Substitutable := by
  rw [substitutable_iff_chernoff]
  intro W V hWV x hx
  obtain ⟨hxV, hxW⟩ := hx
  have hx :
      x ∈ C (C W ∪ (V \ W)) := by
    rw [← hpi W (V \ W), Set.union_diff_cancel hWV]
    exact hxV
  rcases C.choose_subset _ hx with hxCW | hxDiff
  · exact hxCW
  · exact (hxDiff.2 hxW).elim

/-- Aizerman–Malishevski / Chambers–Yenmez, finiteness-free in set form. -/
theorem pathIndependent_iff_substitutable_and_consistent :
    C.PathIndependent ↔ C.Substitutable ∧ C.Consistent :=
  ⟨fun hpi => ⟨hpi.substitutable, hpi.consistent⟩,
   fun h => h.1.pathIndependent h.2⟩

end ChoiceFunction

end MathEconLib.Choice
