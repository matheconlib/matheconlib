import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Set.Card

/-!
# Cardinalities of finite fibers

A finite set is partitioned by the fibers of any map. Only the set being
counted is required to be finite; neither the domain nor the codomain needs
a finiteness instance.
-/

open scoped BigOperators

namespace Set.Finite

/-- Count a finite set by fibers over any finite set covering its image. -/
theorem ncard_eq_sum_ncard_fiber {X I : Type*} {A : Set X} (hA : A.Finite)
    (f : X → I) (T : Finset I) (hT : ∀ x ∈ A, f x ∈ T) :
    A.ncard = ∑ i ∈ T, ({x ∈ A | f x = i} : Set X).ncard := by
  classical
  rw [Set.ncard_eq_toFinset_card A hA,
    Finset.card_eq_sum_card_fiberwise (fun x hx => hT x (hA.mem_toFinset.mp hx))]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hf : ({x ∈ A | f x = i} : Set X).Finite := hA.subset (fun _ hx => hx.1)
  rw [Set.ncard_eq_toFinset_card _ hf]
  congr 1
  ext x
  constructor
  · intro hx
    obtain ⟨hxA, hxi⟩ := Finset.mem_filter.mp hx
    exact hf.mem_toFinset.mpr ⟨hA.mem_toFinset.mp hxA, hxi⟩
  · intro hx
    obtain ⟨hxA, hxi⟩ := hf.mem_toFinset.mp hx
    exact Finset.mem_filter.mpr ⟨hA.mem_toFinset.mpr hxA, hxi⟩

end Set.Finite
