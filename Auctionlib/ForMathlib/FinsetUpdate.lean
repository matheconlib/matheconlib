module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Sum of `Function.update`

`Finset.sum_update` expresses `∑ j ∈ s, Function.update f i b j` in terms
of `b` and the original values `f j` for `j ≠ i`, when `i ∈ s`.
-/

@[expose] public section

open Finset

theorem Finset.sum_update {ι : Type*} {M : Type*} [AddCommMonoid M]
    [DecidableEq ι] {s : Finset ι} {f : ι → M} {i : ι} (hi : i ∈ s) (b : M) :
    ∑ j ∈ s, Function.update f i b j = b + ∑ j ∈ s.erase i, f j := by
  rw [← Finset.add_sum_erase _ _ hi, Function.update_self]
  congr 1
  exact Finset.sum_congr rfl fun j hj =>
    Function.update_of_ne (Finset.ne_of_mem_erase hj) b f

theorem Finset.sum_update_univ {ι : Type*} {M : Type*} [AddCommMonoid M]
    [DecidableEq ι] [Fintype ι] (f : ι → M) (i : ι) (b : M) :
    ∑ j, Function.update f i b j = b + ∑ j ∈ Finset.univ.erase i, f j :=
  Finset.sum_update (Finset.mem_univ i) b

end
