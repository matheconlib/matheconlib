module

public import Mathlib.Order.Lattice
public import Mathlib.Order.Monotone.Defs

/-! # `Function.update` and the pointwise order on `∀ i, π i`

## Main results

* `Function.update_sup_update` :
  `Function.update u j s ⊔ Function.update v j t = Function.update (u ⊔ v) j (s ⊔ t)`.
* `Function.update_inf_update` :
  `Function.update u j s ⊓ Function.update v j t = Function.update (u ⊓ v) j (s ⊓ t)`.
* `Function.update_update_mono` :
  `Monotone fun s => Function.update (Function.update u i s) j y`.
-/

@[expose] public section

namespace Function

variable {ι : Type*} {π : ι → Type*} [DecidableEq ι]

/-- `z[i ↦ x]` is the function `z` updated at `i` to the value `x`, that is,
`Function.update z i x`. Updates chain: `z[i ↦ x][j ↦ y]` is
`Function.update (Function.update z i x) j y`. -/
scoped notation:max z "[" i " ↦ " x "]" => Function.update z i x

/-- `Function.update u j s ⊔ Function.update v j t = Function.update (u ⊔ v) j (s ⊔ t)`. -/
theorem update_sup_update [∀ i, SemilatticeSup (π i)] (u v : ∀ i, π i) (j : ι) (s t : π j) :
    u[j ↦ s] ⊔ v[j ↦ t] = (u ⊔ v)[j ↦ s ⊔ t] := by
  funext i
  obtain rfl | hij := eq_or_ne i j
  · simp only [Pi.sup_apply, Function.update_self]
  · simp only [Pi.sup_apply, Function.update_of_ne hij]

/-- `Function.update u j s ⊓ Function.update v j t = Function.update (u ⊓ v) j (s ⊓ t)`. -/
theorem update_inf_update [∀ i, SemilatticeInf (π i)] (u v : ∀ i, π i) (j : ι) (s t : π j) :
    u[j ↦ s] ⊓ v[j ↦ t] = (u ⊓ v)[j ↦ s ⊓ t] := by
  funext i
  obtain rfl | hij := eq_or_ne i j
  · simp only [Pi.inf_apply, Function.update_self]
  · simp only [Pi.inf_apply, Function.update_of_ne hij]

/-- `Monotone fun s => Function.update (Function.update u i s) j y`. -/
theorem update_update_mono [∀ i, Preorder (π i)] (u : ∀ k, π k) (i j : ι) (y : π j) :
    Monotone fun s : π i => u[i ↦ s][j ↦ y] :=
  fun _ _ hs => update_le_update_iff.2 ⟨le_rfl, fun k _ => update_mono hs k⟩

end Function

end
