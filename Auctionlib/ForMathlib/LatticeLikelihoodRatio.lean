module

public import Auctionlib.ForMathlib.StochasticOrder
public import Mathlib

/-! # The lattice likelihood-ratio order

## Main results

* `LatticeLikelihoodRatioLE`: `q z * p w ≤ q (z ⊔ w) * p (z ⊓ w)` for all `z`, `w`
  in a lattice.
* `latticeLikelihoodRatioLE_iff`: on `ℝ`, `LatticeLikelihoodRatioLE p q ↔ LikelihoodRatioLE p q`.
* `LatticeLikelihoodRatioLE.const_mul`: `LatticeLikelihoodRatioLE (c · p) (d · q)` for
  `0 ≤ c`, `0 ≤ d`.
-/

@[expose] public section

/-- The lattice likelihood-ratio order on `p q : α → ℝ` over a lattice `α`:
for all `z`, `w`, `q z * p w ≤ q (z ⊔ w) * p (z ⊓ w)`. -/
def LatticeLikelihoodRatioLE {α : Type*} [Lattice α] (p q : α → ℝ) : Prop :=
  ∀ z w : α, q z * p w ≤ q (z ⊔ w) * p (z ⊓ w)

/-- On the linear order `ℝ` the lattice likelihood-ratio order coincides with the
likelihood-ratio order: `LatticeLikelihoodRatioLE p q ↔ LikelihoodRatioLE p q`. -/
theorem latticeLikelihoodRatioLE_iff (p q : ℝ → ℝ) :
    LatticeLikelihoodRatioLE p q ↔ LikelihoodRatioLE p q := by
  constructor
  · intro h x y hxy
    have hxy' := h x y
    rwa [sup_of_le_right hxy, inf_of_le_left hxy] at hxy'
  · intro h z w
    rcases le_total z w with hzw | hzw
    · rw [sup_of_le_right hzw, inf_of_le_left hzw]
      exact h hzw
    · rw [sup_of_le_left hzw, inf_of_le_right hzw]

/-- The lattice likelihood-ratio order is preserved by nonnegative constant rescaling:
`LatticeLikelihoodRatioLE p q` implies `LatticeLikelihoodRatioLE (fun x => c * p x)
(fun x => d * q x)` for `0 ≤ c` and `0 ≤ d`. -/
theorem LatticeLikelihoodRatioLE.const_mul {α : Type*} [Lattice α] {p q : α → ℝ}
    (hlr : LatticeLikelihoodRatioLE p q) {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) :
    LatticeLikelihoodRatioLE (fun x => c * p x) (fun x => d * q x) := by
  intro z w
  dsimp only
  calc d * q z * (c * p w) = d * c * (q z * p w) := by ring
    _ ≤ d * c * (q (z ⊔ w) * p (z ⊓ w)) :=
        mul_le_mul_of_nonneg_left (hlr z w) (mul_nonneg hd hc)
    _ = d * q (z ⊔ w) * (c * p (z ⊓ w)) := by ring

end
