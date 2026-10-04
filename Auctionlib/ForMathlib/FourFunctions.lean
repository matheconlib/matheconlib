module

public import Auctionlib.ForMathlib.LatticeLikelihoodRatio
public import Mathlib

/-! # The four-functions (Ahlswede–Daykin) relation

## Main results

* `FourFunctionsLE` : for `f₁ f₂ f₃ f₄ : α → ℝ` on a lattice `α`,
  `f₁ z * f₂ w ≤ f₃ (z ⊓ w) * f₄ (z ⊔ w)` for all `z`, `w`.
* `latticeLikelihoodRatioLE_iff_fourFunctionsLE` :
  `LatticeLikelihoodRatioLE p q ↔ FourFunctionsLE q p p q`.
* `add_le_add_of_le_of_mul_le` : for reals with `0 ≤ X`, `0 ≤ Y`, `P ≤ X`, `Q ≤ X` and
  `P * Q ≤ X * Y`, `P + Q ≤ X + Y`.
* `FourFunctionsLE.perm_le_of_le` : for `FourFunctionsLE ψ₁ ψ₂ ψ₃ ψ₄` on `ℝ` with all
  four functions nonnegative and `s ≤ s'`,
  `ψ₁ s * ψ₂ s' + ψ₁ s' * ψ₂ s ≤ ψ₃ s * ψ₄ s' + ψ₃ s' * ψ₄ s`.
* `FourFunctionsLE.perm_le` : the same inequality with no ordering of `s`, `s'`.
* `integral_mul_integral_le_of_fourFunctionsLE` : for `FourFunctionsLE ψ₁ ψ₂ ψ₃ ψ₄` on `ℝ`
  with all four functions nonnegative and `μ`-integrable,
  `(∫ s, ψ₁ s ∂μ) * (∫ s, ψ₂ s ∂μ) ≤ (∫ s, ψ₃ s ∂μ) * (∫ s, ψ₄ s ∂μ)`.
-/

@[expose] public section

open MeasureTheory

/-- The four-functions (Ahlswede–Daykin) relation on `f₁ f₂ f₃ f₄ : α → ℝ` over a lattice
`α`: for all `z`, `w`, `f₁ z * f₂ w ≤ f₃ (z ⊓ w) * f₄ (z ⊔ w)`.

The slot order is that of Mathlib's `four_functions_theorem`. `Affiliated f` is the
diagonal case `FourFunctionsLE f f f f` and `LatticeLikelihoodRatioLE p q` is the case
`FourFunctionsLE q p p q`, each up to one `mul_comm`. -/
def FourFunctionsLE {α : Type*} [Lattice α] (f₁ f₂ f₃ f₄ : α → ℝ) : Prop :=
  ∀ z w : α, f₁ z * f₂ w ≤ f₃ (z ⊓ w) * f₄ (z ⊔ w)

/-- `LatticeLikelihoodRatioLE p q ↔ FourFunctionsLE q p p q`. -/
theorem latticeLikelihoodRatioLE_iff_fourFunctionsLE {α : Type*} [Lattice α] (p q : α → ℝ) :
    LatticeLikelihoodRatioLE p q ↔ FourFunctionsLE q p p q := by
  constructor
  · intro h z w
    exact (h z w).trans_eq (mul_comm _ _)
  · intro h z w
    exact (h z w).trans_eq (mul_comm _ _)

/-- For reals `X Y P Q` with `0 ≤ X`, `0 ≤ Y`, `P ≤ X`, `Q ≤ X` and `P * Q ≤ X * Y`,
`P + Q ≤ X + Y`. -/
theorem add_le_add_of_le_of_mul_le {X Y P Q : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (h1 : P ≤ X) (h2 : Q ≤ X) (h3 : P * Q ≤ X * Y) :
    P + Q ≤ X + Y := by
  rcases eq_or_lt_of_le hX with hX0 | hX0
  · linarith
  · have hkey : X * (P + Q) ≤ X * (X + Y) := by
      nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]
    exact le_of_mul_le_mul_left hkey hX0

/-- The permanent inequality for the four-functions relation on `ℝ`, in the ordered case
`s ≤ s'`: for nonnegative `ψ₁ ψ₂ ψ₃ ψ₄` with `FourFunctionsLE ψ₁ ψ₂ ψ₃ ψ₄`,
`ψ₁ s * ψ₂ s' + ψ₁ s' * ψ₂ s ≤ ψ₃ s * ψ₄ s' + ψ₃ s' * ψ₄ s`. -/
theorem FourFunctionsLE.perm_le_of_le {ψ₁ ψ₂ ψ₃ ψ₄ : ℝ → ℝ}
    (h : FourFunctionsLE ψ₁ ψ₂ ψ₃ ψ₄)
    (h₁ : 0 ≤ ψ₁) (h₂ : 0 ≤ ψ₂) (h₃ : 0 ≤ ψ₃) (h₄ : 0 ≤ ψ₄) {s s' : ℝ} (hss : s ≤ s') :
    ψ₁ s * ψ₂ s' + ψ₁ s' * ψ₂ s ≤ ψ₃ s * ψ₄ s' + ψ₃ s' * ψ₄ s := by
  have e1 := h s s'
  have e2 := h s' s
  have e3 := h s s
  have e4 := h s' s'
  rw [inf_of_le_left hss, sup_of_le_right hss] at e1
  rw [inf_of_le_right hss, sup_of_le_left hss] at e2
  rw [inf_idem, sup_idem] at e3
  rw [inf_idem, sup_idem] at e4
  have hprod : (ψ₁ s * ψ₂ s) * (ψ₁ s' * ψ₂ s') ≤ (ψ₃ s * ψ₄ s) * (ψ₃ s' * ψ₄ s') :=
    mul_le_mul e3 e4 (mul_nonneg (h₁ s') (h₂ s')) (mul_nonneg (h₃ s) (h₄ s))
  have hPQ : (ψ₁ s * ψ₂ s') * (ψ₁ s' * ψ₂ s) ≤ (ψ₃ s * ψ₄ s') * (ψ₃ s' * ψ₄ s) := by
    calc (ψ₁ s * ψ₂ s') * (ψ₁ s' * ψ₂ s)
        = (ψ₁ s * ψ₂ s) * (ψ₁ s' * ψ₂ s') := by ring
      _ ≤ (ψ₃ s * ψ₄ s) * (ψ₃ s' * ψ₄ s') := hprod
      _ = (ψ₃ s * ψ₄ s') * (ψ₃ s' * ψ₄ s) := by ring
  exact add_le_add_of_le_of_mul_le (mul_nonneg (h₃ s) (h₄ s')) (mul_nonneg (h₃ s') (h₄ s))
    e1 e2 hPQ

/-- The permanent inequality for the four-functions relation on `ℝ`, with no ordering of
`s` and `s'` required: for nonnegative `ψ₁ ψ₂ ψ₃ ψ₄` with `FourFunctionsLE ψ₁ ψ₂ ψ₃ ψ₄`,
`ψ₁ s * ψ₂ s' + ψ₁ s' * ψ₂ s ≤ ψ₃ s * ψ₄ s' + ψ₃ s' * ψ₄ s`. -/
theorem FourFunctionsLE.perm_le {ψ₁ ψ₂ ψ₃ ψ₄ : ℝ → ℝ}
    (h : FourFunctionsLE ψ₁ ψ₂ ψ₃ ψ₄)
    (h₁ : 0 ≤ ψ₁) (h₂ : 0 ≤ ψ₂) (h₃ : 0 ≤ ψ₃) (h₄ : 0 ≤ ψ₄) (s s' : ℝ) :
    ψ₁ s * ψ₂ s' + ψ₁ s' * ψ₂ s ≤ ψ₃ s * ψ₄ s' + ψ₃ s' * ψ₄ s := by
  rcases le_total s s' with hss | hss
  · exact h.perm_le_of_le h₁ h₂ h₃ h₄ hss
  · have := h.perm_le_of_le h₁ h₂ h₃ h₄ hss
    linarith

/-- The one-dimensional continuous four-functions inequality: for nonnegative
`μ`-integrable `ψ₁ ψ₂ ψ₃ ψ₄ : ℝ → ℝ` with `FourFunctionsLE ψ₁ ψ₂ ψ₃ ψ₄`,
`(∫ s, ψ₁ s ∂μ) * (∫ s, ψ₂ s ∂μ) ≤ (∫ s, ψ₃ s ∂μ) * (∫ s, ψ₄ s ∂μ)`. -/
theorem integral_mul_integral_le_of_fourFunctionsLE {μ : Measure ℝ} [SigmaFinite μ]
    {ψ₁ ψ₂ ψ₃ ψ₄ : ℝ → ℝ} (h : FourFunctionsLE ψ₁ ψ₂ ψ₃ ψ₄)
    (h₁ : 0 ≤ ψ₁) (h₂ : 0 ≤ ψ₂) (h₃ : 0 ≤ ψ₃) (h₄ : 0 ≤ ψ₄)
    (i₁ : Integrable ψ₁ μ) (i₂ : Integrable ψ₂ μ)
    (i₃ : Integrable ψ₃ μ) (i₄ : Integrable ψ₄ μ) :
    (∫ s, ψ₁ s ∂μ) * (∫ s, ψ₂ s ∂μ) ≤ (∫ s, ψ₃ s ∂μ) * (∫ s, ψ₄ s ∂μ) := by
  have j₁ : Integrable (fun z : ℝ × ℝ => ψ₁ z.1 * ψ₂ z.2) (μ.prod μ) := i₁.mul_prod i₂
  have j₂ : Integrable (fun z : ℝ × ℝ => ψ₂ z.1 * ψ₁ z.2) (μ.prod μ) := i₂.mul_prod i₁
  have j₃ : Integrable (fun z : ℝ × ℝ => ψ₃ z.1 * ψ₄ z.2) (μ.prod μ) := i₃.mul_prod i₄
  have j₄ : Integrable (fun z : ℝ × ℝ => ψ₄ z.1 * ψ₃ z.2) (μ.prod μ) := i₄.mul_prod i₃
  have e₁ : ∫ z : ℝ × ℝ, ψ₁ z.1 * ψ₂ z.2 ∂(μ.prod μ)
      = (∫ s, ψ₁ s ∂μ) * ∫ s, ψ₂ s ∂μ := integral_prod_mul ψ₁ ψ₂
  have e₂ : ∫ z : ℝ × ℝ, ψ₂ z.1 * ψ₁ z.2 ∂(μ.prod μ)
      = (∫ s, ψ₂ s ∂μ) * ∫ s, ψ₁ s ∂μ := integral_prod_mul ψ₂ ψ₁
  have e₃ : ∫ z : ℝ × ℝ, ψ₃ z.1 * ψ₄ z.2 ∂(μ.prod μ)
      = (∫ s, ψ₃ s ∂μ) * ∫ s, ψ₄ s ∂μ := integral_prod_mul ψ₃ ψ₄
  have e₄ : ∫ z : ℝ × ℝ, ψ₄ z.1 * ψ₃ z.2 ∂(μ.prod μ)
      = (∫ s, ψ₄ s ∂μ) * ∫ s, ψ₃ s ∂μ := integral_prod_mul ψ₄ ψ₃
  have hpt : ∀ z : ℝ × ℝ, ψ₁ z.1 * ψ₂ z.2 + ψ₂ z.1 * ψ₁ z.2
      ≤ ψ₃ z.1 * ψ₄ z.2 + ψ₄ z.1 * ψ₃ z.2 := by
    intro z
    have := h.perm_le h₁ h₂ h₃ h₄ z.1 z.2
    linarith
  have hmono : ∫ z : ℝ × ℝ, (ψ₁ z.1 * ψ₂ z.2 + ψ₂ z.1 * ψ₁ z.2) ∂(μ.prod μ)
      ≤ ∫ z : ℝ × ℝ, (ψ₃ z.1 * ψ₄ z.2 + ψ₄ z.1 * ψ₃ z.2) ∂(μ.prod μ) :=
    integral_mono (j₁.add j₂) (j₃.add j₄) hpt
  rw [integral_add j₁ j₂, integral_add j₃ j₄, e₁, e₂, e₃, e₄] at hmono
  linarith

end
