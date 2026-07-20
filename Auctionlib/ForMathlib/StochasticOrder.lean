module

public import Mathlib

/-! # Stochastic orders: the likelihood-ratio order and MLR ⇒ FOSD

## Main results

* `LikelihoodRatioLE`: `p ≤lr q` iff `q x * p y ≤ q y * p x` for all `x ≤ y`;
  where `p` is positive this says `q / p` is nondecreasing.
* `LikelihoodRatioLE.sub_mul_sub_nonneg`:
  `0 ≤ (g x - g y) * (q x * p y - p x * q y)` for monotone `g`.
* `integral_mul_integral_le_of_likelihoodRatioLE`:
  `(∫ g·p) * (∫ q) ≤ (∫ g·q) * (∫ p)` for monotone `g`.
* `integral_mul_le_of_likelihoodRatioLE`: for densities of total mass one,
  `∫ g·p ≤ ∫ g·q` for monotone `g`.
* `setIntegral_Ioi_mul_integral_le_of_likelihoodRatioLE`:
  `(∫ x in Ioi t, p) * (∫ q) ≤ (∫ x in Ioi t, q) * (∫ p)`.
-/

@[expose] public section

open MeasureTheory

/-- The likelihood-ratio order `p ≤lr q` on densities `p q : ℝ → ℝ`:
for all `x ≤ y`, `q x * p y ≤ q y * p x`. Where `p` is positive this says
`q / p` is nondecreasing. -/
def LikelihoodRatioLE (p q : ℝ → ℝ) : Prop :=
  ∀ ⦃x y : ℝ⦄, x ≤ y → q x * p y ≤ q y * p x

/-- The likelihood-ratio order is reflexive. -/
theorem LikelihoodRatioLE.refl (p : ℝ → ℝ) : LikelihoodRatioLE p p :=
  fun x y _ => (mul_comm (p x) (p y)).le

/-- The likelihood-ratio order is preserved by nonnegative constant rescaling. -/
theorem LikelihoodRatioLE.const_mul {p q : ℝ → ℝ} (hlr : LikelihoodRatioLE p q)
    {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) :
    LikelihoodRatioLE (fun x => c * p x) (fun x => d * q x) := by
  intro x y hxy
  dsimp only
  calc d * q x * (c * p y) = d * c * (q x * p y) := by ring
    _ ≤ d * c * (q y * p x) :=
        mul_le_mul_of_nonneg_left (hlr hxy) (mul_nonneg hd hc)
    _ = d * q y * (c * p x) := by ring

/-- `p ≤lr r · p` for nonnegative `p` and nondecreasing `r`. -/
theorem LikelihoodRatioLE.of_monotone_mul {p r : ℝ → ℝ} (hp0 : 0 ≤ p)
    (hr : Monotone r) : LikelihoodRatioLE p (fun x => r x * p x) := by
  intro x y hxy
  dsimp only
  calc r x * p x * p y = r x * (p x * p y) := by ring
    _ ≤ r y * (p x * p y) :=
        mul_le_mul_of_nonneg_right (hr hxy) (mul_nonneg (hp0 x) (hp0 y))
    _ = r y * p y * p x := by ring

set_option linter.unusedVariables false in
/-- For `p ≤lr q` and monotone `g`,
`0 ≤ (g x - g y) * (q x * p y - p x * q y)`: both factors share the sign of
`x - y`. -/
@[nolint unusedArguments]
theorem LikelihoodRatioLE.sub_mul_sub_nonneg {p q g : ℝ → ℝ}
    (hlr : LikelihoodRatioLE p q) (hp0 : 0 ≤ p) (hq0 : 0 ≤ q)
    (hg : Monotone g) (x y : ℝ) :
    0 ≤ (g x - g y) * (q x * p y - p x * q y) := by
  rcases le_total x y with hxy | hxy
  · -- both factors are ≤ 0
    have h1 : g x ≤ g y := hg hxy
    have h2 : q x * p y ≤ p x * q y := (hlr hxy).trans_eq (mul_comm _ _)
    calc (0 : ℝ) ≤ (g y - g x) * (p x * q y - q x * p y) :=
          mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)
      _ = (g x - g y) * (q x * p y - p x * q y) := by ring
  · -- both factors are ≥ 0
    have h1 : g y ≤ g x := hg hxy
    have h2 : p x * q y ≤ q x * p y := (mul_comm (p x) (q y)).trans_le (hlr hxy)
    exact mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)

/-- MLR ⇒ FOSD, cross-multiplied form: if `p ≤lr q` are nonnegative densities
and `g` is monotone, then `(∫ g·p) * (∫ q) ≤ (∫ g·q) * (∫ p)`. -/
theorem integral_mul_integral_le_of_likelihoodRatioLE {μ : Measure ℝ}
    [SigmaFinite μ] {p q g : ℝ → ℝ} (hp0 : 0 ≤ p) (hq0 : 0 ≤ q)
    (hlr : LikelihoodRatioLE p q) (hg : Monotone g)
    (hpi : Integrable p μ) (hqi : Integrable q μ)
    (hgpi : Integrable (fun x => g x * p x) μ)
    (hgqi : Integrable (fun x => g x * q x) μ) :
    (∫ x, g x * p x ∂μ) * (∫ x, q x ∂μ) ≤
      (∫ x, g x * q x ∂μ) * (∫ x, p x ∂μ) := by
  have h1 : Integrable (fun z : ℝ × ℝ => g z.1 * q z.1 * p z.2) (μ.prod μ) :=
    hgqi.mul_prod hpi
  have h2 : Integrable (fun z : ℝ × ℝ => g z.1 * p z.1 * q z.2) (μ.prod μ) :=
    hgpi.mul_prod hqi
  have h3 : Integrable (fun z : ℝ × ℝ => q z.1 * (g z.2 * p z.2)) (μ.prod μ) :=
    hqi.mul_prod hgpi
  have h4 : Integrable (fun z : ℝ × ℝ => p z.1 * (g z.2 * q z.2)) (μ.prod μ) :=
    hpi.mul_prod hgqi
  have e1 : ∫ z : ℝ × ℝ, g z.1 * q z.1 * p z.2 ∂(μ.prod μ)
      = (∫ x, g x * q x ∂μ) * ∫ x, p x ∂μ :=
    integral_prod_mul (fun x => g x * q x) p
  have e2 : ∫ z : ℝ × ℝ, g z.1 * p z.1 * q z.2 ∂(μ.prod μ)
      = (∫ x, g x * p x ∂μ) * ∫ x, q x ∂μ :=
    integral_prod_mul (fun x => g x * p x) q
  have e3 : ∫ z : ℝ × ℝ, q z.1 * (g z.2 * p z.2) ∂(μ.prod μ)
      = (∫ x, q x ∂μ) * ∫ x, g x * p x ∂μ :=
    integral_prod_mul q (fun x => g x * p x)
  have e4 : ∫ z : ℝ × ℝ, p z.1 * (g z.2 * q z.2) ∂(μ.prod μ)
      = (∫ x, p x ∂μ) * ∫ x, g x * q x ∂μ :=
    integral_prod_mul p (fun x => g x * q x)
  have key : ∫ z : ℝ × ℝ, (g z.1 - g z.2) * (q z.1 * p z.2 - p z.1 * q z.2)
        ∂(μ.prod μ)
      = 2 * ((∫ x, g x * q x ∂μ) * ∫ x, p x ∂μ)
        - 2 * ((∫ x, g x * p x ∂μ) * ∫ x, q x ∂μ) := by
    have hfe : (fun z : ℝ × ℝ => (g z.1 - g z.2) * (q z.1 * p z.2 - p z.1 * q z.2))
        = fun z : ℝ × ℝ =>
            (g z.1 * q z.1 * p z.2 + p z.1 * (g z.2 * q z.2))
              - (g z.1 * p z.1 * q z.2 + q z.1 * (g z.2 * p z.2)) := by
      funext z; ring
    have hsum : Integrable
        (fun z : ℝ × ℝ => g z.1 * q z.1 * p z.2 + p z.1 * (g z.2 * q z.2))
        (μ.prod μ) := h1.add h4
    have hsum' : Integrable
        (fun z : ℝ × ℝ => g z.1 * p z.1 * q z.2 + q z.1 * (g z.2 * p z.2))
        (μ.prod μ) := h2.add h3
    rw [hfe, integral_sub hsum hsum', integral_add h1 h4,
      integral_add h2 h3, e1, e2, e3, e4]
    ring
  have hnn : 0 ≤ ∫ z : ℝ × ℝ, (g z.1 - g z.2) * (q z.1 * p z.2 - p z.1 * q z.2)
      ∂(μ.prod μ) :=
    integral_nonneg fun z => hlr.sub_mul_sub_nonneg hp0 hq0 hg z.1 z.2
  rw [key] at hnn
  linarith

/-- Monotone expectations: if `p ≤lr q` are nonnegative densities of total
mass one, then `∫ g·p ≤ ∫ g·q` for every monotone `g`. -/
theorem integral_mul_le_of_likelihoodRatioLE {μ : Measure ℝ} [SigmaFinite μ]
    {p q g : ℝ → ℝ} (hp0 : 0 ≤ p) (hq0 : 0 ≤ q)
    (hlr : LikelihoodRatioLE p q) (hg : Monotone g)
    (hpi : Integrable p μ) (hqi : Integrable q μ)
    (hgpi : Integrable (fun x => g x * p x) μ)
    (hgqi : Integrable (fun x => g x * q x) μ)
    (hp1 : ∫ x, p x ∂μ = 1) (hq1 : ∫ x, q x ∂μ = 1) :
    ∫ x, g x * p x ∂μ ≤ ∫ x, g x * q x ∂μ := by
  have h := integral_mul_integral_le_of_likelihoodRatioLE hp0 hq0 hlr hg
    hpi hqi hgpi hgqi
  rwa [hp1, hq1, mul_one, mul_one] at h

/-- The indicator of `Ioi t` is monotone. -/
theorem monotone_indicator_Ioi_one (t : ℝ) :
    Monotone ((Set.Ioi t).indicator (1 : ℝ → ℝ)) := by
  intro a b hab
  by_cases ha : a ∈ Set.Ioi t
  · rw [Set.indicator_of_mem ha, Set.indicator_of_mem (isUpperSet_Ioi t hab ha)]
    simp only [Pi.one_apply, le_refl]
  · rw [Set.indicator_of_notMem ha]
    exact Set.indicator_apply_nonneg fun _ => zero_le_one

/-- Upper tails compare under the likelihood-ratio order: if `p ≤lr q` are
nonnegative integrable densities, then for every `t`,
`(∫ x in Ioi t, p) * (∫ q) ≤ (∫ x in Ioi t, q) * (∫ p)`. -/
theorem setIntegral_Ioi_mul_integral_le_of_likelihoodRatioLE {μ : Measure ℝ}
    [SigmaFinite μ] {p q : ℝ → ℝ} (hp0 : 0 ≤ p) (hq0 : 0 ≤ q)
    (hlr : LikelihoodRatioLE p q)
    (hpi : Integrable p μ) (hqi : Integrable q μ) (t : ℝ) :
    (∫ x in Set.Ioi t, p x ∂μ) * (∫ x, q x ∂μ) ≤
      (∫ x in Set.Ioi t, q x ∂μ) * (∫ x, p x ∂μ) := by
  have hind : ∀ h : ℝ → ℝ,
      (fun x => (Set.Ioi t).indicator (1 : ℝ → ℝ) x * h x)
        = (Set.Ioi t).indicator h := by
    intro h
    funext x
    by_cases hx : x ∈ Set.Ioi t
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hgpi : Integrable (fun x => (Set.Ioi t).indicator (1 : ℝ → ℝ) x * p x) μ := by
    rw [hind p]; exact hpi.indicator measurableSet_Ioi
  have hgqi : Integrable (fun x => (Set.Ioi t).indicator (1 : ℝ → ℝ) x * q x) μ := by
    rw [hind q]; exact hqi.indicator measurableSet_Ioi
  have h := integral_mul_integral_le_of_likelihoodRatioLE hp0 hq0 hlr
    (monotone_indicator_Ioi_one t) hpi hqi hgpi hgqi
  rwa [hind p, hind q, integral_indicator measurableSet_Ioi,
    integral_indicator measurableSet_Ioi] at h

end
