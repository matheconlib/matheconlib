module

public import Auctionlib.Auction.Affiliation.Basic
public import Auctionlib.ForMathlib.FourFunctions
public import Auctionlib.ForMathlib.UpdateLattice
public import Mathlib

/-! # Marginalization closure of affiliation

## Main results

* `Auction.Affiliation.Affiliated.update_le` : for `Affiliated f`,
  `f (u[j↦p]) * f (v[j↦q]) ≤ f ((u ⊔ v)[j↦p ⊔ q]) * f ((u ⊓ v)[j↦p ⊓ q])`.
* `Auction.Affiliation.Affiliated.permanent_le_of_le` : the permanent inequality for
  `Affiliated f` with `0 ≤ f`, under `s ≤ s'`.
* `Auction.Affiliation.Affiliated.permanent_le` : the permanent inequality for
  `Affiliated f` with `0 ≤ f`, for arbitrary `s`, `s'`: writing `a = u ⊔ v` and
  `b = u ⊓ v`,
  `f (u[j↦s]) * f (v[j↦s']) + f (u[j↦s']) * f (v[j↦s])
    ≤ f (a[j↦s]) * f (b[j↦s']) + f (a[j↦s']) * f (b[j↦s])`.
* `Auction.Affiliation.marginal` : `marginal μ f j x = ∫ s, f (Function.update x j s) ∂μ`.
* `Auction.Affiliation.marginal_nonneg` : `0 ≤ f` implies `0 ≤ marginal μ f j`.
* `Auction.Affiliation.marginal_affiliated` : if `Affiliated f`, `0 ≤ f` and every
  `j`-fibre `fun s => f (Function.update x j s)` is `μ`-integrable, then
  `Affiliated (marginal μ f j)`.
* `Auction.Affiliation.affiliated_iff_fourFunctionsLE_self` :
  `Affiliated f ↔ FourFunctionsLE f f f f`.
* `FourFunctionsLE.marginal` : `FourFunctionsLE f₁ f₂ f₃ f₄` with all four functions
  nonnegative and all `j`-fibres `μ`-integrable implies
  `FourFunctionsLE (marginal μ f₁ j) (marginal μ f₂ j) (marginal μ f₃ j) (marginal μ f₄ j)`.
* `Auction.Affiliation.marginalList` : `marginalList μ F (j :: l) = marginalList μ
  (marginal μ F j) l` and `marginalList μ F [] = F`.
* `Auction.Affiliation.FibreIntegrable` : `μ`-integrability of the `j`-fibres of every
  iterated marginal produced along a list of coordinates.
* `Auction.Affiliation.marginalList_nonneg` : `0 ≤ F` implies `0 ≤ marginalList μ F l`.
* `Auction.Affiliation.marginalList_congr_of_dependsOn` : if `F x = F y` whenever `x` and
  `y` agree on every `j ∈ l`, then `marginalList μ F l` is constant.
* `FourFunctionsLE.marginalList` : `FourFunctionsLE f₁ f₂ f₃ f₄` with all four functions
  nonnegative and `FibreIntegrable` along `l` implies `FourFunctionsLE` of the four
  iterated marginals along `l`.
* `Auction.Affiliation.FibreIntegrable.add`,
  `Auction.Affiliation.marginalList_add` : additivity of `marginalList`.
* `Auction.Affiliation.FibreIntegrable.const_mul`,
  `Auction.Affiliation.marginalList_const_mul` : `marginalList μ (fun y => c * F y) l x
  = c * marginalList μ F l x`.
* `Auction.Affiliation.marginal_pos_of_pos` : for `0 ≤ G`, `0 ≤ H` and `G` strictly positive
  wherever `H` is, `0 < marginal μ H j x` implies `0 < marginal μ G j x`.
* `Auction.Affiliation.marginalList_pos_of_pos` : the same implication for the iterated
  marginal along `l`, under `FibreIntegrable` along `l` for both functions.
* `Auction.Affiliation.marginalList_lt_of_lt` : for a nonnegative weight `ρ` whose iterated
  marginal along `l` is positive and `g₁ < g₂` pointwise,
  `marginalList μ (fun z => g₁ z * ρ z) l x < marginalList μ (fun z => g₂ z * ρ z) l x`.
-/

@[expose] public section

open MeasureTheory

namespace Auction.Affiliation

/-- Affiliation in a single coordinate, with the moving coordinate normalised:
`f (u[j↦p]) * f (v[j↦q]) ≤ f ((u ⊔ v)[j↦p ⊔ q]) * f ((u ⊓ v)[j↦p ⊓ q])`. -/
theorem Affiliated.update_le {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : Affiliated f)
    (j : Fin n) (u v : Fin n → ℝ) (p q : ℝ) :
    f (Function.update u j p) * f (Function.update v j q)
      ≤ f (Function.update (u ⊔ v) j (p ⊔ q))
        * f (Function.update (u ⊓ v) j (p ⊓ q)) := by
  have h := hf (Function.update u j p) (Function.update v j q)
  rw [Function.update_sup_update, Function.update_inf_update] at h
  exact h

/-- The permanent inequality for `Affiliated f` with `0 ≤ f`, in the ordered case
`s ≤ s'`: writing `a = u ⊔ v` and `b = u ⊓ v`,
`f (u[j↦s]) * f (v[j↦s']) + f (u[j↦s']) * f (v[j↦s])
  ≤ f (a[j↦s]) * f (b[j↦s']) + f (a[j↦s']) * f (b[j↦s])`. -/
theorem Affiliated.permanent_le_of_le {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : Affiliated f) (hf0 : 0 ≤ f) (j : Fin n) (u v : Fin n → ℝ) {s s' : ℝ}
    (hss : s ≤ s') :
    f (Function.update u j s) * f (Function.update v j s')
        + f (Function.update u j s') * f (Function.update v j s)
      ≤ f (Function.update (u ⊔ v) j s) * f (Function.update (u ⊓ v) j s')
        + f (Function.update (u ⊔ v) j s') * f (Function.update (u ⊓ v) j s) := by
  have h1 := hf.update_le j u v s s'
  have h2 := hf.update_le j u v s' s
  have h3 := hf.update_le j u v s s
  have h4 := hf.update_le j u v s' s'
  rw [sup_of_le_right hss, inf_of_le_left hss] at h1
  rw [sup_of_le_left hss, inf_of_le_right hss] at h2
  rw [sup_idem, inf_idem] at h3
  rw [sup_idem, inf_idem] at h4
  have hprod :
      (f (Function.update u j s) * f (Function.update v j s))
          * (f (Function.update u j s') * f (Function.update v j s'))
        ≤ (f (Function.update (u ⊔ v) j s) * f (Function.update (u ⊓ v) j s))
          * (f (Function.update (u ⊔ v) j s') * f (Function.update (u ⊓ v) j s')) :=
    mul_le_mul h3 h4 (mul_nonneg (hf0 _) (hf0 _)) (mul_nonneg (hf0 _) (hf0 _))
  have hPQ :
      (f (Function.update u j s) * f (Function.update v j s'))
          * (f (Function.update u j s') * f (Function.update v j s))
        ≤ (f (Function.update (u ⊔ v) j s') * f (Function.update (u ⊓ v) j s))
          * (f (Function.update (u ⊔ v) j s) * f (Function.update (u ⊓ v) j s')) := by
    calc (f (Function.update u j s) * f (Function.update v j s'))
            * (f (Function.update u j s') * f (Function.update v j s))
        = (f (Function.update u j s) * f (Function.update v j s))
            * (f (Function.update u j s') * f (Function.update v j s')) := by ring
      _ ≤ (f (Function.update (u ⊔ v) j s) * f (Function.update (u ⊓ v) j s))
            * (f (Function.update (u ⊔ v) j s') * f (Function.update (u ⊓ v) j s')) := hprod
      _ = (f (Function.update (u ⊔ v) j s') * f (Function.update (u ⊓ v) j s))
            * (f (Function.update (u ⊔ v) j s) * f (Function.update (u ⊓ v) j s')) := by ring
  have hmain := add_le_add_of_le_of_mul_le
    (mul_nonneg (hf0 (Function.update (u ⊔ v) j s')) (hf0 (Function.update (u ⊓ v) j s)))
    (mul_nonneg (hf0 (Function.update (u ⊔ v) j s)) (hf0 (Function.update (u ⊓ v) j s')))
    h1 h2 hPQ
  linarith

/-- The permanent inequality for `Affiliated f` with `0 ≤ f`, with no ordering of `s`
and `s'` required (unlike `Affiliated.permanent_le_of_le`, whose hypothesis is
`s ≤ s'`): writing `a = u ⊔ v` and `b = u ⊓ v`,
`f (u[j↦s]) * f (v[j↦s']) + f (u[j↦s']) * f (v[j↦s])
  ≤ f (a[j↦s]) * f (b[j↦s']) + f (a[j↦s']) * f (b[j↦s])`. -/
theorem Affiliated.permanent_le {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : Affiliated f) (hf0 : 0 ≤ f) (j : Fin n) (u v : Fin n → ℝ) (s s' : ℝ) :
    f (Function.update u j s) * f (Function.update v j s')
        + f (Function.update u j s') * f (Function.update v j s)
      ≤ f (Function.update (u ⊔ v) j s) * f (Function.update (u ⊓ v) j s')
        + f (Function.update (u ⊔ v) j s') * f (Function.update (u ⊓ v) j s) := by
  rcases le_total s s' with hss | hss
  · exact hf.permanent_le_of_le hf0 j u v hss
  · have h := hf.permanent_le_of_le hf0 j u v hss
    linarith

/-- `marginal μ f j x = ∫ s, f (Function.update x j s) ∂μ`. It is constant in coordinate
`j`. -/
noncomputable def marginal {n : ℕ} (μ : Measure ℝ) (f : (Fin n → ℝ) → ℝ)
    (j : Fin n) (x : Fin n → ℝ) : ℝ :=
  ∫ s, f (Function.update x j s) ∂μ

/-- `0 ≤ f` implies `0 ≤ marginal μ f j`. -/
theorem marginal_nonneg {n : ℕ} {μ : Measure ℝ} {f : (Fin n → ℝ) → ℝ}
    (hf0 : 0 ≤ f) (j : Fin n) : 0 ≤ marginal μ f j :=
  fun _ => integral_nonneg fun _ => hf0 _

/-- If `Affiliated f`, `0 ≤ f` and every `j`-fibre `fun s => f (Function.update x j s)`
is `μ`-integrable, then `Affiliated (marginal μ f j)`. -/
theorem marginal_affiliated {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]
    {f : (Fin n → ℝ) → ℝ} (hf : Affiliated f) (hf0 : 0 ≤ f) (j : Fin n)
    (hint : ∀ x : Fin n → ℝ, Integrable (fun s => f (Function.update x j s)) μ) :
    Affiliated (marginal μ f j) := by
  intro u v
  have hU := hint u
  have hV := hint v
  have hA := hint (u ⊔ v)
  have hB := hint (u ⊓ v)
  have h1 : Integrable (fun z : ℝ × ℝ => f (Function.update (u ⊔ v) j z.1)
      * f (Function.update (u ⊓ v) j z.2)) (μ.prod μ) := hA.mul_prod hB
  have h2 : Integrable (fun z : ℝ × ℝ => f (Function.update (u ⊓ v) j z.1)
      * f (Function.update (u ⊔ v) j z.2)) (μ.prod μ) := hB.mul_prod hA
  have h3 : Integrable (fun z : ℝ × ℝ => f (Function.update u j z.1)
      * f (Function.update v j z.2)) (μ.prod μ) := hU.mul_prod hV
  have h4 : Integrable (fun z : ℝ × ℝ => f (Function.update v j z.1)
      * f (Function.update u j z.2)) (μ.prod μ) := hV.mul_prod hU
  have e1 : ∫ z : ℝ × ℝ, f (Function.update (u ⊔ v) j z.1)
        * f (Function.update (u ⊓ v) j z.2) ∂(μ.prod μ)
      = (∫ s, f (Function.update (u ⊔ v) j s) ∂μ)
        * ∫ s, f (Function.update (u ⊓ v) j s) ∂μ :=
    integral_prod_mul (fun s => f (Function.update (u ⊔ v) j s))
      (fun s => f (Function.update (u ⊓ v) j s))
  have e2 : ∫ z : ℝ × ℝ, f (Function.update (u ⊓ v) j z.1)
        * f (Function.update (u ⊔ v) j z.2) ∂(μ.prod μ)
      = (∫ s, f (Function.update (u ⊓ v) j s) ∂μ)
        * ∫ s, f (Function.update (u ⊔ v) j s) ∂μ :=
    integral_prod_mul (fun s => f (Function.update (u ⊓ v) j s))
      (fun s => f (Function.update (u ⊔ v) j s))
  have e3 : ∫ z : ℝ × ℝ, f (Function.update u j z.1)
        * f (Function.update v j z.2) ∂(μ.prod μ)
      = (∫ s, f (Function.update u j s) ∂μ) * ∫ s, f (Function.update v j s) ∂μ :=
    integral_prod_mul (fun s => f (Function.update u j s))
      (fun s => f (Function.update v j s))
  have e4 : ∫ z : ℝ × ℝ, f (Function.update v j z.1)
        * f (Function.update u j z.2) ∂(μ.prod μ)
      = (∫ s, f (Function.update v j s) ∂μ) * ∫ s, f (Function.update u j s) ∂μ :=
    integral_prod_mul (fun s => f (Function.update v j s))
      (fun s => f (Function.update u j s))
  have hpt : ∀ z : ℝ × ℝ,
      f (Function.update u j z.1) * f (Function.update v j z.2)
          + f (Function.update v j z.1) * f (Function.update u j z.2)
        ≤ f (Function.update (u ⊔ v) j z.1) * f (Function.update (u ⊓ v) j z.2)
          + f (Function.update (u ⊓ v) j z.1) * f (Function.update (u ⊔ v) j z.2) := by
    intro z
    have h := hf.permanent_le hf0 j u v z.1 z.2
    linarith
  have hmono : ∫ z : ℝ × ℝ, (f (Function.update u j z.1) * f (Function.update v j z.2)
          + f (Function.update v j z.1) * f (Function.update u j z.2)) ∂(μ.prod μ)
      ≤ ∫ z : ℝ × ℝ, (f (Function.update (u ⊔ v) j z.1) * f (Function.update (u ⊓ v) j z.2)
          + f (Function.update (u ⊓ v) j z.1) * f (Function.update (u ⊔ v) j z.2))
          ∂(μ.prod μ) :=
    integral_mono (h3.add h4) (h1.add h2) hpt
  rw [integral_add h3 h4, integral_add h1 h2, e1, e2, e3, e4] at hmono
  simp only [marginal, ge_iff_le]
  linarith

/-! ### The four-functions relation along a list of coordinates -/

/-- `Affiliated f ↔ FourFunctionsLE f f f f`. -/
theorem affiliated_iff_fourFunctionsLE_self {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    Affiliated f ↔ FourFunctionsLE f f f f := by
  constructor
  · intro h x y
    exact (h x y).trans_eq (mul_comm _ _)
  · intro h x y
    exact (h x y).trans_eq (mul_comm _ _)

/-- If `FourFunctionsLE f₁ f₂ f₃ f₄`, all four functions are nonnegative and all their
`j`-fibres `fun s => f_k (Function.update x j s)` are `μ`-integrable, then
`FourFunctionsLE (marginal μ f₁ j) (marginal μ f₂ j) (marginal μ f₃ j)
(marginal μ f₄ j)`. -/
theorem _root_.FourFunctionsLE.marginal {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]
    {f₁ f₂ f₃ f₄ : (Fin n → ℝ) → ℝ} (h : FourFunctionsLE f₁ f₂ f₃ f₄)
    (h₁ : 0 ≤ f₁) (h₂ : 0 ≤ f₂) (h₃ : 0 ≤ f₃) (h₄ : 0 ≤ f₄) (j : Fin n)
    (k₁ : ∀ x : Fin n → ℝ, Integrable (fun s => f₁ (Function.update x j s)) μ)
    (k₂ : ∀ x : Fin n → ℝ, Integrable (fun s => f₂ (Function.update x j s)) μ)
    (k₃ : ∀ x : Fin n → ℝ, Integrable (fun s => f₃ (Function.update x j s)) μ)
    (k₄ : ∀ x : Fin n → ℝ, Integrable (fun s => f₄ (Function.update x j s)) μ) :
    FourFunctionsLE (marginal μ f₁ j) (marginal μ f₂ j) (marginal μ f₃ j)
      (marginal μ f₄ j) := by
  intro u v
  have hff : FourFunctionsLE (fun s => f₁ (Function.update u j s))
      (fun s => f₂ (Function.update v j s))
      (fun s => f₃ (Function.update (u ⊓ v) j s))
      (fun s => f₄ (Function.update (u ⊔ v) j s)) := by
    intro s s'
    have hs := h (Function.update u j s) (Function.update v j s')
    rwa [Function.update_inf_update, Function.update_sup_update] at hs
  simpa only [marginal] using integral_mul_integral_le_of_fourFunctionsLE hff
    (fun _ => h₁ _) (fun _ => h₂ _) (fun _ => h₃ _) (fun _ => h₄ _)
    (k₁ u) (k₂ v) (k₃ (u ⊓ v)) (k₄ (u ⊔ v))

/-- `marginalList μ F l` marginalizes the coordinates listed in `l`, head first:
`marginalList μ F [] = F` and
`marginalList μ F (j :: l) = marginalList μ (marginal μ F j) l`. -/
noncomputable def marginalList {n : ℕ} (μ : Measure ℝ) :
    ((Fin n → ℝ) → ℝ) → List (Fin n) → (Fin n → ℝ) → ℝ
  | F, [], x => F x
  | F, j :: l, x => marginalList μ (marginal μ F j) l x

/-- `FibreIntegrable μ F l` asserts that at every stage of the iteration
`marginalList μ F l` the `j`-fibres of the current function are `μ`-integrable:
`FibreIntegrable μ F [] = True` and `FibreIntegrable μ F (j :: l)` is
`(∀ x, Integrable (fun s => F (Function.update x j s)) μ) ∧
FibreIntegrable μ (marginal μ F j) l`. -/
def FibreIntegrable {n : ℕ} (μ : Measure ℝ) :
    ((Fin n → ℝ) → ℝ) → List (Fin n) → Prop
  | _, [] => True
  | F, j :: l => (∀ x : Fin n → ℝ, Integrable (fun s => F (Function.update x j s)) μ)
      ∧ FibreIntegrable μ (marginal μ F j) l

/-- `0 ≤ F` implies `0 ≤ marginalList μ F l`. -/
theorem marginalList_nonneg {n : ℕ} {μ : Measure ℝ} :
    ∀ (l : List (Fin n)) {F : (Fin n → ℝ) → ℝ}, 0 ≤ F → 0 ≤ marginalList μ F l := by
  intro l
  induction l with
  | nil => intro F hF; exact hF
  | cons j l ih => intro F hF; exact ih (marginal_nonneg hF j)

/-- If `F x = F y` whenever `x` and `y` agree on every `j ∈ l`, then `marginalList μ F l`
is constant: `marginalList μ F l x = marginalList μ F l y` for all `x`, `y`. -/
theorem marginalList_congr_of_dependsOn {n : ℕ} {μ : Measure ℝ} :
    ∀ (l : List (Fin n)) {F : (Fin n → ℝ) → ℝ},
      (∀ x y : Fin n → ℝ, (∀ j ∈ l, x j = y j) → F x = F y) →
      ∀ x y : Fin n → ℝ, marginalList μ F l x = marginalList μ F l y := by
  intro l
  induction l with
  | nil => intro F hF x y; exact hF x y (by simp)
  | cons j l ih =>
    intro F hF x y
    show marginalList μ (marginal μ F j) l x = marginalList μ (marginal μ F j) l y
    refine ih (fun u v huv => ?_) x y
    have hfun : (fun s => F (Function.update u j s))
        = fun s => F (Function.update v j s) := by
      funext s
      refine hF _ _ fun k hk => ?_
      obtain rfl | hkj := eq_or_ne k j
      · simp
      · simp only [Function.update_of_ne hkj]
        exact huv k ((List.mem_cons.1 hk).resolve_left hkj)
    simp only [marginal, hfun]

/-- If `FourFunctionsLE f₁ f₂ f₃ f₄`, all four functions are nonnegative and all four are
`FibreIntegrable` along `l`, then the four iterated marginals along `l` again satisfy the
four-functions relation. -/
theorem _root_.FourFunctionsLE.marginalList {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ] :
    ∀ (l : List (Fin n)) {f₁ f₂ f₃ f₄ : (Fin n → ℝ) → ℝ},
      FourFunctionsLE f₁ f₂ f₃ f₄ → 0 ≤ f₁ → 0 ≤ f₂ → 0 ≤ f₃ → 0 ≤ f₄ →
      FibreIntegrable μ f₁ l → FibreIntegrable μ f₂ l → FibreIntegrable μ f₃ l →
      FibreIntegrable μ f₄ l →
      FourFunctionsLE (marginalList μ f₁ l) (marginalList μ f₂ l)
        (marginalList μ f₃ l) (marginalList μ f₄ l) := by
  intro l
  induction l with
  | nil => intro f₁ f₂ f₃ f₄ h _ _ _ _ _ _ _ _; exact h
  | cons j l ih =>
    intro f₁ f₂ f₃ f₄ h h₁ h₂ h₃ h₄ k₁ k₂ k₃ k₄
    exact ih (h.marginal h₁ h₂ h₃ h₄ j k₁.1 k₂.1 k₃.1 k₄.1)
      (marginal_nonneg h₁ j) (marginal_nonneg h₂ j) (marginal_nonneg h₃ j)
      (marginal_nonneg h₄ j) k₁.2 k₂.2 k₃.2 k₄.2

/-! ### Linearity of `marginalList` -/

private theorem fibreIntegrable_add_and_marginalList_add {n : ℕ} {μ : Measure ℝ} :
    ∀ (l : List (Fin n)) {F G : (Fin n → ℝ) → ℝ},
      FibreIntegrable μ F l → FibreIntegrable μ G l →
      FibreIntegrable μ (fun x => F x + G x) l
        ∧ ∀ x, marginalList μ (fun y => F y + G y) l x
            = marginalList μ F l x + marginalList μ G l x := by
  intro l
  induction l with
  | nil => intro F G _ _; exact ⟨trivial, fun _ => rfl⟩
  | cons j l ih =>
    intro F G hF hG
    have hmarg : marginal μ (fun y => F y + G y) j
        = fun x => marginal μ F j x + marginal μ G j x := by
      funext x
      simpa only [marginal] using integral_add (hF.1 x) (hG.1 x)
    refine ⟨⟨fun x => (hF.1 x).add (hG.1 x), ?_⟩, fun x => ?_⟩
    · rw [show (marginal μ (fun x => F x + G x) j)
          = fun x => marginal μ F j x + marginal μ G j x from hmarg]
      exact (ih hF.2 hG.2).1
    · show marginalList μ (marginal μ (fun y => F y + G y) j) l x
          = marginalList μ (marginal μ F j) l x + marginalList μ (marginal μ G j) l x
      rw [hmarg]
      exact (ih hF.2 hG.2).2 x

private theorem fibreIntegrable_const_mul_and_marginalList_const_mul {n : ℕ}
    {μ : Measure ℝ} :
    ∀ (l : List (Fin n)) {F : (Fin n → ℝ) → ℝ} (c : ℝ), FibreIntegrable μ F l →
      FibreIntegrable μ (fun x => c * F x) l
        ∧ ∀ x, marginalList μ (fun y => c * F y) l x = c * marginalList μ F l x := by
  intro l
  induction l with
  | nil => intro F c _; exact ⟨trivial, fun _ => rfl⟩
  | cons j l ih =>
    intro F c hF
    have hmarg : marginal μ (fun y => c * F y) j = fun x => c * marginal μ F j x := by
      funext x
      simpa only [marginal] using integral_const_mul c fun s => F (Function.update x j s)
    refine ⟨⟨fun x => (hF.1 x).const_mul c, ?_⟩, fun x => ?_⟩
    · rw [show (marginal μ (fun x => c * F x) j) = fun x => c * marginal μ F j x from hmarg]
      exact (ih c hF.2).1
    · show marginalList μ (marginal μ (fun y => c * F y) j) l x
          = c * marginalList μ (marginal μ F j) l x
      rw [hmarg]
      exact (ih c hF.2).2 x

/-- `FibreIntegrable` is closed under pointwise addition. -/
theorem FibreIntegrable.add {n : ℕ} {μ : Measure ℝ} {F G : (Fin n → ℝ) → ℝ}
    {l : List (Fin n)} (hF : FibreIntegrable μ F l) (hG : FibreIntegrable μ G l) :
    FibreIntegrable μ (fun x => F x + G x) l :=
  (fibreIntegrable_add_and_marginalList_add l hF hG).1

/-- `marginalList μ (fun y => F y + G y) l x = marginalList μ F l x + marginalList μ G l x`
for `F`, `G` `FibreIntegrable` along `l`. -/
theorem marginalList_add {n : ℕ} {μ : Measure ℝ} {F G : (Fin n → ℝ) → ℝ}
    {l : List (Fin n)} (hF : FibreIntegrable μ F l) (hG : FibreIntegrable μ G l)
    (x : Fin n → ℝ) :
    marginalList μ (fun y => F y + G y) l x
      = marginalList μ F l x + marginalList μ G l x :=
  (fibreIntegrable_add_and_marginalList_add l hF hG).2 x

/-- `FibreIntegrable` is closed under multiplication by a constant. -/
theorem FibreIntegrable.const_mul {n : ℕ} {μ : Measure ℝ} {F : (Fin n → ℝ) → ℝ}
    {l : List (Fin n)} (hF : FibreIntegrable μ F l) (c : ℝ) :
    FibreIntegrable μ (fun x => c * F x) l :=
  (fibreIntegrable_const_mul_and_marginalList_const_mul l c hF).1

/-- `marginalList μ (fun y => c * F y) l x = c * marginalList μ F l x` for `F`
`FibreIntegrable` along `l`. -/
theorem marginalList_const_mul {n : ℕ} {μ : Measure ℝ} {F : (Fin n → ℝ) → ℝ}
    {l : List (Fin n)} (hF : FibreIntegrable μ F l) (c : ℝ) (x : Fin n → ℝ) :
    marginalList μ (fun y => c * F y) l x = c * marginalList μ F l x :=
  (fibreIntegrable_const_mul_and_marginalList_const_mul l c hF).2 x

/-! ### Positivity of `marginalList`

A single integral `∫ s, G (x[j↦s]) ∂μ` of a nonnegative `G` is positive exactly when the
`j`-fibre of `G` has support of positive `μ`-measure
(`MeasureTheory.integral_pos_iff_support_of_nonneg`). Comparing two nonnegative functions
therefore reduces to comparing supports, and `marginal_pos_of_pos` transfers positivity from
`H` to any `G` that is strictly positive wherever `H` is.

Iterating along a list needs the hypothesis in exactly this *implication* form. The
positivity of a stage weight is not available from the positivity of the final iterated
integral, and the product structure `G = g * ρ` is destroyed by the first marginalization; the
implication `0 < H z → 0 < G z`, by contrast, is reproduced at every stage by
`marginal_pos_of_pos`, which is what makes the induction in `marginalList_pos_of_pos` go
through with no stage-wise positivity hypothesis. -/

/-- If `0 ≤ G`, `0 ≤ H`, `G` is strictly positive wherever `H` is, and both `j`-fibres at `x`
are `μ`-integrable, then `0 < marginal μ H j x` implies `0 < marginal μ G j x`. -/
theorem marginal_pos_of_pos {n : ℕ} {μ : Measure ℝ} {G H : (Fin n → ℝ) → ℝ}
    (hG0 : 0 ≤ G) (hH0 : 0 ≤ H) (hGH : ∀ z, 0 < H z → 0 < G z) (j : Fin n) (x : Fin n → ℝ)
    (hH : Integrable (fun s => H (Function.update x j s)) μ)
    (hG : Integrable (fun s => G (Function.update x j s)) μ)
    (hpos : 0 < marginal μ H j x) : 0 < marginal μ G j x := by
  rw [marginal, integral_pos_iff_support_of_nonneg
    (f := fun s => G (Function.update x j s)) (fun _ => hG0 _) hG]
  rw [marginal, integral_pos_iff_support_of_nonneg
    (f := fun s => H (Function.update x j s)) (fun _ => hH0 _) hH] at hpos
  refine hpos.trans_le (measure_mono fun s hs => ?_)
  have hHs : 0 < H (Function.update x j s) :=
    lt_of_le_of_ne (hH0 _) (Ne.symm (Function.mem_support.1 hs))
  exact Function.mem_support.2 (hGH _ hHs).ne'

/-- If `0 ≤ G`, `0 ≤ H`, `G` is strictly positive wherever `H` is, and both are
`FibreIntegrable` along `l`, then `0 < marginalList μ H l x` implies
`0 < marginalList μ G l x`. -/
theorem marginalList_pos_of_pos {n : ℕ} {μ : Measure ℝ} :
    ∀ (l : List (Fin n)) {G H : (Fin n → ℝ) → ℝ} (x : Fin n → ℝ),
      0 ≤ G → 0 ≤ H → (∀ z, 0 < H z → 0 < G z) →
      FibreIntegrable μ G l → FibreIntegrable μ H l →
      0 < marginalList μ H l x → 0 < marginalList μ G l x := by
  intro l
  induction l with
  | nil => intro G H x _ _ hGH _ _ hpos; exact hGH x hpos
  | cons j l ih =>
    intro G H x hG0 hH0 hGH hG hH hpos
    exact ih x (marginal_nonneg hG0 j) (marginal_nonneg hH0 j)
      (fun z hz => marginal_pos_of_pos hG0 hH0 hGH j z (hH.1 z) (hG.1 z) hz) hG.2 hH.2 hpos

/-- Strict comparison of two iterated marginals against a common nonnegative weight `ρ`:
if `g₁ z < g₂ z` for every `z`, the iterated marginal of `ρ` along `l` at `x` is positive,
and `ρ`, `g₁ * ρ` and `g₂ * ρ` are all `FibreIntegrable` along `l`, then
`marginalList μ (fun z => g₁ z * ρ z) l x < marginalList μ (fun z => g₂ z * ρ z) l x`.

The three integrability hypotheses are what the proof consumes: `ρ` carries the positivity
through the induction, and the two products are needed to split
`g₂ * ρ = g₁ * ρ + (g₂ - g₁) * ρ` by `marginalList_add`. -/
theorem marginalList_lt_of_lt {n : ℕ} {μ : Measure ℝ} :
    ∀ (l : List (Fin n)) {ρ g₁ g₂ : (Fin n → ℝ) → ℝ} (x : Fin n → ℝ),
      0 ≤ ρ → (∀ z, g₁ z < g₂ z) → 0 < marginalList μ ρ l x →
      FibreIntegrable μ ρ l → FibreIntegrable μ (fun z => g₁ z * ρ z) l →
      FibreIntegrable μ (fun z => g₂ z * ρ z) l →
      marginalList μ (fun z => g₁ z * ρ z) l x
        < marginalList μ (fun z => g₂ z * ρ z) l x := by
  intro l ρ g₁ g₂ x hρ hg hpos hIρ h₁ h₂
  have hdiffeq : (fun z => (g₂ z - g₁ z) * ρ z)
      = fun z => g₂ z * ρ z + (-1) * (g₁ z * ρ z) := by
    funext z; ring
  have hdiff : FibreIntegrable μ (fun z => (g₂ z - g₁ z) * ρ z) l := by
    rw [hdiffeq]; exact h₂.add (h₁.const_mul (-1))
  have hlt : 0 < marginalList μ (fun z => (g₂ z - g₁ z) * ρ z) l x :=
    marginalList_pos_of_pos l x (fun z => mul_nonneg (sub_nonneg.2 (hg z).le) (hρ z)) hρ
      (fun z hz => mul_pos (sub_pos.2 (hg z)) hz) hdiff hIρ hpos
  have hadd := marginalList_add h₁ hdiff x
  have hsum : (fun y => g₁ y * ρ y + (g₂ y - g₁ y) * ρ y) = fun y => g₂ y * ρ y := by
    funext y; ring
  rw [hsum] at hadd
  linarith

end Auction.Affiliation

end
