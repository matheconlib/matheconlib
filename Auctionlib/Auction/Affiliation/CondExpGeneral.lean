module

public import Auctionlib.Auction.Affiliation.Marginal
public import Auctionlib.ForMathlib.FourFunctions
public import Auctionlib.ForMathlib.UpdateLattice
public import Mathlib

/-! # Lemma 7.3 — monotone conditional expectations, general `n`, continuous case

## Main results

* `Affiliated.fourFunctionsLE_slice_mul`: `FourFunctionsLE` for the four pinned slice products.
* `Affiliated.marginalList_mul_le`: `N t * D t' ≤ D t * N t'` for the iterated slice marginals.
* `Affiliated.marginalList_mul_le_of_bddBelow`: the same with `0 ≤ g` weakened to bounded below.
* `rivals`: `rivals i = (Finset.univ.erase i).sort (· ≤ ·)`.
* `length_rivals`, `mem_rivals_iff`: `(rivals i).length = n - 1` and `j ∈ rivals i ↔ j ≠ i`.
* `condNumer`, `condDenom`: the iterated marginals of the pinned slice products along `rivals i`.
* `Affiliated.condNumer_mul_condDenom_le`: Lemma 7.3, cross-multiplied.
* `Affiliated.condNumer_mul_condDenom_le_of_bddBelow`: `0 ≤ g` weakened to bounded below.
* `Affiliated.monotone_condExp`: `Monotone` of the ratio under globally positive `condDenom`.
* `Affiliated.monotoneOn_condExp`: `MonotoneOn` over the positivity set of `condDenom`.
* `marginalList_rivals_congr`: constancy in the base profile for `F` independent of `i`.

The conditional expectation is realised as the iterated marginal `marginalList μ · (rivals i)`,
not as an integral against `MeasureTheory.Measure.pi` over the rival coordinates, and nothing
here refers to `MeasureTheory.condExp`. The two agree by Fubini–Tonelli under the
`FibreIntegrable` hypotheses, which are assumed rather than derived; `0 ≤ g` (respectively
`∃ m, ∀ y, m ≤ g y`) is required.
-/

@[expose] public section

open MeasureTheory
open scoped Function

namespace Auction.Affiliation

/-- For `Affiliated f` with `0 ≤ f`, `Monotone g`, `0 ≤ g` and `t ≤ t'`, the quadruple
`f₁ z = g (z[i↦t]) * f (z[i↦t])`, `f₂ z = f (z[i↦t'])`, `f₃ z = f (z[i↦t])`,
`f₄ z = g (z[i↦t']) * f (z[i↦t'])` satisfies `FourFunctionsLE f₁ f₂ f₃ f₄`, i.e.
`g (z[i↦t]) * f (z[i↦t]) * f (w[i↦t'])
  ≤ f ((z ⊓ w)[i↦t]) * (g ((z ⊔ w)[i↦t']) * f ((z ⊔ w)[i↦t']))`. -/
theorem Affiliated.fourFunctionsLE_slice_mul {n : ℕ} {f g : (Fin n → ℝ) → ℝ}
    (hf : Affiliated f) (hf0 : 0 ≤ f) (hg : Monotone g) (hg0 : 0 ≤ g) (i : Fin n)
    {t t' : ℝ} (ht : t ≤ t') :
    FourFunctionsLE (fun z => g (z[i ↦ t]) * f (z[i ↦ t])) (fun z => f (z[i ↦ t']))
      (fun z => f (z[i ↦ t]))
      (fun z => g (z[i ↦ t']) * f (z[i ↦ t'])) := by
  intro z w
  dsimp only
  have ha : f (z[i ↦ t]) * f (w[i ↦ t']) ≤ f ((z ⊓ w)[i ↦ t]) * f ((z ⊔ w)[i ↦ t']) := by
    have hs := hf (z[i ↦ t]) (w[i ↦ t'])
    rw [Function.update_sup_update, Function.update_inf_update, sup_of_le_right ht,
      inf_of_le_left ht] at hs
    linarith
  have hb : g (z[i ↦ t]) ≤ g ((z ⊔ w)[i ↦ t']) := by
    refine hg fun k => ?_
    obtain rfl | hk := eq_or_ne k i
    · simpa using ht
    · simp only [Function.update_of_ne hk, Pi.sup_apply]
      exact le_sup_left
  calc g (z[i ↦ t]) * f (z[i ↦ t]) * f (w[i ↦ t']) = g (z[i ↦ t])
          * (f (z[i ↦ t]) * f (w[i ↦ t'])) := by ring
    _ ≤ g ((z ⊔ w)[i ↦ t']) * (f ((z ⊓ w)[i ↦ t]) * f ((z ⊔ w)[i ↦ t'])) :=
        mul_le_mul hb ha (mul_nonneg (hf0 _) (hf0 _)) (hg0 _)
    _ = f ((z ⊓ w)[i ↦ t]) * (g ((z ⊔ w)[i ↦ t']) * f ((z ⊔ w)[i ↦ t'])) := by ring

/-- **Lemma 7.3, general `n`, continuous case**, in cross-multiplied form along an
arbitrary list `l` of marginalized coordinates. For `Affiliated f` with `0 ≤ f`,
`Monotone g`, `0 ≤ g`, `t ≤ t'` and all four slices `FibreIntegrable` along `l`,
writing `N s = marginalList μ (fun z => g (z[i↦s]) * f (z[i↦s])) l x` and
`D s = marginalList μ (fun z => f (z[i↦s])) l x`, one has `N t * D t' ≤ D t * N t'`.

`0 ≤ g` is required on all of `Fin n → ℝ`, including off the support of `f`, where the
notes assume only that `g` is nondecreasing and integrable.

`i` is not required to be absent from `l`. For finite `μ`, a repetition of `i` in `l`
rescales all four iterated marginals by the same nonnegative mass. -/
theorem Affiliated.marginalList_mul_le {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]
    {f g : (Fin n → ℝ) → ℝ} (hf : Affiliated f) (hf0 : 0 ≤ f) (hg : Monotone g)
    (hg0 : 0 ≤ g) (i : Fin n) (l : List (Fin n)) {t t' : ℝ} (ht : t ≤ t')
    (h₁ : FibreIntegrable μ (fun z => g (z[i ↦ t]) * f (z[i ↦ t])) l)
    (h₂ : FibreIntegrable μ (fun z => f (z[i ↦ t'])) l)
    (h₃ : FibreIntegrable μ (fun z => f (z[i ↦ t])) l)
    (h₄ : FibreIntegrable μ (fun z => g (z[i ↦ t']) * f (z[i ↦ t'])) l)
    (x : Fin n → ℝ) :
    marginalList μ (fun z => g (z[i ↦ t]) * f (z[i ↦ t])) l x
        * marginalList μ (fun z => f (z[i ↦ t'])) l x ≤ marginalList μ (fun z => f (z[i ↦ t])) l x
        * marginalList μ (fun z => g (z[i ↦ t']) * f (z[i ↦ t'])) l x := by
  have key := (hf.fourFunctionsLE_slice_mul hf0 hg hg0 i ht).marginalList l
    (fun z => mul_nonneg (hg0 (z[i ↦ t])) (hf0 (z[i ↦ t])))
    (fun z => hf0 (z[i ↦ t']))
    (fun z => hf0 (z[i ↦ t]))
    (fun z => mul_nonneg (hg0 (z[i ↦ t'])) (hf0 (z[i ↦ t'])))
    h₁ h₂ h₃ h₄ x x
  simpa only [inf_idem, sup_idem] using key

/-- `Affiliated.marginalList_mul_le` with `0 ≤ g` weakened to `∃ m, ∀ y, m ≤ g y`: for
`Affiliated f` with `0 ≤ f`, `Monotone g`, `m ≤ g` pointwise, `t ≤ t'` and all four
slices `FibreIntegrable` along `l`, `N t * D t' ≤ D t * N t'`. -/
theorem Affiliated.marginalList_mul_le_of_bddBelow {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]
    {f g : (Fin n → ℝ) → ℝ} (hf : Affiliated f) (hf0 : 0 ≤ f) (hg : Monotone g)
    {m : ℝ} (hm : ∀ y, m ≤ g y) (i : Fin n) (l : List (Fin n)) {t t' : ℝ} (ht : t ≤ t')
    (h₁ : FibreIntegrable μ (fun z => g (z[i ↦ t]) * f (z[i ↦ t])) l)
    (h₂ : FibreIntegrable μ (fun z => f (z[i ↦ t'])) l)
    (h₃ : FibreIntegrable μ (fun z => f (z[i ↦ t])) l)
    (h₄ : FibreIntegrable μ (fun z => g (z[i ↦ t']) * f (z[i ↦ t'])) l)
    (x : Fin n → ℝ) :
    marginalList μ (fun z => g (z[i ↦ t]) * f (z[i ↦ t])) l x
        * marginalList μ (fun z => f (z[i ↦ t'])) l x ≤ marginalList μ (fun z => f (z[i ↦ t])) l x
        * marginalList μ (fun z => g (z[i ↦ t']) * f (z[i ↦ t'])) l x := by
  have hg₀ : Monotone fun y => g y - m := fun a b hab => sub_le_sub_right (hg hab) m
  have hg₀0 : (0 : (Fin n → ℝ) → ℝ) ≤ fun y => g y - m := fun y => sub_nonneg.2 (hm y)
  have key : ∀ s : ℝ,
      FibreIntegrable μ (fun z => g (z[i ↦ s]) * f (z[i ↦ s])) l →
      FibreIntegrable μ (fun z => f (z[i ↦ s])) l →
      FibreIntegrable μ (fun z => (g (z[i ↦ s]) - m) * f (z[i ↦ s])) l
        ∧ marginalList μ (fun z => (g (z[i ↦ s]) - m) * f (z[i ↦ s])) l x = marginalList μ
              (fun z => g (z[i ↦ s]) * f (z[i ↦ s])) l x
            - m * marginalList μ (fun z => f (z[i ↦ s])) l x := by
    intro s hs hd
    have hG : FibreIntegrable μ (fun z => (-m) * f (z[i ↦ s])) l :=
      hd.const_mul (-m)
    have hfe : (fun z : Fin n → ℝ => (g (z[i ↦ s]) - m) * f (z[i ↦ s]))
        = fun z : Fin n → ℝ => g (z[i ↦ s]) * f (z[i ↦ s])
            + (-m) * f (z[i ↦ s]) := by
      funext z; ring
    refine ⟨?_, ?_⟩
    · rw [hfe]; exact hs.add hG
    · have hsum := marginalList_add (F := fun z => g (z[i ↦ s]) * f (z[i ↦ s]))
        (G := fun z => (-m) * f (z[i ↦ s])) hs hG x
      have hcm := marginalList_const_mul (F := fun z => f (z[i ↦ s])) hd (-m) x
      rw [hfe, hsum, hcm]; ring
  obtain ⟨k₁, v₁⟩ := key t h₁ h₃
  obtain ⟨k₄, v₄⟩ := key t' h₄ h₂
  have main := hf.marginalList_mul_le hf0 hg₀ hg₀0 i l ht k₁ h₂ h₃ k₄ x
  rw [v₁, v₄] at main
  nlinarith [main]

/-! ### Integrating out all rival coordinates -/

/-- `rivals i = (Finset.univ.erase i).sort (· ≤ ·)`, the increasing list of the
coordinates other than `i`. -/
def rivals {n : ℕ} (i : Fin n) : List (Fin n) :=
  (Finset.univ.erase i).sort (· ≤ ·)

/-- `(rivals i).length = n - 1`. -/
theorem length_rivals {n : ℕ} (i : Fin n) : (rivals i).length = n - 1 := by
  simp [rivals, Finset.length_sort, Finset.card_erase_of_mem]

/-- `j ∈ rivals i ↔ j ≠ i`. -/
theorem mem_rivals_iff {n : ℕ} (i j : Fin n) : j ∈ rivals i ↔ j ≠ i := by
  simp [rivals, Finset.mem_sort]

/-- `condNumer μ f g i t = marginalList μ (fun z => g (z[i↦t]) * f (z[i↦t])) (rivals i) 0`:
the numerator of `E[g(X) | Xᵢ = t]`, with every coordinate other than `i` integrated
against `μ`. -/
noncomputable def condNumer {n : ℕ} (μ : Measure ℝ) (f g : (Fin n → ℝ) → ℝ)
    (i : Fin n) (t : ℝ) : ℝ :=
  marginalList μ (fun z => g (z[i ↦ t]) * f (z[i ↦ t])) (rivals i) 0

/-- `condDenom μ f i t = marginalList μ (fun z => f (z[i↦t])) (rivals i) 0`: the
denominator of `E[g(X) | Xᵢ = t]`, with every coordinate other than `i` integrated
against `μ`. -/
noncomputable def condDenom {n : ℕ} (μ : Measure ℝ) (f : (Fin n → ℝ) → ℝ) (i : Fin n) (t : ℝ) : ℝ :=
  marginalList μ (fun z => f (z[i ↦ t])) (rivals i) 0

/-- **Lemma 7.3** (monotone conditional expectations), general `n`, continuous case, in
cross-multiplied form: for `Affiliated f` with `0 ≤ f`, `Monotone g`, `0 ≤ g`, `t ≤ t'`
and the four slices `FibreIntegrable` along `rivals i`,
`condNumer μ f g i t * condDenom μ f i t' ≤ condDenom μ f i t * condNumer μ f g i t'`.

`0 ≤ g` is required on all of `Fin n → ℝ`, including off the support of `f`, where the
notes assume only that `g` is nondecreasing and integrable. -/
theorem Affiliated.condNumer_mul_condDenom_le {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]
    {f g : (Fin n → ℝ) → ℝ} (hf : Affiliated f) (hf0 : 0 ≤ f) (hg : Monotone g)
    (hg0 : 0 ≤ g) (i : Fin n) {t t' : ℝ} (ht : t ≤ t')
    (h₁ : FibreIntegrable μ (fun z => g (z[i ↦ t]) * f (z[i ↦ t])) (rivals i))
    (h₂ : FibreIntegrable μ (fun z => f (z[i ↦ t'])) (rivals i))
    (h₃ : FibreIntegrable μ (fun z => f (z[i ↦ t])) (rivals i))
    (h₄ : FibreIntegrable μ (fun z => g (z[i ↦ t']) * f (z[i ↦ t'])) (rivals i)) :
    condNumer μ f g i t * condDenom μ f i t' ≤ condDenom μ f i t * condNumer μ f g i t' :=
  hf.marginalList_mul_le hf0 hg hg0 i (rivals i) ht h₁ h₂ h₃ h₄ 0

/-- `Affiliated.condNumer_mul_condDenom_le` with `0 ≤ g` weakened to `∃ m, ∀ y, m ≤ g y`. -/
theorem Affiliated.condNumer_mul_condDenom_le_of_bddBelow {n : ℕ} {μ : Measure ℝ}
    [SigmaFinite μ] {f g : (Fin n → ℝ) → ℝ} (hf : Affiliated f) (hf0 : 0 ≤ f)
    (hg : Monotone g) {m : ℝ} (hm : ∀ y, m ≤ g y) (i : Fin n) {t t' : ℝ} (ht : t ≤ t')
    (h₁ : FibreIntegrable μ (fun z => g (z[i ↦ t]) * f (z[i ↦ t])) (rivals i))
    (h₂ : FibreIntegrable μ (fun z => f (z[i ↦ t'])) (rivals i))
    (h₃ : FibreIntegrable μ (fun z => f (z[i ↦ t])) (rivals i))
    (h₄ : FibreIntegrable μ (fun z => g (z[i ↦ t']) * f (z[i ↦ t'])) (rivals i)) :
    condNumer μ f g i t * condDenom μ f i t' ≤ condDenom μ f i t * condNumer μ f g i t' :=
  hf.marginalList_mul_le_of_bddBelow hf0 hg hm i (rivals i) ht h₁ h₂ h₃ h₄ 0

/-- **Lemma 7.3**, division form on the set where the denominator is positive: for
`Affiliated f` with `0 ≤ f`, `Monotone g`, `0 ≤ g` and the four slices `FibreIntegrable`
along `rivals i` at every height, `t ↦ condNumer μ f g i t / condDenom μ f i t` is
nondecreasing on `{t | 0 < condDenom μ f i t}`.

`0 ≤ g` is required on all of `Fin n → ℝ`, including off the support of `f`, where the
notes assume only that `g` is nondecreasing and integrable. -/
theorem Affiliated.monotoneOn_condExp {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]
    {f g : (Fin n → ℝ) → ℝ} (hf : Affiliated f) (hf0 : 0 ≤ f) (hg : Monotone g)
    (hg0 : 0 ≤ g) (i : Fin n)
    (hnum : ∀ t : ℝ, FibreIntegrable μ (fun z => g (z[i ↦ t]) * f (z[i ↦ t])) (rivals i))
    (hden : ∀ t : ℝ, FibreIntegrable μ (fun z => f (z[i ↦ t])) (rivals i)) :
    MonotoneOn (fun t => condNumer μ f g i t / condDenom μ f i t)
      {t : ℝ | 0 < condDenom μ f i t} := by
  intro t ht t' ht' hle
  simp only [Set.mem_setOf_eq] at ht ht'
  rw [div_le_div_iff₀ ht ht']
  have h := hf.condNumer_mul_condDenom_le hf0 hg hg0 i hle (hnum t) (hden t') (hden t) (hnum t')
  linarith

/-- **Lemma 7.3**, division form: for `Affiliated f` with `0 ≤ f`, `Monotone g`, `0 ≤ g`,
positive `condDenom μ f i`, and the four slices `FibreIntegrable` along `rivals i` at
every height, `t ↦ condNumer μ f g i t / condDenom μ f i t` is nondecreasing.

`0 ≤ g` is required on all of `Fin n → ℝ`, including off the support of `f`, where the
notes assume only that `g` is nondecreasing and integrable. -/
theorem Affiliated.monotone_condExp {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]
    {f g : (Fin n → ℝ) → ℝ} (hf : Affiliated f) (hf0 : 0 ≤ f) (hg : Monotone g)
    (hg0 : 0 ≤ g) (i : Fin n) (hD : ∀ t : ℝ, 0 < condDenom μ f i t)
    (hnum : ∀ t : ℝ, FibreIntegrable μ (fun z => g (z[i ↦ t]) * f (z[i ↦ t])) (rivals i))
    (hden : ∀ t : ℝ, FibreIntegrable μ (fun z => f (z[i ↦ t])) (rivals i)) :
    Monotone fun t => condNumer μ f g i t / condDenom μ f i t := fun t t' hle =>
  hf.monotoneOn_condExp hf0 hg hg0 i hnum hden (hD t) (hD t') hle

/-- For `F` independent of coordinate `i`, `marginalList μ F (rivals i) x` does not depend
on `x`: `marginalList μ F (rivals i) x = marginalList μ F (rivals i) y`. In particular
`condNumer` and `condDenom` are unchanged if the base profile `0` is replaced by any
other profile. -/
theorem marginalList_rivals_congr {n : ℕ} {μ : Measure ℝ} {F : (Fin n → ℝ) → ℝ}
    (i : Fin n) (hF : ∀ (z : Fin n → ℝ) (s : ℝ), F (z[i ↦ s]) = F z)
    (x y : Fin n → ℝ) :
    marginalList μ F (rivals i) x = marginalList μ F (rivals i) y := by
  refine marginalList_congr_of_dependsOn (rivals i) (fun u v huv => ?_) x y
  have : u[i ↦ v i] = v := by
    funext k
    obtain rfl | hk := eq_or_ne k i
    · simp
    · simpa [Function.update_of_ne hk] using huv k ((mem_rivals_iff i k).2 hk)
  rw [← hF u (v i), this]

end Auction.Affiliation

end
