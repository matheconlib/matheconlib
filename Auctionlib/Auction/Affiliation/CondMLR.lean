module

public import Auctionlib.Auction.Affiliation.Basic
public import Auctionlib.ForMathlib.LatticeLikelihoodRatio
public import Auctionlib.ForMathlib.UpdateLattice
public import Mathlib

/-! # Affiliation and the likelihood-ratio order along one coordinate

## Main results

* `Affiliated.latticeLikelihoodRatioLE_slice`: for `Affiliated f`, `i : Fin n` and `t ≤ t'`,
  the pair of slices `p z = f (Function.update z i t)`, `q z = f (Function.update z i t')`
  satisfies `LatticeLikelihoodRatioLE p q`.
* `Affiliated.likelihoodRatioLE_slice₂`: for `t ≤ t'`, the one-dimensional slices
  `p y = f (Function.update (Function.update c i t) j y)` and
  `q y = f (Function.update (Function.update c i t') j y)` satisfy `LikelihoodRatioLE p q`.
* `Affiliated.integral_mul_integral_le`:
  `(∫ g(t,·)·f(t,·)) * (∫ f(t',·)) ≤ (∫ g(t',·)·f(t',·)) * (∫ f(t,·))` for `Affiliated f`,
  `0 ≤ f`, `Monotone g` and `t ≤ t'`, where `(s, ·)` abbreviates
  `fun y => Function.update (Function.update c i s) j y`.

Every coordinate other than `i` and `j` is frozen at the constant profile `c` throughout, so
the conditional expectation controlled by `Affiliated.integral_mul_integral_le` is
`t ↦ E[g(X) | X i = t, X k = c k for k ∉ {i, j}]`. This coincides with the notes'
Lemma 7.3 when `n = 2`; for `n > 2` it is the frozen-coordinate statement, not Lemma 7.3.
-/

@[expose] public section

open MeasureTheory

namespace Auction.Affiliation

/-- For `Affiliated f`, `i : Fin n` and `t ≤ t'`, the slices
`p z = f (Function.update z i t)` and `q z = f (Function.update z i t')` satisfy
`LatticeLikelihoodRatioLE p q`, i.e.
`f (Function.update z i t') * f (Function.update w i t) ≤
f (Function.update (z ⊔ w) i t') * f (Function.update (z ⊓ w) i t)`. -/
theorem Affiliated.latticeLikelihoodRatioLE_slice {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : Affiliated f) (i : Fin n) {t t' : ℝ} (ht : t ≤ t') :
    LatticeLikelihoodRatioLE (fun z => f (Function.update z i t))
      (fun z => f (Function.update z i t')) := by
  intro z w
  have h := hf (Function.update z i t') (Function.update w i t)
  rw [Function.update_sup_update, Function.update_inf_update, sup_of_le_left ht,
    inf_of_le_right ht] at h
  exact h

/-- For `Affiliated f`, indices `i j : Fin n`, a base profile `c` and `t ≤ t'`, the
one-dimensional slices `p y = f (Function.update (Function.update c i t) j y)` and
`q y = f (Function.update (Function.update c i t') j y)` satisfy `LikelihoodRatioLE p q`.
For `i = j` the outer update shadows the inner one, so `p = q` and the conclusion is a
tautology; the content is for `i ≠ j`. -/
theorem Affiliated.likelihoodRatioLE_slice₂ {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : Affiliated f) (i j : Fin n) (c : Fin n → ℝ) {t t' : ℝ} (ht : t ≤ t') :
    LikelihoodRatioLE (fun y => f (Function.update (Function.update c i t) j y))
      (fun y => f (Function.update (Function.update c i t') j y)) := by
  intro y y' hy
  have h := hf (Function.update (Function.update c i t') j y)
    (Function.update (Function.update c i t) j y')
  rw [Function.update_sup_update, Function.update_inf_update, Function.update_sup_update,
    Function.update_inf_update, sup_idem, inf_idem, sup_of_le_left ht, inf_of_le_right ht,
    sup_of_le_right hy, inf_of_le_left hy] at h
  exact h

/-- For `Affiliated f` with `0 ≤ f`, monotone `g`, indices `i j : Fin n`, base profile `c`,
`t ≤ t'` and `u s y = Function.update (Function.update c i s) j y`,
`(∫ y, g (u t y) * f (u t y) ∂μ) * (∫ y, f (u t' y) ∂μ) ≤
(∫ y, g (u t' y) * f (u t' y) ∂μ) * (∫ y, f (u t y) ∂μ)`.

Dividing by the two `f`-integrals, this says that
`t ↦ E[g(X) | X i = t, X k = c k for k ∉ {i, j}]` is nondecreasing: coordinate `j` is
integrated against `μ`, and every coordinate other than `i` and `j` is frozen at `c`. It
coincides with the notes' Lemma 7.3 when `n = 2`.

For `i = j` the outer update shadows the inner one, so the two sides agree and the
conclusion is a tautology; the content is for `i ≠ j`. -/
theorem Affiliated.integral_mul_integral_le {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]
    {f g : (Fin n → ℝ) → ℝ} (hf : Affiliated f) (hf0 : 0 ≤ f) (hg : Monotone g)
    (i j : Fin n) (c : Fin n → ℝ) {t t' : ℝ} (ht : t ≤ t')
    (hpi : Integrable (fun y => f (Function.update (Function.update c i t) j y)) μ)
    (hqi : Integrable (fun y => f (Function.update (Function.update c i t') j y)) μ)
    (hgpi : Integrable (fun y => g (Function.update (Function.update c i t) j y) *
      f (Function.update (Function.update c i t) j y)) μ)
    (hgqi : Integrable (fun y => g (Function.update (Function.update c i t) j y) *
      f (Function.update (Function.update c i t') j y)) μ)
    (hgqi' : Integrable (fun y => g (Function.update (Function.update c i t') j y) *
      f (Function.update (Function.update c i t') j y)) μ) :
    (∫ y, g (Function.update (Function.update c i t) j y) *
        f (Function.update (Function.update c i t) j y) ∂μ) *
      (∫ y, f (Function.update (Function.update c i t') j y) ∂μ) ≤
    (∫ y, g (Function.update (Function.update c i t') j y) *
        f (Function.update (Function.update c i t') j y) ∂μ) *
      (∫ y, f (Function.update (Function.update c i t) j y) ∂μ) := by
  have hp0 : (0 : ℝ → ℝ) ≤ fun y => f (Function.update (Function.update c i t) j y) :=
    fun y => hf0 _
  have hq0 : (0 : ℝ → ℝ) ≤ fun y => f (Function.update (Function.update c i t') j y) :=
    fun y => hf0 _
  have hgmono : Monotone fun y => g (Function.update (Function.update c i t) j y) :=
    hg.comp Function.update_mono
  have key := integral_mul_integral_le_of_likelihoodRatioLE (μ := μ) hp0 hq0
    (hf.likelihoodRatioLE_slice₂ i j c ht) hgmono hpi hqi hgpi hgqi
  have hstep : (∫ y, g (Function.update (Function.update c i t) j y) *
        f (Function.update (Function.update c i t') j y) ∂μ) ≤
      ∫ y, g (Function.update (Function.update c i t') j y) *
        f (Function.update (Function.update c i t') j y) ∂μ :=
    integral_mono hgqi hgqi' fun y =>
      mul_le_mul_of_nonneg_right (hg (Function.update_update_mono c i j y ht)) (hf0 _)
  have hpint : 0 ≤ ∫ y, f (Function.update (Function.update c i t) j y) ∂μ :=
    integral_nonneg fun y => hf0 _
  exact key.trans (mul_le_mul_of_nonneg_right hstep hpint)

end Auction.Affiliation

end
