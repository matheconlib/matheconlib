module

public import Auctionlib.Auction.Affiliation.CondValue
public import Mathlib

/-! # The pivotal deviation-gain integral of Theorem 7.5

## Main results

* `Auction.Affiliation.cornerNumer_eq_zero_of_cornerDenom_eq_zero` : where the corner
  denominator vanishes so does the corner numerator, `cornerDenom μ E i j x y = 0 →
  cornerNumer μ E i j x y = 0`, under the pinned-slice integrability of both.
* `Auction.Affiliation.pivotalGain` : `pivotalGain μ E i j x a b
  = ∫ y in Set.Ioc a b, (cornerNumer μ E i j x y − bidII μ E i j y * cornerDenom μ E i j x y) ∂μ`,
  the corner-`j` deviation-gain integral on the pivot shell `(a, b]` with the integrand
  pinned at the true signal `x`.
* `Auction.Affiliation.Affiliated.pivotalGain_nonpos` : for `Affiliated E.f` and
  `x ≤ a`, together with the support-regularity hypothesis `hreg`,
  `pivotalGain μ E i j x a b ≤ 0`.
* `Auction.Affiliation.Affiliated.pivotalGain_nonneg` : for `Affiliated E.f` and `b ≤ x`,
  `0 ≤ pivotalGain μ E i j x a b`, with no support-regularity hypothesis needed.
* `Auction.Affiliation.Affiliated.bidII_pivotalOptimal` : the packaged statement that against
  the diagonal `bidII`, shells above the bidder's signal contribute nonpositive gain and
  shells below it contribute nonnegative gain.

`pivotalGain μ E i j x a b` is the corner-`j` deviation-gain integral from the notes' proof of
Theorem 7.5 (Milgrom–Weber 1982): the value-minus-price mass a bidder of signal `x` picks up on
the pivot shell `(a, b]` when the rivals bid the diagonal `bidII` and rival `j` is the top
rival. The two sign theorems say that against `bidII`, shells above the bidder's signal
contribute nonpositive gain and shells below it contribute nonnegative gain — the
pivotal/marginal optimality identity of the notes' proof, stated in corner form. Nothing in
this file — or anywhere in the library — defines a mechanism, an interim expected utility, or a
best response, so no statement here asserts that `pivotalGain` is the change in second-price
interim expected utility, and no Bayes–Nash equilibrium claim is made; the identification with
the game layer is not formalized.

The upward theorem `Affiliated.pivotalGain_nonpos` carries the support-regularity hypothesis
`hreg : ∀ y ∈ Set.Ioc a b, 0 < cornerDenom μ E i j x y → 0 < cornerDenom μ E i j y y`, and this
hypothesis is genuinely necessary: on the zone where `0 < cornerDenom μ E i j x y` while
`cornerDenom μ E i j y y = 0`, Lean forces `bidII μ E i j y = 0` (`div_zero`) and the integrand
degenerates to `cornerNumer μ E i j x y ≥ 0` — the wrong sign for the upward claim. Affiliation
does not exclude this zone, because the `x`-slice support of the corner density can strictly
exceed the diagonal support; so `hreg` is a caller's obligation, refutable if globalized, and is
kept explicit exactly as `Auction.Affiliation.CondValue` documents its refutable-if-globalized
hypotheses. The downward theorem needs no such hypothesis: there the degenerate zones all give
`cornerNumer μ E i j x y ≥ 0`, the right sign.
-/

@[expose] public section

open MeasureTheory

namespace Auction.Affiliation

/-! ### The zero-numerator transfer -/

/-- Where the corner denominator vanishes so does the corner numerator:
`cornerDenom μ E i j x y = 0 → cornerNumer μ E i j x y = 0`.

The integrability hypotheses are load-bearing: `marginalList` of a non-integrable stage is
junk, so the positivity transfer that drives the proof genuinely consumes them. The proof runs
by contradiction — a positive numerator forces, via `marginalList_pos_of_pos` applied to the
pointwise implication `0 < v · ρ → 0 < ρ`, a positive denominator. -/
theorem cornerNumer_eq_zero_of_cornerDenom_eq_zero {n : ℕ} {μ : Measure ℝ}
    {E : SignalValueEnv n} (i j : Fin n) (x y : ℝ)
    (hnum : FibreIntegrable μ
      (fun z => E.v i (Function.update (Function.update z i x) j y)
        * topDensity E.f i j (Function.update (Function.update z i x) j y))
      (otherRivals i j))
    (hden : FibreIntegrable μ
      (fun z => topDensity E.f i j (Function.update (Function.update z i x) j y))
      (otherRivals i j))
    (h : cornerDenom μ E i j x y = 0) : cornerNumer μ E i j x y = 0 := by
  by_contra hne
  have hpos : 0 < cornerNumer μ E i j x y :=
    lt_of_le_of_ne (cornerNumer_nonneg i j x y) (Ne.symm hne)
  have hf0 : (0 : (Fin n → ℝ) → ℝ) ≤ E.f := fun X => E.f_nonneg X
  have hGH : ∀ z : Fin n → ℝ,
      0 < E.v i (Function.update (Function.update z i x) j y)
          * topDensity E.f i j (Function.update (Function.update z i x) j y) →
      0 < topDensity E.f i j (Function.update (Function.update z i x) j y) := by
    intro z hz
    have hr0 := topDensity_nonneg hf0 i j (Function.update (Function.update z i x) j y)
    simp only [Pi.zero_apply] at hr0
    rcases hr0.eq_or_lt with heq | hlt
    · rw [← heq, mul_zero] at hz
      exact absurd hz (lt_irrefl _)
    · exact hlt
  have hden0 : 0 < cornerDenom μ E i j x y :=
    marginalList_pos_of_pos (otherRivals i j) (0 : Fin n → ℝ)
      (fun z => topDensity_nonneg hf0 i j (Function.update (Function.update z i x) j y))
      (fun z => mul_nonneg (E.v_nonneg i _)
        (topDensity_nonneg hf0 i j (Function.update (Function.update z i x) j y)))
      hGH hden hnum hpos
  rw [h] at hden0
  exact lt_irrefl _ hden0

/-! ### The pivotal deviation-gain integral -/

/-- `pivotalGain μ E i j x a b
= ∫ y in Set.Ioc a b, (cornerNumer μ E i j x y − bidII μ E i j y * cornerDenom μ E i j x y) ∂μ`:
the corner-`j` deviation-gain integral from the notes' proof of Theorem 7.5 (Milgrom–Weber
1982) — the value-minus-price mass a bidder of signal `x` picks up on the pivot shell `(a, b]`
when the rivals bid the diagonal `bidII` and rival `j` is the top rival. The integrand is
pinned at the true signal `x`; the endpoints `a`, `b` select the shell, so that the same
definition serves the upward shell `(x, x₂]` and the downward forgone shell `(x₂, x]`. Nothing
in this file — or anywhere in the library — defines a mechanism, an interim expected utility, or
a best response, so `pivotalGain` is not asserted to be the change in second-price interim
expected utility, and no Bayes–Nash equilibrium claim is made; the identification with the game
layer is not formalized. -/
noncomputable def pivotalGain {n : ℕ} (μ : Measure ℝ) (E : SignalValueEnv n) (i j : Fin n)
    (x a b : ℝ) : ℝ :=
  ∫ y in Set.Ioc a b,
    (cornerNumer μ E i j x y - bidII μ E i j y * cornerDenom μ E i j x y) ∂μ

/-! ### The two deviation signs -/

/-- For `Affiliated E.f` and `x ≤ a`, and under the support-regularity hypothesis `hreg`,
`pivotalGain μ E i j x a b ≤ 0`: against the diagonal `bidII`, a pivot shell strictly above the
bidder's signal contributes nonpositive deviation gain.

The hypothesis `hreg : ∀ y ∈ Set.Ioc a b, 0 < cornerDenom μ E i j x y → 0 < cornerDenom μ E i j
y y` is genuinely necessary and is not derivable from affiliation: on the zone where the
`x`-slice denominator is positive but the diagonal denominator vanishes, `bidII μ E i j y = 0`
by `div_zero` and the integrand degenerates to `cornerNumer μ E i j x y ≥ 0`, the wrong sign.
It is the caller's obligation, refutable if globalized, kept explicit in the house style of
`Auction.Affiliation.CondValue`. -/
theorem Affiliated.pivotalGain_nonpos {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]
    {E : SignalValueEnv n} (hf : Affiliated E.f) (i j : Fin n) {x a b : ℝ} (hxa : x ≤ a)
    (hreg : ∀ y ∈ Set.Ioc a b, 0 < cornerDenom μ E i j x y → 0 < cornerDenom μ E i j y y)
    (hnum : ∀ s t : ℝ, FibreIntegrable μ
      (fun z => E.v i (Function.update (Function.update z i s) j t)
        * topDensity E.f i j (Function.update (Function.update z i s) j t))
      (otherRivals i j))
    (hden : ∀ s t : ℝ, FibreIntegrable μ
      (fun z => topDensity E.f i j (Function.update (Function.update z i s) j t))
      (otherRivals i j)) :
    pivotalGain μ E i j x a b ≤ 0 := by
  refine setIntegral_nonpos measurableSet_Ioc (fun y hy => ?_)
  have hxy : x ≤ y := hxa.trans hy.1.le
  rcases eq_or_lt_of_le (cornerDenom_nonneg i j x y) with hd0 | hdpos
  · -- cornerDenom μ E i j x y = 0
    have hnum0 : cornerNumer μ E i j x y = 0 :=
      cornerNumer_eq_zero_of_cornerDenom_eq_zero i j x y (hnum x y) (hden x y) hd0.symm
    rw [hnum0, ← hd0, mul_zero, sub_zero]
  · -- 0 < cornerDenom μ E i j x y
    have hdyy : 0 < cornerDenom μ E i j y y := hreg y hy hdpos
    have mono := hf.monotoneOn_w_fst i j y (fun t => hnum t y) (fun t => hden t y)
    have hwle : w μ E i j x y ≤ bidII μ E i j y :=
      mono (Set.mem_setOf_eq ▸ hdpos) (Set.mem_setOf_eq ▸ hdyy) hxy
    have hcancel : w μ E i j x y * cornerDenom μ E i j x y = cornerNumer μ E i j x y := by
      rw [w]; exact div_mul_cancel₀ _ hdpos.ne'
    rw [show cornerNumer μ E i j x y - bidII μ E i j y * cornerDenom μ E i j x y
          = (w μ E i j x y - bidII μ E i j y) * cornerDenom μ E i j x y from by
        rw [sub_mul, hcancel]]
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hwle) (cornerDenom_nonneg i j x y)

/-- For `Affiliated E.f` and `b ≤ x`, `0 ≤ pivotalGain μ E i j x a b`: against the diagonal
`bidII`, a pivot shell strictly below the bidder's signal contributes nonnegative deviation
gain. No support-regularity hypothesis is needed downward — the degenerate zones all yield
`cornerNumer μ E i j x y ≥ 0`, the right sign. -/
theorem Affiliated.pivotalGain_nonneg {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]
    {E : SignalValueEnv n} (hf : Affiliated E.f) (i j : Fin n) {x a b : ℝ} (hbx : b ≤ x)
    (hnum : ∀ s t : ℝ, FibreIntegrable μ
      (fun z => E.v i (Function.update (Function.update z i s) j t)
        * topDensity E.f i j (Function.update (Function.update z i s) j t))
      (otherRivals i j))
    (hden : ∀ s t : ℝ, FibreIntegrable μ
      (fun z => topDensity E.f i j (Function.update (Function.update z i s) j t))
      (otherRivals i j)) :
    0 ≤ pivotalGain μ E i j x a b := by
  refine setIntegral_nonneg measurableSet_Ioc (fun y hy => ?_)
  have hyx : y ≤ x := hy.2.trans hbx
  rcases eq_or_lt_of_le (cornerDenom_nonneg i j x y) with hd0 | hdpos
  · -- cornerDenom μ E i j x y = 0
    rw [← hd0, mul_zero, sub_zero]
    exact cornerNumer_nonneg i j x y
  · rcases eq_or_lt_of_le (cornerDenom_nonneg i j y y) with hdyy0 | hdyy
    · -- cornerDenom μ E i j y y = 0, hence bidII μ E i j y = 0
      have hb0 : bidII μ E i j y = 0 := by rw [bidII, w, ← hdyy0, div_zero]
      rw [hb0, zero_mul, sub_zero]
      exact cornerNumer_nonneg i j x y
    · -- both denominators positive
      have mono := hf.monotoneOn_w_fst i j y (fun t => hnum t y) (fun t => hden t y)
      have hle : bidII μ E i j y ≤ w μ E i j x y :=
        mono (Set.mem_setOf_eq ▸ hdyy) (Set.mem_setOf_eq ▸ hdpos) hyx
      have hcancel : w μ E i j x y * cornerDenom μ E i j x y = cornerNumer μ E i j x y := by
        rw [w]; exact div_mul_cancel₀ _ hdpos.ne'
      rw [show cornerNumer μ E i j x y - bidII μ E i j y * cornerDenom μ E i j x y
            = (w μ E i j x y - bidII μ E i j y) * cornerDenom μ E i j x y from by
          rw [sub_mul, hcancel]]
      exact mul_nonneg (sub_nonneg.2 hle) (cornerDenom_nonneg i j x y)

/-! ### The packaged pivotal-optimality statement -/

/-- Against the diagonal `bidII`, shells above the bidder's signal contribute nonpositive gain
and shells below it contribute nonnegative gain: for every `x₂`, `x ≤ x₂` gives
`pivotalGain μ E i j x x x₂ ≤ 0` and `x₂ ≤ x` gives `0 ≤ pivotalGain μ E i j x x₂ x`. This is
the pivotal/marginal optimality identity of the notes' proof of Theorem 7.5 (Milgrom–Weber
1982), stated in corner form. It is named `bidII_pivotalOptimal`, not a "best response":
nothing here defines a mechanism, an interim expected utility, or a best response, so no
statement asserts that `pivotalGain` is the change in second-price interim expected utility, and
no Bayes–Nash equilibrium claim is made; the identification with the game layer is not
formalized. The upward half carries the caller's support-regularity obligation `hreg`, which is
refutable if globalized (see `Affiliated.pivotalGain_nonpos`). -/
theorem Affiliated.bidII_pivotalOptimal {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]
    {E : SignalValueEnv n} (hf : Affiliated E.f) (i j : Fin n) {x : ℝ}
    (hreg : ∀ y : ℝ, x < y → 0 < cornerDenom μ E i j x y → 0 < cornerDenom μ E i j y y)
    (hnum : ∀ s t : ℝ, FibreIntegrable μ
      (fun z => E.v i (Function.update (Function.update z i s) j t)
        * topDensity E.f i j (Function.update (Function.update z i s) j t))
      (otherRivals i j))
    (hden : ∀ s t : ℝ, FibreIntegrable μ
      (fun z => topDensity E.f i j (Function.update (Function.update z i s) j t))
      (otherRivals i j)) :
    ∀ x₂ : ℝ, (x ≤ x₂ → pivotalGain μ E i j x x x₂ ≤ 0)
      ∧ (x₂ ≤ x → 0 ≤ pivotalGain μ E i j x x₂ x) := by
  intro x₂
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · exact hf.pivotalGain_nonpos i j le_rfl
      (fun y hy hpos => hreg y hy.1 hpos) hnum hden
  · exact hf.pivotalGain_nonneg i j le_rfl hnum hden
