module

public import Auctionlib.Auction.Affiliation.CondValue
public import Auctionlib.ForMathlib.StochasticOrder
public import Mathlib

/-! # The linkage effect of the corner second-price payment

## Main results

* `Auction.Affiliation.Affiliated.cornerDenom_mul_cornerDenom_le` : for `Affiliated E.f`,
  `x ≤ x'` and `y ≤ y'`,
  `cornerDenom μ E i j x y' * cornerDenom μ E i j x' y
  ≤ cornerDenom μ E i j x y * cornerDenom μ E i j x' y'` — the TP2 (total positivity of
  order 2) cross-product inequality of the marginalized top-rival density, obtained from the
  four-functions relation of the four pinned corner slices.
* `Auction.Affiliation.Affiliated.monotoneOn_bidII` : the non-strict companion of
  `Affiliated.strictMonoOn_bidII`; `MonotoneOn (bidII μ E i j) S` on a set `S` on which
  `cornerDenom μ E i j` is positive at every pair of points.
* `Auction.Affiliation.marginalList_affiliated` : marginalization preserves affiliation —
  `Affiliated f`, `0 ≤ f` and `FibreIntegrable μ f l` imply `Affiliated (marginalList μ f l)`.
* `Auction.Affiliation.linkNumer`, `Auction.Affiliation.linkDenom`,
  `Auction.Affiliation.expectedPayII` : `linkNumer μ E i j x = ∫ y in Iic x, bidII y ·
  cornerDenom x y`, `linkDenom μ E i j x = ∫ y in Iic x, cornerDenom x y`, and their ratio
  `expectedPayII μ E i j x = linkNumer μ E i j x / linkDenom μ E i j x`.
* `Auction.Affiliation.Affiliated.linkage_signal_step` : the likelihood-ratio (MLR ⇒ FOSD)
  step over the winning event `{top rival ≤ x}`, cross-multiplied.
* `Auction.Affiliation.linkage_truncation_step` : the elementary widening step from
  `Iic x` to `Iic x'` against the single `x'`-slice, cross-multiplied.
* `Auction.Affiliation.Affiliated.expectedPayII_mono` : the linkage effect — for
  `Affiliated E.f` and `x ≤ x'`, `expectedPayII μ E i j x ≤ expectedPayII μ E i j x'`.
* `Auction.Affiliation.Affiliated.expectedPayII_le_bidII` : the winner's-margin corollary —
  `expectedPayII μ E i j x ≤ bidII μ E i j x`.

The pivotal-optimality integrals of the notes' proof of Theorem 7.5 and the linkage
monotonicity of the second-price winner's conditional expected payment from the proof of
Theorem 7.7 (Milgrom–Weber 1982), both in corner form. No mechanism, interim utility,
equilibrium, revenue, first-price format, or English format is defined or claimed;
Proposition 7.6 and the revenue ranking of Theorem 7.7 are not formalized.

`hbid : MonotoneOn (bidII μ E i j) (Set.Iic x')` is a genuine caller obligation, not an
automatic fact. `Affiliated.monotoneOn_bidII` discharges it on a set on which
`cornerDenom μ E i j` is positive at every pair of points — in practice a subset of the
signal box. Extending it across the region below the box, where `bidII ≡ 0` because
`cornerDenom ≡ 0` there (`E.f_support`), needs support bookkeeping that is not carried here;
so `hbid` on `Set.Iic x'` remains the caller's to supply. As in
`Auction.Affiliation.CondValue`, the unrestricted `Monotone (bidII μ E i j)` is not vacuous
but refutable, since `bidII μ E i j` returns to `0` past `E.x_hi`.
-/

@[expose] public section

open MeasureTheory

namespace Auction.Affiliation

/-! ### TP2 of the marginalized top-rival density -/

/-- For `Affiliated E.f`, `x ≤ x'` and `y ≤ y'`,
`cornerDenom μ E i j x y' * cornerDenom μ E i j x' y
≤ cornerDenom μ E i j x y * cornerDenom μ E i j x' y'`.

This is the two-coordinate total-positivity (TP2) inequality of the marginalized top-rival
density. It is obtained without ever forming the marginalized function: the four pinned
corner slices of `topDensity E.f i j` satisfy the four-functions relation pointwise (from
`affiliated_topDensity` applied at `z[i↦x][j↦y']` and `w[i↦x'][j↦y]`), and
`FourFunctionsLE.marginalList` pushes that relation through the iterated marginal along
`otherRivals i j`, evaluated at the base profile. -/
theorem Affiliated.cornerDenom_mul_cornerDenom_le {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]
    {E : SignalValueEnv n} (hf : Affiliated E.f) (i j : Fin n) {x x' y y' : ℝ}
    (hx : x ≤ x') (hy : y ≤ y')
    (hden : ∀ s t : ℝ, FibreIntegrable μ
      (fun z => topDensity E.f i j (Function.update (Function.update z i s) j t))
      (otherRivals i j)) :
    cornerDenom μ E i j x y' * cornerDenom μ E i j x' y
      ≤ cornerDenom μ E i j x y * cornerDenom μ E i j x' y' := by
  have hf0 : (0 : (Fin n → ℝ) → ℝ) ≤ E.f := fun X => E.f_nonneg X
  have haff : Affiliated (topDensity E.f i j) := affiliated_topDensity hf hf0 i j
  have hρ0 : (0 : (Fin n → ℝ) → ℝ) ≤ topDensity E.f i j := topDensity_nonneg hf0 i j
  have hFF : FourFunctionsLE
      (fun z => topDensity E.f i j (Function.update (Function.update z i x) j y'))
      (fun z => topDensity E.f i j (Function.update (Function.update z i x') j y))
      (fun z => topDensity E.f i j (Function.update (Function.update z i x) j y))
      (fun z => topDensity E.f i j (Function.update (Function.update z i x') j y')) := by
    intro z w
    have h := haff (Function.update (Function.update z i x) j y')
      (Function.update (Function.update w i x') j y)
    simp only [Function.update_sup_update, Function.update_inf_update,
      sup_of_le_right hx, sup_of_le_left hy, inf_of_le_left hx, inf_of_le_right hy] at h
    exact h.trans_eq (mul_comm _ _)
  have key := FourFunctionsLE.marginalList (otherRivals i j) hFF
    (fun z => hρ0 (Function.update (Function.update z i x) j y'))
    (fun z => hρ0 (Function.update (Function.update z i x') j y))
    (fun z => hρ0 (Function.update (Function.update z i x) j y))
    (fun z => hρ0 (Function.update (Function.update z i x') j y'))
    (hden x y') (hden x' y) (hden x y) (hden x' y')
  have hkey := key 0 0
  simpa only [cornerDenom, inf_idem, sup_idem] using hkey

/-! ### Non-strict monotonicity of the diagonal -/

/-- The non-strict companion of `Affiliated.strictMonoOn_bidII`: for `Affiliated E.f` and
`i ≠ j`, `bidII μ E i j` is nondecreasing on any set `S` on which `cornerDenom μ E i j` is
positive at every pair of points.

As with the strict version, the pair condition — rather than positivity on the diagonal —
is what the proof `w x x ≤ w x' x ≤ w x' x'` consumes, the middle step needing
`0 < cornerDenom μ E i j x' x` at the off-diagonal point.

`S` is a pairwise-positivity set, in practice inside the signal box. Extending `MonotoneOn`
to a set that meets the region where `bidII ≡ 0` needs support bookkeeping not carried here;
this lemma is the honest discharge of the caller obligation `hbid` on such a set only. -/
theorem Affiliated.monotoneOn_bidII {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]
    {E : SignalValueEnv n} (hf : Affiliated E.f) (i j : Fin n) (hij : i ≠ j) {S : Set ℝ}
    (hnum : ∀ s t : ℝ, FibreIntegrable μ
      (fun z => E.v i (Function.update (Function.update z i s) j t)
        * topDensity E.f i j (Function.update (Function.update z i s) j t))
      (otherRivals i j))
    (hden : ∀ s t : ℝ, FibreIntegrable μ
      (fun z => topDensity E.f i j (Function.update (Function.update z i s) j t))
      (otherRivals i j))
    (hS : ∀ ⦃s : ℝ⦄, s ∈ S → ∀ ⦃t : ℝ⦄, t ∈ S → 0 < cornerDenom μ E i j s t) :
    MonotoneOn (bidII μ E i j) S := by
  intro x hx x' hx' hxx
  have h₁ : w μ E i j x x ≤ w μ E i j x' x :=
    hf.monotoneOn_w_fst i j x (fun t => hnum t x) (fun t => hden t x) (hS hx hx) (hS hx' hx)
      hxx
  have h₂ : w μ E i j x' x ≤ w μ E i j x' x' :=
    hf.monotoneOn_w_snd i j hij x' (fun t => hnum x' t) (fun t => hden x' t) (hS hx' hx)
      (hS hx' hx') hxx
  simpa only [bidII] using h₁.trans h₂

/-! ### Marginalization preserves affiliation -/

/-- Marginalization preserves affiliation: if `Affiliated f`, `0 ≤ f` and `f` is
`FibreIntegrable` along `l`, then `Affiliated (marginalList μ f l)`. Not consumed on the
linkage critical path — that route goes through `FourFunctionsLE.marginalList` on the pinned
corner slices — but recorded here as the honest formalization of the fact, iterating
`marginal_affiliated`. -/
theorem marginalList_affiliated {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ] :
    ∀ (l : List (Fin n)) {f : (Fin n → ℝ) → ℝ}, Affiliated f → 0 ≤ f →
      FibreIntegrable μ f l → Affiliated (marginalList μ f l) := by
  intro l
  induction l with
  | nil => intro f hf _ _ u v; exact hf u v
  | cons j l ih =>
    intro f hf hf0 hFI
    exact ih (marginal_affiliated hf hf0 j hFI.1) (marginal_nonneg hf0 j) hFI.2

/-! ### The corner second-price payment -/

/-- `linkDenom μ E i j x = ∫ y in Set.Iic x, cornerDenom μ E i j x y ∂μ`: the mass of the
corner top-rival density over the winning event `{top rival ≤ x}`. -/
noncomputable def linkDenom {n : ℕ} (μ : Measure ℝ) (E : SignalValueEnv n) (i j : Fin n)
    (x : ℝ) : ℝ :=
  ∫ y in Set.Iic x, cornerDenom μ E i j x y ∂μ

/-- `linkNumer μ E i j x = ∫ y in Set.Iic x, bidII μ E i j y * cornerDenom μ E i j x y ∂μ`:
the price statistic `bidII` of the top rival integrated over the winning event. -/
noncomputable def linkNumer {n : ℕ} (μ : Measure ℝ) (E : SignalValueEnv n) (i j : Fin n)
    (x : ℝ) : ℝ :=
  ∫ y in Set.Iic x, bidII μ E i j y * cornerDenom μ E i j x y ∂μ

/-- `expectedPayII μ E i j x = linkNumer μ E i j x / linkDenom μ E i j x`.

In corner-`j` form, the winner's conditional expected payment in the second-price format:
the price statistic `bidII` of the top rival integrated over the winning event
`{top rival ≤ x}`. No statement here defines a mechanism, revenue, or the first-price or
English formats. -/
noncomputable def expectedPayII {n : ℕ} (μ : Measure ℝ) (E : SignalValueEnv n) (i j : Fin n)
    (x : ℝ) : ℝ :=
  linkNumer μ E i j x / linkDenom μ E i j x

/-! ### The signal step: likelihood-ratio comparison over the winning event -/

/-- The likelihood-ratio (MLR ⇒ FOSD) step, cross-multiplied over the winning event
`{top rival ≤ x}`: for `Affiliated E.f`, `x ≤ x'`, monotone diagonal `bidII` on `Set.Iic x'`
and the standard integrability data,
`(∫ y in Iic x, bidII y · cornerDenom x y) · (∫ y in Iic x, cornerDenom x' y)
≤ (∫ y in Iic x, bidII y · cornerDenom x' y) · (∫ y in Iic x, cornerDenom x y)`.

The two densities `cornerDenom μ E i j x ·` and `cornerDenom μ E i j x' ·` are in the
likelihood-ratio order by `Affiliated.cornerDenom_mul_cornerDenom_le`, and
`bidII μ E i j` — truncated at `x'` so as to be globally monotone, which agrees with `bidII`
on `Set.Iic x` — is the monotone test function; the inequality is
`integral_mul_integral_le_of_likelihoodRatioLE` over `μ.restrict (Set.Iic x)`. -/
theorem Affiliated.linkage_signal_step {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]
    {E : SignalValueEnv n} (hf : Affiliated E.f) (i j : Fin n) {x x' : ℝ} (hx : x ≤ x')
    (hbid : MonotoneOn (bidII μ E i j) (Set.Iic x'))
    (hden : ∀ s t : ℝ, FibreIntegrable μ
      (fun z => topDensity E.f i j (Function.update (Function.update z i s) j t))
      (otherRivals i j))
    (hp : IntegrableOn (fun y => cornerDenom μ E i j x y) (Set.Iic x) μ)
    (hq : IntegrableOn (fun y => cornerDenom μ E i j x' y) (Set.Iic x) μ)
    (hgp : IntegrableOn (fun y => bidII μ E i j y * cornerDenom μ E i j x y) (Set.Iic x) μ)
    (hgq : IntegrableOn (fun y => bidII μ E i j y * cornerDenom μ E i j x' y) (Set.Iic x) μ) :
    (∫ y in Set.Iic x, bidII μ E i j y * cornerDenom μ E i j x y ∂μ)
        * (∫ y in Set.Iic x, cornerDenom μ E i j x' y ∂μ)
      ≤ (∫ y in Set.Iic x, bidII μ E i j y * cornerDenom μ E i j x' y ∂μ)
        * (∫ y in Set.Iic x, cornerDenom μ E i j x y ∂μ) := by
  haveI : SigmaFinite (μ.restrict (Set.Iic x)) := inferInstance
  have hp0 : (0 : ℝ → ℝ) ≤ fun y => cornerDenom μ E i j x y :=
    fun y => cornerDenom_nonneg i j x y
  have hq0 : (0 : ℝ → ℝ) ≤ fun y => cornerDenom μ E i j x' y :=
    fun y => cornerDenom_nonneg i j x' y
  have hlr : LikelihoodRatioLE (fun y => cornerDenom μ E i j x y)
      (fun y => cornerDenom μ E i j x' y) := by
    intro a b hab
    show cornerDenom μ E i j x' a * cornerDenom μ E i j x b
      ≤ cornerDenom μ E i j x' b * cornerDenom μ E i j x a
    have h := hf.cornerDenom_mul_cornerDenom_le i j hx hab hden
    rw [mul_comm (cornerDenom μ E i j x' a), mul_comm (cornerDenom μ E i j x' b)]
    exact h
  have hg : Monotone (fun y => bidII μ E i j (min y x')) := by
    intro a b hab
    exact hbid (Set.mem_Iic.2 (min_le_right a x')) (Set.mem_Iic.2 (min_le_right b x'))
      (min_le_min hab le_rfl)
  have hgp' : Integrable (fun y => bidII μ E i j (min y x') * cornerDenom μ E i j x y)
      (μ.restrict (Set.Iic x)) :=
    hgp.congr_fun (fun y hy => by
      rw [min_eq_left (le_trans (Set.mem_Iic.1 hy) hx)]) measurableSet_Iic
  have hgq' : Integrable (fun y => bidII μ E i j (min y x') * cornerDenom μ E i j x' y)
      (μ.restrict (Set.Iic x)) :=
    hgq.congr_fun (fun y hy => by
      rw [min_eq_left (le_trans (Set.mem_Iic.1 hy) hx)]) measurableSet_Iic
  have key := integral_mul_integral_le_of_likelihoodRatioLE
    (μ := μ.restrict (Set.Iic x))
    (p := fun y => cornerDenom μ E i j x y) (q := fun y => cornerDenom μ E i j x' y)
    (g := fun y => bidII μ E i j (min y x')) hp0 hq0 hlr hg hp hq hgp' hgq'
  have e1 : ∫ y in Set.Iic x, bidII μ E i j (min y x') * cornerDenom μ E i j x y ∂μ
      = ∫ y in Set.Iic x, bidII μ E i j y * cornerDenom μ E i j x y ∂μ :=
    setIntegral_congr_fun measurableSet_Iic
      (fun y hy => by rw [min_eq_left (le_trans (Set.mem_Iic.1 hy) hx)])
  have e2 : ∫ y in Set.Iic x, bidII μ E i j (min y x') * cornerDenom μ E i j x' y ∂μ
      = ∫ y in Set.Iic x, bidII μ E i j y * cornerDenom μ E i j x' y ∂μ :=
    setIntegral_congr_fun measurableSet_Iic
      (fun y hy => by rw [min_eq_left (le_trans (Set.mem_Iic.1 hy) hx)])
  rw [e1, e2] at key
  exact key

/-! ### The truncation step: widening the winning event to `Iic x'` -/

/-- The elementary widening step, cross-multiplied: for `x ≤ x'`, monotone diagonal `bidII`
on `Set.Iic x'` and integrability of the `x'`-slice on `Set.Iic x'`,
`(∫ y in Iic x, bidII y · cornerDenom x' y) · (∫ y in Iic x', cornerDenom x' y)
≤ (∫ y in Iic x', bidII y · cornerDenom x' y) · (∫ y in Iic x, cornerDenom x' y)`.

Affiliation-free: split `Set.Iic x' = Set.Iic x ∪ Set.Ioc x x'`, and use that on the added
shell `Set.Ioc x x'` the diagonal `bidII` is at least its value at `x`, while on `Set.Iic x`
it is at most that value; the cross-multiplied inequality then follows from nonnegativity of
the two partial masses. -/
theorem linkage_truncation_step {n : ℕ} {μ : Measure ℝ} {E : SignalValueEnv n} (i j : Fin n)
    {x x' : ℝ} (hx : x ≤ x')
    (hbid : MonotoneOn (bidII μ E i j) (Set.Iic x'))
    (hq : IntegrableOn (fun y => cornerDenom μ E i j x' y) (Set.Iic x') μ)
    (hgq : IntegrableOn (fun y => bidII μ E i j y * cornerDenom μ E i j x' y)
      (Set.Iic x') μ) :
    (∫ y in Set.Iic x, bidII μ E i j y * cornerDenom μ E i j x' y ∂μ)
        * (∫ y in Set.Iic x', cornerDenom μ E i j x' y ∂μ)
      ≤ (∫ y in Set.Iic x', bidII μ E i j y * cornerDenom μ E i j x' y ∂μ)
        * (∫ y in Set.Iic x, cornerDenom μ E i j x' y ∂μ) := by
  have hdIic : IntegrableOn (fun y => cornerDenom μ E i j x' y) (Set.Iic x) μ :=
    hq.mono_set (Set.Iic_subset_Iic.2 hx)
  have hdIoc : IntegrableOn (fun y => cornerDenom μ E i j x' y) (Set.Ioc x x') μ :=
    hq.mono_set Set.Ioc_subset_Iic_self
  have hgIic : IntegrableOn (fun y => bidII μ E i j y * cornerDenom μ E i j x' y)
      (Set.Iic x) μ := hgq.mono_set (Set.Iic_subset_Iic.2 hx)
  have hgIoc : IntegrableOn (fun y => bidII μ E i j y * cornerDenom μ E i j x' y)
      (Set.Ioc x x') μ := hgq.mono_set Set.Ioc_subset_Iic_self
  have hunionD : ∫ y in Set.Iic x', cornerDenom μ E i j x' y ∂μ
      = (∫ y in Set.Iic x, cornerDenom μ E i j x' y ∂μ)
        + ∫ y in Set.Ioc x x', cornerDenom μ E i j x' y ∂μ := by
    rw [← Set.Iic_union_Ioc_eq_Iic hx,
      setIntegral_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc hdIic hdIoc]
  have hunionN : ∫ y in Set.Iic x', bidII μ E i j y * cornerDenom μ E i j x' y ∂μ
      = (∫ y in Set.Iic x, bidII μ E i j y * cornerDenom μ E i j x' y ∂μ)
        + ∫ y in Set.Ioc x x', bidII μ E i j y * cornerDenom μ E i j x' y ∂μ := by
    rw [← Set.Iic_union_Ioc_eq_Iic hx,
      setIntegral_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc hgIic hgIoc]
  have hD1 : 0 ≤ ∫ y in Set.Iic x, cornerDenom μ E i j x' y ∂μ :=
    setIntegral_nonneg measurableSet_Iic (fun y _ => cornerDenom_nonneg i j x' y)
  have hD2 : 0 ≤ ∫ y in Set.Ioc x x', cornerDenom μ E i j x' y ∂μ :=
    setIntegral_nonneg measurableSet_Ioc (fun y _ => cornerDenom_nonneg i j x' y)
  have hN1 : (∫ y in Set.Iic x, bidII μ E i j y * cornerDenom μ E i j x' y ∂μ)
      ≤ bidII μ E i j x * ∫ y in Set.Iic x, cornerDenom μ E i j x' y ∂μ := by
    calc (∫ y in Set.Iic x, bidII μ E i j y * cornerDenom μ E i j x' y ∂μ)
        ≤ ∫ y in Set.Iic x, bidII μ E i j x * cornerDenom μ E i j x' y ∂μ :=
          setIntegral_mono_on hgIic (hdIic.const_mul _) measurableSet_Iic
            (fun y hy => mul_le_mul_of_nonneg_right
              (hbid (Set.mem_Iic.2 (le_trans (Set.mem_Iic.1 hy) hx)) (Set.mem_Iic.2 hx)
                (Set.mem_Iic.1 hy))
              (cornerDenom_nonneg i j x' y))
      _ = bidII μ E i j x * ∫ y in Set.Iic x, cornerDenom μ E i j x' y ∂μ :=
          integral_const_mul _ _
  have hN2 : bidII μ E i j x * (∫ y in Set.Ioc x x', cornerDenom μ E i j x' y ∂μ)
      ≤ ∫ y in Set.Ioc x x', bidII μ E i j y * cornerDenom μ E i j x' y ∂μ := by
    calc bidII μ E i j x * (∫ y in Set.Ioc x x', cornerDenom μ E i j x' y ∂μ)
        = ∫ y in Set.Ioc x x', bidII μ E i j x * cornerDenom μ E i j x' y ∂μ :=
          (integral_const_mul _ _).symm
      _ ≤ ∫ y in Set.Ioc x x', bidII μ E i j y * cornerDenom μ E i j x' y ∂μ :=
          setIntegral_mono_on (hdIoc.const_mul _) hgIoc measurableSet_Ioc
            (fun y hy => mul_le_mul_of_nonneg_right
              (hbid (Set.mem_Iic.2 hx) (Set.mem_Iic.2 hy.2) hy.1.le)
              (cornerDenom_nonneg i j x' y))
  rw [hunionD, hunionN]
  nlinarith [mul_le_mul_of_nonneg_right hN1 hD2, mul_le_mul_of_nonneg_right hN2 hD1, hD1, hD2]

/-! ### The linkage effect -/

/-- The linkage effect: for `Affiliated E.f` and `x ≤ x'`, the winner's conditional expected
payment `expectedPayII μ E i j x` is nondecreasing in the winner's signal.

The second-price payment is statistically linked to the winner's signal, so the winner's
conditional expected payment is nondecreasing in that signal — while a first-price-style
payment depends on the own signal alone. No statement here defines a mechanism, revenue, or
the first-price or English formats: the revenue RANKING of Theorem 7.7 additionally requires
the symmetric first-price equilibrium of Proposition 7.6 (not formalized), a model of the
English button auction (not modeled), and the aggregation of interim payments into expected
revenue (not formalized). No revenue-ranking claim is made.

The chain is `expectedPayII μ E i j x ≤ A / B ≤ expectedPayII μ E i j x'`, where `A`, `B`
are the numerator and denominator of the mixed ratio against the `x'`-slice over
`Set.Iic x`: the first inequality is `linkage_signal_step`, the second is
`linkage_truncation_step`. The middle positivity `hB` is a genuine extra hypothesis — TP2
does not transfer pointwise positivity from the `x`-slice to the `x'`-slice. -/
theorem Affiliated.expectedPayII_mono {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]
    {E : SignalValueEnv n} (hf : Affiliated E.f) (i j : Fin n) {x x' : ℝ} (hx : x ≤ x')
    (hbid : MonotoneOn (bidII μ E i j) (Set.Iic x'))
    (hden : ∀ s t : ℝ, FibreIntegrable μ
      (fun z => topDensity E.f i j (Function.update (Function.update z i s) j t))
      (otherRivals i j))
    (hp : IntegrableOn (fun y => cornerDenom μ E i j x y) (Set.Iic x) μ)
    (hgp : IntegrableOn (fun y => bidII μ E i j y * cornerDenom μ E i j x y) (Set.Iic x) μ)
    (hq' : IntegrableOn (fun y => cornerDenom μ E i j x' y) (Set.Iic x') μ)
    (hgq' : IntegrableOn (fun y => bidII μ E i j y * cornerDenom μ E i j x' y)
      (Set.Iic x') μ)
    (hD : 0 < linkDenom μ E i j x)
    (hB : 0 < ∫ y in Set.Iic x, cornerDenom μ E i j x' y ∂μ)
    (hD' : 0 < linkDenom μ E i j x') :
    expectedPayII μ E i j x ≤ expectedPayII μ E i j x' := by
  have hsig := hf.linkage_signal_step i j hx hbid hden hp
    (hq'.mono_set (Set.Iic_subset_Iic.2 hx)) hgp (hgq'.mono_set (Set.Iic_subset_Iic.2 hx))
  have htrunc := linkage_truncation_step i j hx hbid hq' hgq'
  have h1 : expectedPayII μ E i j x
      ≤ (∫ y in Set.Iic x, bidII μ E i j y * cornerDenom μ E i j x' y ∂μ)
        / (∫ y in Set.Iic x, cornerDenom μ E i j x' y ∂μ) := by
    rw [expectedPayII, div_le_div_iff₀ hD hB, linkNumer, linkDenom]
    exact hsig
  have h2 : (∫ y in Set.Iic x, bidII μ E i j y * cornerDenom μ E i j x' y ∂μ)
        / (∫ y in Set.Iic x, cornerDenom μ E i j x' y ∂μ)
      ≤ expectedPayII μ E i j x' := by
    rw [expectedPayII, div_le_div_iff₀ hB hD', linkNumer, linkDenom]
    exact htrunc
  exact h1.trans h2

/-- The winner's-margin corollary: for `Affiliated E.f`, monotone diagonal `bidII` on
`Set.Iic x` and positive `linkDenom`, the winner's conditional expected payment never exceeds
their own diagonal bid, `expectedPayII μ E i j x ≤ bidII μ E i j x`. No comparison to any
first-price payment is asserted. -/
theorem Affiliated.expectedPayII_le_bidII {n : ℕ} {μ : Measure ℝ} {E : SignalValueEnv n}
    (i j : Fin n) {x : ℝ}
    (hbid : MonotoneOn (bidII μ E i j) (Set.Iic x))
    (hp : IntegrableOn (fun y => cornerDenom μ E i j x y) (Set.Iic x) μ)
    (hgp : IntegrableOn (fun y => bidII μ E i j y * cornerDenom μ E i j x y) (Set.Iic x) μ)
    (hD : 0 < linkDenom μ E i j x) :
    expectedPayII μ E i j x ≤ bidII μ E i j x := by
  rw [expectedPayII, div_le_iff₀ hD, linkNumer, linkDenom, ← integral_const_mul]
  exact setIntegral_mono_on hgp (hp.const_mul _) measurableSet_Iic
    (fun y hy => mul_le_mul_of_nonneg_right
      (hbid hy (Set.mem_Iic.2 le_rfl) (Set.mem_Iic.1 hy)) (cornerDenom_nonneg i j x y))

end Auction.Affiliation

end
