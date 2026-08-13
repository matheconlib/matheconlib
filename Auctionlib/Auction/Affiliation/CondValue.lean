module

public import Auctionlib.Auction.Affiliation.CondExpGeneral
public import Auctionlib.Auction.Affiliation.Sublattice
public import Mathlib

/-! # The corner conditional value and its diagonal

## Main results

* `Auction.Affiliation.otherRivals` : `otherRivals i j = (rivals i).erase j`, with
  `Auction.Affiliation.nodup_rivals` and
  `Auction.Affiliation.mem_otherRivals_iff : k ∈ otherRivals i j ↔ k ≠ i ∧ k ≠ j`.
* `Auction.Affiliation.mem_maxAt_update_update_iff` :
  `Function.update (Function.update z i x) j y ∈ maxAt i j ↔ ∀ k, k ≠ i → k ≠ j → z k ≤ y`.
* `Auction.Affiliation.cornerDenom`, `Auction.Affiliation.cornerNumer` : the iterated
  marginals of `fun z => topDensity E.f i j (z[i↦x][j↦y])` and of
  `fun z => E.v i (z[i↦x][j↦y]) * topDensity E.f i j (z[i↦x][j↦y])` along
  `otherRivals i j`, evaluated at the base profile `0`.
* `Auction.Affiliation.w` : `w μ E i j x y = cornerNumer μ E i j x y / cornerDenom μ E i j x y`.
* `Auction.Affiliation.bidII` : `bidII μ E i j x = w μ E i j x x`.
* `Auction.Affiliation.marginalList_corner_congr` : `marginalList μ F (otherRivals i j)` is
  constant for `F` independent of coordinates `i` and `j`.
* `Auction.Affiliation.cornerDenom_base_indep`, `Auction.Affiliation.cornerNumer_base_indep` :
  `cornerDenom` and `cornerNumer` are unchanged if the base profile `0` is replaced by any
  other profile.
* `Auction.Affiliation.cornerDenom_nonneg`, `Auction.Affiliation.cornerNumer_nonneg` :
  `0 ≤ cornerDenom μ E i j x y` and `0 ≤ cornerNumer μ E i j x y`.
* `Auction.Affiliation.Affiliated.cornerNumer_mul_cornerDenom_le_fst` : for `Affiliated E.f`
  and `x ≤ x'`, `cornerNumer μ E i j x y * cornerDenom μ E i j x' y
  ≤ cornerDenom μ E i j x y * cornerNumer μ E i j x' y`.
* `Auction.Affiliation.Affiliated.monotoneOn_w_fst` :
  `MonotoneOn (fun x => w μ E i j x y) {x | 0 < cornerDenom μ E i j x y}`.
* `Auction.Affiliation.Affiliated.cornerNumer_mul_cornerDenom_le_snd` : for `Affiliated E.f`,
  `i ≠ j` and `y ≤ y'`, `cornerNumer μ E i j x y * cornerDenom μ E i j x y'
  ≤ cornerDenom μ E i j x y * cornerNumer μ E i j x y'`.
* `Auction.Affiliation.Affiliated.monotoneOn_w_snd` :
  `MonotoneOn (fun y => w μ E i j x y) {y | 0 < cornerDenom μ E i j x y}`.
* `Auction.Affiliation.crossNumer` : the iterated marginal of
  `fun z => E.v i (z[i↦x][j↦y]) * topDensity E.f i j (z[i↦x'][j↦y])`.
* `Auction.Affiliation.ownEffect` : the iterated marginal of
  `fun z => (E.v i (z[i↦x'][j↦y]) - E.v i (z[i↦x][j↦y])) * topDensity E.f i j (z[i↦x'][j↦y])`.
* `Auction.Affiliation.HasStrictOwnEffect` :
  `∀ x x' ∈ S, x < x' → 0 < ownEffect μ E i j x x' y`.
* `Auction.Affiliation.cornerNumer_eq_crossNumer_add_ownEffect` :
  `cornerNumer μ E i j x' y = crossNumer μ E i j x x' y + ownEffect μ E i j x x' y`.
* `Auction.Affiliation.Affiliated.cornerNumer_mul_cornerDenom_le_cross` : for
  `Affiliated E.f` and `x ≤ x'`, `cornerNumer μ E i j x y * cornerDenom μ E i j x' y
  ≤ cornerDenom μ E i j x y * crossNumer μ E i j x x' y`.
* `Auction.Affiliation.Affiliated.strictMonoOn_w_fst` : under
  `HasStrictOwnEffect μ E i j y T` and `0 < cornerDenom μ E i j t y` for `t ∈ T`,
  `StrictMonoOn (fun x => w μ E i j x y) T`, with
  `Auction.Affiliation.Affiliated.strictMonoOn_w_fst_cornerDenom_pos` the case
  `T = {x | 0 < cornerDenom μ E i j x y}`.
* `Auction.Affiliation.Affiliated.strictMonoOn_bidII` : under
  `HasStrictOwnEffect μ E i j y S` for every `y ∈ S` and `0 < cornerDenom μ E i j s t` for
  all `s, t ∈ S`, `StrictMonoOn (bidII μ E i j) S`.
* `Auction.Affiliation.hasStrictOwnEffect_of_v_strictMono` : `HasStrictOwnEffect μ E i j y S`
  from `0 < cornerDenom μ E i j t y` for `t ∈ S` and integrability alone — the strictness
  itself comes from `SignalValueEnv.v_strictMono_own`.
* `Auction.Affiliation.Affiliated.strictMonoOn_w_fst_of_v_strictMono`,
  `Auction.Affiliation.Affiliated.strictMonoOn_w_fst_cornerDenom_pos_of_v_strictMono`,
  `Auction.Affiliation.Affiliated.strictMonoOn_bidII_of_v_strictMono` : the strict
  monotonicity results with `HasStrictOwnEffect` discharged, so that the caller supplies
  only `i ≠ j`, positivity of `cornerDenom`, and integrability.

`w μ E i j x y` is the ratio of the two iterated marginals of the density
`topDensity E.f i j`, in which coordinate `i` is pinned at `x`, coordinate `j` is pinned at
`y`, and the sublattice indicator of `maxAt i j` confines every remaining coordinate to
`(-∞, y]`. It is therefore the conditional value of bidder `i` *given that rival `j`
attains the maximum of the rival signals*: one corner of the `n − 1` corners of the joint
density of `(Xᵢ, maxₖ≠ᵢ Xₖ)`. No theorem here identifies `w μ E i j x y` with
`E[Vᵢ | Xᵢ = x, Y = y]`; that identification requires summing the corners and holds only
under a symmetry hypothesis, which is not formalized in this file. As in
`Auction.Affiliation.CondExpGeneral`, nothing here refers to `MeasureTheory.condExp` or to a
disintegration kernel, and `w` is a functional of the chosen density representative `E.f`
rather than of the law: altering `E.f` on a null set changes `w` pointwise, exactly as
`ForMathlib/StochasticOrder.lean` records for `LikelihoodRatioLE`.

`HasStrictOwnEffect` is a hypothesis of `Affiliated.strictMonoOn_w_fst` and
`Affiliated.strictMonoOn_bidII`, but it is *not* an extra assumption on the model:
`hasStrictOwnEffect_of_v_strictMono` derives it from `SignalValueEnv.v_strictMono_own`
together with positivity of `cornerDenom` and the integrability hypotheses. The
own-signal increment `E.v i (z[i↦x'][j↦y]) − E.v i (z[i↦x][j↦y])` is strictly positive at
every `z` when `x < x'` and `i ≠ j`, the weight `topDensity E.f i j (z[i↦x'][j↦y])` is
nonnegative, and `0 < cornerDenom μ E i j x' y` says the iterated marginal of that weight
alone is positive; `marginalList_lt_of_lt` turns this into strict positivity of the iterated
marginal of the product. The `HasStrictOwnEffect`-parameterised statements are kept because
they isolate exactly what the affiliation argument uses.

Every monotonicity result is stated in `MonotoneOn`/`StrictMonoOn` form over a set on which
`cornerDenom μ E i j` is positive. `E.f_support` makes `cornerDenom μ E i j x y = 0` whenever
`x` or `y` lies outside `Set.Icc E.x_lo E.x_hi`; the same argument makes
`cornerNumer μ E i j x y = 0` there, so `w μ E i j x y = 0 / 0 = 0` off the signal box. Hence
no `SignalValueEnv` has a globally positive `cornerDenom` or a globally strict `ownEffect`,
and the unrestricted `Monotone`/`StrictMono` forms are not vacuous but **refutable**: their
hypotheses are satisfiable, and the conclusions fail. `StrictMono (fun x => w μ E i j x y)`
fails outright, since `w μ E i j · y` is constantly `0` on `(E.x_hi, ∞)`; and
`Monotone (fun x => w μ E i j x y)` fails for every environment whose `w μ E i j · y` is
positive somewhere, since the value must drop back to `0` past `E.x_hi`. This is why the
statements are restricted rather than merely stated globally.

**`n = 2` degenerates.** At `n = 2` this whole layer carries no integral. `otherRivals i j`
is empty, so `marginalList μ · (otherRivals i j)` is the identity (`marginalList μ F [] = F`)
and the `FibreIntegrable` hypotheses of the statements here are literally `True`
(`FibreIntegrable μ F [] = True`); and `maxAt i j` is the whole space, so
`topDensity E.f i j = E.f`. `cornerDenom` and `cornerNumer` are then plain evaluations of
the density and of `v * density` at the pinned profile, with no marginalization at all.
`n ≥ 3` is the first informative case. See `Auction.Affiliation.Examples.otherRivals_two`
and `Auction.Affiliation.Examples.maxAt_two` for the collapse, and the `n = 3` / `n = 4`
instantiations there for the cases that exercise the marginalization.
-/

@[expose] public section

open MeasureTheory

namespace Auction.Affiliation

/-! ### The rivals other than a designated one -/

/-- `otherRivals i j = (rivals i).erase j`, the coordinates other than `i` and `j`. -/
def otherRivals {n : ℕ} (i j : Fin n) : List (Fin n) := (rivals i).erase j

/-- `(rivals i).Nodup`. -/
theorem nodup_rivals {n : ℕ} (i : Fin n) : (rivals i).Nodup :=
  Finset.sort_nodup _ _

/-- `k ∈ otherRivals i j ↔ k ≠ i ∧ k ≠ j`. -/
theorem mem_otherRivals_iff {n : ℕ} (i j k : Fin n) :
    k ∈ otherRivals i j ↔ k ≠ i ∧ k ≠ j := by
  rw [otherRivals, (nodup_rivals i).mem_erase_iff, mem_rivals_iff]
  tauto

/-! ### `Function.update` bookkeeping -/

private theorem monotone_update_profile {n : ℕ} (k : Fin n) (c : ℝ) :
    Monotone fun z : Fin n → ℝ => Function.update z k c := by
  intro a b hab m
  obtain rfl | hm := eq_or_ne m k
  · simp
  · simpa only [Function.update_of_ne hm] using hab m

private theorem upd_i_idem {n : ℕ} (z : Fin n → ℝ) (i j : Fin n) (s x y : ℝ) :
    Function.update (Function.update (Function.update z i s) i x) j y
      = Function.update (Function.update z i x) j y := by
  rw [Function.update_idem]

private theorem upd_j_absorb {n : ℕ} {i j : Fin n} (hij : i ≠ j) (z : Fin n → ℝ)
    (s x y : ℝ) :
    Function.update (Function.update (Function.update z j s) i x) j y
      = Function.update (Function.update z i x) j y := by
  rw [Function.update_comm (Ne.symm hij) s x z, Function.update_idem]

/-- `Function.update (Function.update z i x) j y ∈ maxAt i j` if and only if
`z k ≤ y` for every `k ≠ i`, `k ≠ j`: pinning coordinate `j` at `y` turns the sublattice
indicator of `maxAt i j` into the indicator of the lower box `{z | ∀ k ≠ i, k ≠ j, z k ≤ y}`.

No proof below consumes this; it is exported as the interpretation lemma for `cornerDenom` and
`cornerNumer`, which is what licenses reading them as *corner* marginals of the joint law of
`(Xᵢ, maxₖ≠ᵢ Xₖ)`, and it is the step any explicit evaluation of those marginals (rewriting the
indicator as a product of one-dimensional cutoffs at `y`) has to start from. -/
theorem mem_maxAt_update_update_iff {n : ℕ} (i j : Fin n) (z : Fin n → ℝ) (x y : ℝ) :
    Function.update (Function.update z i x) j y ∈ maxAt i j
      ↔ ∀ k, k ≠ i → k ≠ j → z k ≤ y := by
  simp only [mem_maxAt_iff, Function.update_self]
  constructor
  · intro h k hki hkj
    have hk := h k hki hkj
    rwa [Function.update_of_ne hkj, Function.update_of_ne hki] at hk
  · intro h k hki hkj
    rw [Function.update_of_ne hkj, Function.update_of_ne hki]
    exact h k hki hkj

/-! ### The corner conditional value -/

/-- `cornerDenom μ E i j x y
= marginalList μ (fun z => topDensity E.f i j (z[i↦x][j↦y])) (otherRivals i j) 0`. -/
noncomputable def cornerDenom {n : ℕ} (μ : Measure ℝ) (E : SignalValueEnv n) (i j : Fin n)
    (x y : ℝ) : ℝ :=
  marginalList μ
    (fun z => topDensity E.f i j (Function.update (Function.update z i x) j y))
    (otherRivals i j) 0

/-- `cornerNumer μ E i j x y
= marginalList μ (fun z => E.v i (z[i↦x][j↦y]) * topDensity E.f i j (z[i↦x][j↦y]))
(otherRivals i j) 0`. -/
noncomputable def cornerNumer {n : ℕ} (μ : Measure ℝ) (E : SignalValueEnv n) (i j : Fin n)
    (x y : ℝ) : ℝ :=
  marginalList μ
    (fun z => E.v i (Function.update (Function.update z i x) j y)
      * topDensity E.f i j (Function.update (Function.update z i x) j y))
    (otherRivals i j) 0

/-- `w μ E i j x y = cornerNumer μ E i j x y / cornerDenom μ E i j x y`: the conditional
value of bidder `i` at own signal `x` given that rival `j` attains the value `y` and is the
largest of the rival signals. It is one corner of the joint density of
`(Xᵢ, maxₖ≠ᵢ Xₖ)`, not the full conditional expectation `E[Vᵢ | Xᵢ = x, Y = y]`. -/
noncomputable def w {n : ℕ} (μ : Measure ℝ) (E : SignalValueEnv n) (i j : Fin n)
    (x y : ℝ) : ℝ :=
  cornerNumer μ E i j x y / cornerDenom μ E i j x y

/-- `bidII μ E i j x = w μ E i j x x`, the diagonal of the corner conditional value.

**`bidII` is discontinuous at the signal floor as soon as `n ≥ 3`.** The corner denominator
`cornerDenom μ E i j x x` marginalizes the `n − 2` coordinates in `otherRivals i j` against
the `maxAt i j` indicator, which confines each of them to `(-∞, x]`; at `x = E.x_lo` the
density's support meets that region in a set the marginalizing measure gives no mass, so
the denominator is `0` and `w = 0 / 0 = 0` — division by zero returns `0` in Lean. At every
interior point the same ratio is the bidder's own value. The worked instance is
`Auction.Affiliation.Examples.bidII_three_at_zero`, `bidII volume (Ebox 3) 0 1 0 = 0`,
against `Auction.Affiliation.Examples.bidII_three`, `bidII volume (Ebox 3) 0 1 x = exp x`
for `0 < x ≤ 1`: a jump of size `exp E.x_lo = 1` at the left endpoint, not a removable
artefact. At `n = 2` there is nothing to marginalize and the phenomenon is absent
(`Auction.Affiliation.Examples.bidII_tri_two` is `exp x` on the whole closed box). This is
why the results below are stated on sets where `cornerDenom` is positive. -/
noncomputable def bidII {n : ℕ} (μ : Measure ℝ) (E : SignalValueEnv n) (i j : Fin n)
    (x : ℝ) : ℝ :=
  w μ E i j x x

/-! ### Independence of the base profile -/

/-- For `F` independent of coordinates `i` and `j`, `marginalList μ F (otherRivals i j) x`
does not depend on `x`. -/
theorem marginalList_corner_congr {n : ℕ} {μ : Measure ℝ} {F : (Fin n → ℝ) → ℝ}
    (i j : Fin n)
    (hFi : ∀ (z : Fin n → ℝ) (s : ℝ), F (Function.update z i s) = F z)
    (hFj : ∀ (z : Fin n → ℝ) (s : ℝ), F (Function.update z j s) = F z)
    (x y : Fin n → ℝ) :
    marginalList μ F (otherRivals i j) x = marginalList μ F (otherRivals i j) y := by
  refine marginalList_congr_of_dependsOn (otherRivals i j) (fun u v huv => ?_) x y
  have key : Function.update (Function.update u i (v i)) j (v j) = v := by
    funext k
    obtain rfl | hkj := eq_or_ne k j
    · simp
    · rw [Function.update_of_ne hkj]
      obtain rfl | hki := eq_or_ne k i
      · simp
      · rw [Function.update_of_ne hki]
        exact huv k ((mem_otherRivals_iff i j k).2 ⟨hki, hkj⟩)
  rw [← hFi u (v i), ← hFj (Function.update u i (v i)) (v j), key]

/-- `cornerDenom` is unchanged if the base profile `0` is replaced by any other profile. -/
theorem cornerDenom_base_indep {n : ℕ} {μ : Measure ℝ} {E : SignalValueEnv n} {i j : Fin n}
    (hij : i ≠ j) (x y : ℝ) (b : Fin n → ℝ) :
    marginalList μ
        (fun z => topDensity E.f i j (Function.update (Function.update z i x) j y))
        (otherRivals i j) b
      = cornerDenom μ E i j x y :=
  marginalList_corner_congr i j (fun _ _ => by simp only [upd_i_idem])
    (fun _ _ => by simp only [upd_j_absorb hij]) b 0

/-- `cornerNumer` is unchanged if the base profile `0` is replaced by any other profile. -/
theorem cornerNumer_base_indep {n : ℕ} {μ : Measure ℝ} {E : SignalValueEnv n} {i j : Fin n}
    (hij : i ≠ j) (x y : ℝ) (b : Fin n → ℝ) :
    marginalList μ
        (fun z => E.v i (Function.update (Function.update z i x) j y)
          * topDensity E.f i j (Function.update (Function.update z i x) j y))
        (otherRivals i j) b
      = cornerNumer μ E i j x y :=
  marginalList_corner_congr i j (fun _ _ => by simp only [upd_i_idem])
    (fun _ _ => by simp only [upd_j_absorb hij]) b 0

/-! ### Nonnegativity -/

/-- `0 ≤ cornerDenom μ E i j x y`. -/
theorem cornerDenom_nonneg {n : ℕ} {μ : Measure ℝ} {E : SignalValueEnv n} (i j : Fin n)
    (x y : ℝ) : 0 ≤ cornerDenom μ E i j x y := by
  simp only [cornerDenom]
  exact marginalList_nonneg (otherRivals i j)
    (F := fun z => topDensity E.f i j (Function.update (Function.update z i x) j y))
    (fun z => topDensity_nonneg (fun X => E.f_nonneg X) i j
      (Function.update (Function.update z i x) j y)) 0

/-- `0 ≤ cornerNumer μ E i j x y`. -/
theorem cornerNumer_nonneg {n : ℕ} {μ : Measure ℝ} {E : SignalValueEnv n} (i j : Fin n)
    (x y : ℝ) : 0 ≤ cornerNumer μ E i j x y := by
  simp only [cornerNumer]
  exact marginalList_nonneg (otherRivals i j)
    (F := fun z => E.v i (Function.update (Function.update z i x) j y)
      * topDensity E.f i j (Function.update (Function.update z i x) j y))
    (fun z => mul_nonneg (E.v_nonneg i _)
      (topDensity_nonneg (fun X => E.f_nonneg X) i j
        (Function.update (Function.update z i x) j y))) 0

/-! ### Monotonicity in the own signal -/

/-- For `Affiliated E.f` and `x ≤ x'`,
`cornerNumer μ E i j x y * cornerDenom μ E i j x' y
≤ cornerDenom μ E i j x y * cornerNumer μ E i j x' y`. -/
theorem Affiliated.cornerNumer_mul_cornerDenom_le_fst {n : ℕ} {μ : Measure ℝ}
    [SigmaFinite μ] {E : SignalValueEnv n} (hf : Affiliated E.f) (i j : Fin n) (y : ℝ)
    {x x' : ℝ} (hx : x ≤ x')
    (hnum : ∀ t : ℝ, FibreIntegrable μ
      (fun z => E.v i (Function.update (Function.update z i t) j y)
        * topDensity E.f i j (Function.update (Function.update z i t) j y))
      (otherRivals i j))
    (hden : ∀ t : ℝ, FibreIntegrable μ
      (fun z => topDensity E.f i j (Function.update (Function.update z i t) j y))
      (otherRivals i j)) :
    cornerNumer μ E i j x y * cornerDenom μ E i j x' y
      ≤ cornerDenom μ E i j x y * cornerNumer μ E i j x' y := by
  have hf0 : (0 : (Fin n → ℝ) → ℝ) ≤ E.f := fun X => E.f_nonneg X
  have haff : Affiliated fun z : Fin n → ℝ =>
      topDensity E.f i j (Function.update z j y) :=
    (affiliated_topDensity hf hf0 i j).update_slice j y
  have hd0 : (0 : (Fin n → ℝ) → ℝ)
      ≤ fun z : Fin n → ℝ => topDensity E.f i j (Function.update z j y) :=
    fun z => topDensity_nonneg hf0 i j (Function.update z j y)
  have hgm : Monotone fun z : Fin n → ℝ => E.v i (Function.update z j y) :=
    (E.v_mono i).comp (monotone_update_profile j y)
  have hg0 : (0 : (Fin n → ℝ) → ℝ)
      ≤ fun z : Fin n → ℝ => E.v i (Function.update z j y) :=
    fun _ => E.v_nonneg i _
  have key := haff.marginalList_mul_le hd0 hgm hg0 i (otherRivals i j) hx
    (hnum x) (hden x') (hden x) (hnum x') 0
  simpa only [cornerNumer, cornerDenom] using key

/-- For `Affiliated E.f`, `x ↦ w μ E i j x y` is nondecreasing on
`{x | 0 < cornerDenom μ E i j x y}`. -/
theorem Affiliated.monotoneOn_w_fst {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]
    {E : SignalValueEnv n} (hf : Affiliated E.f) (i j : Fin n) (y : ℝ)
    (hnum : ∀ t : ℝ, FibreIntegrable μ
      (fun z => E.v i (Function.update (Function.update z i t) j y)
        * topDensity E.f i j (Function.update (Function.update z i t) j y))
      (otherRivals i j))
    (hden : ∀ t : ℝ, FibreIntegrable μ
      (fun z => topDensity E.f i j (Function.update (Function.update z i t) j y))
      (otherRivals i j)) :
    MonotoneOn (fun x => w μ E i j x y) {x : ℝ | 0 < cornerDenom μ E i j x y} := by
  intro x hx x' hx' hxx
  simp only [Set.mem_setOf_eq] at hx hx'
  simp only [w]
  rw [div_le_div_iff₀ hx hx']
  have h := hf.cornerNumer_mul_cornerDenom_le_fst i j y hxx hnum hden
  linarith

/-! ### Monotonicity in the rival's signal -/

/-- For `Affiliated E.f`, `i ≠ j` and `y ≤ y'`,
`cornerNumer μ E i j x y * cornerDenom μ E i j x y'
≤ cornerDenom μ E i j x y * cornerNumer μ E i j x y'`. -/
theorem Affiliated.cornerNumer_mul_cornerDenom_le_snd {n : ℕ} {μ : Measure ℝ}
    [SigmaFinite μ] {E : SignalValueEnv n} (hf : Affiliated E.f) (i j : Fin n)
    (hij : i ≠ j) (x : ℝ) {y y' : ℝ} (hy : y ≤ y')
    (hnum : ∀ t : ℝ, FibreIntegrable μ
      (fun z => E.v i (Function.update (Function.update z i x) j t)
        * topDensity E.f i j (Function.update (Function.update z i x) j t))
      (otherRivals i j))
    (hden : ∀ t : ℝ, FibreIntegrable μ
      (fun z => topDensity E.f i j (Function.update (Function.update z i x) j t))
      (otherRivals i j)) :
    cornerNumer μ E i j x y * cornerDenom μ E i j x y'
      ≤ cornerDenom μ E i j x y * cornerNumer μ E i j x y' := by
  have hcomm : ∀ (z : Fin n → ℝ) (s t : ℝ),
      Function.update (Function.update z j s) i t
        = Function.update (Function.update z i t) j s :=
    fun z s t => Function.update_comm (Ne.symm hij) s t z
  have hf0 : (0 : (Fin n → ℝ) → ℝ) ≤ E.f := fun X => E.f_nonneg X
  have haff : Affiliated fun z : Fin n → ℝ =>
      topDensity E.f i j (Function.update z i x) :=
    (affiliated_topDensity hf hf0 i j).update_slice i x
  have hd0 : (0 : (Fin n → ℝ) → ℝ)
      ≤ fun z : Fin n → ℝ => topDensity E.f i j (Function.update z i x) :=
    fun z => topDensity_nonneg hf0 i j (Function.update z i x)
  have hgm : Monotone fun z : Fin n → ℝ => E.v i (Function.update z i x) :=
    (E.v_mono i).comp (monotone_update_profile i x)
  have hg0 : (0 : (Fin n → ℝ) → ℝ)
      ≤ fun z : Fin n → ℝ => E.v i (Function.update z i x) :=
    fun _ => E.v_nonneg i _
  have h₁ : FibreIntegrable μ
      (fun z => E.v i (Function.update (Function.update z j y) i x)
        * topDensity E.f i j (Function.update (Function.update z j y) i x))
      (otherRivals i j) := by
    simpa only [hcomm] using hnum y
  have h₄ : FibreIntegrable μ
      (fun z => E.v i (Function.update (Function.update z j y') i x)
        * topDensity E.f i j (Function.update (Function.update z j y') i x))
      (otherRivals i j) := by
    simpa only [hcomm] using hnum y'
  have h₂ : FibreIntegrable μ
      (fun z => topDensity E.f i j (Function.update (Function.update z j y') i x))
      (otherRivals i j) := by
    simpa only [hcomm] using hden y'
  have h₃ : FibreIntegrable μ
      (fun z => topDensity E.f i j (Function.update (Function.update z j y) i x))
      (otherRivals i j) := by
    simpa only [hcomm] using hden y
  have key := haff.marginalList_mul_le hd0 hgm hg0 j (otherRivals i j) hy h₁ h₂ h₃ h₄ 0
  simpa only [cornerNumer, cornerDenom, hcomm] using key

/-- For `Affiliated E.f` and `i ≠ j`, `y ↦ w μ E i j x y` is nondecreasing on
`{y | 0 < cornerDenom μ E i j x y}`. -/
theorem Affiliated.monotoneOn_w_snd {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]
    {E : SignalValueEnv n} (hf : Affiliated E.f) (i j : Fin n) (hij : i ≠ j) (x : ℝ)
    (hnum : ∀ t : ℝ, FibreIntegrable μ
      (fun z => E.v i (Function.update (Function.update z i x) j t)
        * topDensity E.f i j (Function.update (Function.update z i x) j t))
      (otherRivals i j))
    (hden : ∀ t : ℝ, FibreIntegrable μ
      (fun z => topDensity E.f i j (Function.update (Function.update z i x) j t))
      (otherRivals i j)) :
    MonotoneOn (fun y => w μ E i j x y) {y : ℝ | 0 < cornerDenom μ E i j x y} := by
  intro y hy y' hy' hyy
  simp only [Set.mem_setOf_eq] at hy hy'
  simp only [w]
  rw [div_le_div_iff₀ hy hy']
  have h := hf.cornerNumer_mul_cornerDenom_le_snd i j hij x hyy hnum hden
  linarith

/-! ### The strict own-signal effect -/

/-- `crossNumer μ E i j x x' y
= marginalList μ (fun z => E.v i (z[i↦x][j↦y]) * topDensity E.f i j (z[i↦x'][j↦y]))
(otherRivals i j) 0`: the value taken at own signal `x`, the density at own signal `x'`. -/
noncomputable def crossNumer {n : ℕ} (μ : Measure ℝ) (E : SignalValueEnv n) (i j : Fin n)
    (x x' y : ℝ) : ℝ :=
  marginalList μ
    (fun z => E.v i (Function.update (Function.update z i x) j y)
      * topDensity E.f i j (Function.update (Function.update z i x') j y))
    (otherRivals i j) 0

/-- `ownEffect μ E i j x x' y
= marginalList μ (fun z => (E.v i (z[i↦x'][j↦y]) - E.v i (z[i↦x][j↦y]))
* topDensity E.f i j (z[i↦x'][j↦y])) (otherRivals i j) 0`. -/
noncomputable def ownEffect {n : ℕ} (μ : Measure ℝ) (E : SignalValueEnv n) (i j : Fin n)
    (x x' y : ℝ) : ℝ :=
  marginalList μ
    (fun z => (E.v i (Function.update (Function.update z i x') j y)
        - E.v i (Function.update (Function.update z i x) j y))
      * topDensity E.f i j (Function.update (Function.update z i x') j y))
    (otherRivals i j) 0

/-- `HasStrictOwnEffect μ E i j y S` : `0 < ownEffect μ E i j x x' y` whenever `x < x'` with
`x ∈ S` and `x' ∈ S`.

Derived, not assumed: `hasStrictOwnEffect_of_v_strictMono` proves it from
`SignalValueEnv.v_strictMono_own`, positivity of `cornerDenom μ E i j · y` on `S`, and the
integrability hypotheses. It is kept as a named predicate because it isolates the only use the
affiliation argument makes of strictness.

The height `y` and the set `S` are parameters rather than universally quantified because
`E.f_support` forces `ownEffect μ E i j x x' y = 0` as soon as `y` or `x'` lies outside
`Set.Icc E.x_lo E.x_hi`, so the unrestricted form
`∀ x x' y, x < x' → 0 < ownEffect μ E i j x x' y` holds for no `SignalValueEnv`. -/
def HasStrictOwnEffect {n : ℕ} (μ : Measure ℝ) (E : SignalValueEnv n) (i j : Fin n) (y : ℝ)
    (S : Set ℝ) : Prop :=
  ∀ ⦃x : ℝ⦄, x ∈ S → ∀ ⦃x' : ℝ⦄, x' ∈ S → x < x' → 0 < ownEffect μ E i j x x' y

/-- `cornerNumer μ E i j x' y = crossNumer μ E i j x x' y + ownEffect μ E i j x x' y`. -/
theorem cornerNumer_eq_crossNumer_add_ownEffect {n : ℕ} {μ : Measure ℝ}
    {E : SignalValueEnv n} (i j : Fin n) (x x' y : ℝ)
    (hcross : FibreIntegrable μ
      (fun z => E.v i (Function.update (Function.update z i x) j y)
        * topDensity E.f i j (Function.update (Function.update z i x') j y))
      (otherRivals i j))
    (hnum : FibreIntegrable μ
      (fun z => E.v i (Function.update (Function.update z i x') j y)
        * topDensity E.f i j (Function.update (Function.update z i x') j y))
      (otherRivals i j)) :
    cornerNumer μ E i j x' y = crossNumer μ E i j x x' y + ownEffect μ E i j x x' y := by
  have hfe : (fun z : Fin n → ℝ =>
        E.v i (Function.update (Function.update z i x') j y)
          * topDensity E.f i j (Function.update (Function.update z i x') j y))
      = fun z : Fin n → ℝ =>
        E.v i (Function.update (Function.update z i x) j y)
            * topDensity E.f i j (Function.update (Function.update z i x') j y)
          + (E.v i (Function.update (Function.update z i x') j y)
              - E.v i (Function.update (Function.update z i x) j y))
            * topDensity E.f i j (Function.update (Function.update z i x') j y) := by
    funext z; ring
  have hown : FibreIntegrable μ
      (fun z => (E.v i (Function.update (Function.update z i x') j y)
          - E.v i (Function.update (Function.update z i x) j y))
        * topDensity E.f i j (Function.update (Function.update z i x') j y))
      (otherRivals i j) := by
    have hfe' : (fun z : Fin n → ℝ =>
          (E.v i (Function.update (Function.update z i x') j y)
            - E.v i (Function.update (Function.update z i x) j y))
          * topDensity E.f i j (Function.update (Function.update z i x') j y))
        = fun z : Fin n → ℝ =>
          E.v i (Function.update (Function.update z i x') j y)
              * topDensity E.f i j (Function.update (Function.update z i x') j y)
            + (-1) * (E.v i (Function.update (Function.update z i x) j y)
              * topDensity E.f i j (Function.update (Function.update z i x') j y)) := by
      funext z; ring
    rw [hfe']
    exact hnum.add (hcross.const_mul (-1))
  simp only [cornerNumer, crossNumer, ownEffect, hfe]
  exact marginalList_add hcross hown 0

/-- For `Affiliated E.f` and `x ≤ x'`,
`cornerNumer μ E i j x y * cornerDenom μ E i j x' y
≤ cornerDenom μ E i j x y * crossNumer μ E i j x x' y`. -/
theorem Affiliated.cornerNumer_mul_cornerDenom_le_cross {n : ℕ} {μ : Measure ℝ}
    [SigmaFinite μ] {E : SignalValueEnv n} (hf : Affiliated E.f) (i j : Fin n) (y : ℝ)
    {x x' : ℝ} (hx : x ≤ x')
    (hnum : FibreIntegrable μ
      (fun z => E.v i (Function.update (Function.update z i x) j y)
        * topDensity E.f i j (Function.update (Function.update z i x) j y))
      (otherRivals i j))
    (hcross : FibreIntegrable μ
      (fun z => E.v i (Function.update (Function.update z i x) j y)
        * topDensity E.f i j (Function.update (Function.update z i x') j y))
      (otherRivals i j))
    (hden : ∀ t : ℝ, FibreIntegrable μ
      (fun z => topDensity E.f i j (Function.update (Function.update z i t) j y))
      (otherRivals i j)) :
    cornerNumer μ E i j x y * cornerDenom μ E i j x' y
      ≤ cornerDenom μ E i j x y * crossNumer μ E i j x x' y := by
  have hf0 : (0 : (Fin n → ℝ) → ℝ) ≤ E.f := fun X => E.f_nonneg X
  have haff : Affiliated fun z : Fin n → ℝ =>
      topDensity E.f i j (Function.update z j y) :=
    (affiliated_topDensity hf hf0 i j).update_slice j y
  have hd0 : (0 : (Fin n → ℝ) → ℝ)
      ≤ fun z : Fin n → ℝ => topDensity E.f i j (Function.update z j y) :=
    fun z => topDensity_nonneg hf0 i j (Function.update z j y)
  have hgm : Monotone fun z : Fin n → ℝ =>
      E.v i (Function.update (Function.update z i x) j y) :=
    (E.v_mono i).comp ((monotone_update_profile j y).comp (monotone_update_profile i x))
  have hg0 : (0 : (Fin n → ℝ) → ℝ)
      ≤ fun z : Fin n → ℝ => E.v i (Function.update (Function.update z i x) j y) :=
    fun _ => E.v_nonneg i _
  have h₁ : FibreIntegrable μ
      (fun z => E.v i (Function.update (Function.update (Function.update z i x) i x) j y)
        * topDensity E.f i j (Function.update (Function.update z i x) j y))
      (otherRivals i j) := by
    simpa only [upd_i_idem] using hnum
  have h₄ : FibreIntegrable μ
      (fun z => E.v i (Function.update (Function.update (Function.update z i x') i x) j y)
        * topDensity E.f i j (Function.update (Function.update z i x') j y))
      (otherRivals i j) := by
    simpa only [upd_i_idem] using hcross
  have key := haff.marginalList_mul_le hd0 hgm hg0 i (otherRivals i j) hx
    h₁ (hden x') (hden x) h₄ 0
  simpa only [cornerNumer, cornerDenom, crossNumer, upd_i_idem] using key

/-- Under `HasStrictOwnEffect μ E i j y T` and `0 < cornerDenom μ E i j t y` for `t ∈ T`,
`x ↦ w μ E i j x y` is strictly increasing on `T`. -/
theorem Affiliated.strictMonoOn_w_fst {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]
    {E : SignalValueEnv n} (hf : Affiliated E.f) (i j : Fin n) (y : ℝ) {T : Set ℝ}
    (hT : ∀ ⦃t : ℝ⦄, t ∈ T → 0 < cornerDenom μ E i j t y)
    (hstrict : HasStrictOwnEffect μ E i j y T)
    (hnum : ∀ t : ℝ, FibreIntegrable μ
      (fun z => E.v i (Function.update (Function.update z i t) j y)
        * topDensity E.f i j (Function.update (Function.update z i t) j y))
      (otherRivals i j))
    (hden : ∀ t : ℝ, FibreIntegrable μ
      (fun z => topDensity E.f i j (Function.update (Function.update z i t) j y))
      (otherRivals i j))
    (hcross : ∀ s s' : ℝ, FibreIntegrable μ
      (fun z => E.v i (Function.update (Function.update z i s) j y)
        * topDensity E.f i j (Function.update (Function.update z i s') j y))
      (otherRivals i j)) :
    StrictMonoOn (fun x => w μ E i j x y) T := by
  intro x hx x' hx' hxx
  have hDx := hT hx
  have hDx' := hT hx'
  have hdec := cornerNumer_eq_crossNumer_add_ownEffect (μ := μ) (E := E) i j x x' y
    (hcross x x') (hnum x')
  have hpos : 0 < ownEffect μ E i j x x' y := hstrict hx hx' hxx
  have hlt : crossNumer μ E i j x x' y < cornerNumer μ E i j x' y := by linarith
  have haff := hf.cornerNumer_mul_cornerDenom_le_cross i j y hxx.le (hnum x)
    (hcross x x') hden
  simp only [w]
  rw [div_lt_div_iff₀ hDx hDx']
  have hmul := mul_lt_mul_of_pos_left hlt hDx
  linarith

/-- `Affiliated.strictMonoOn_w_fst` on the positive-denominator set. -/
theorem Affiliated.strictMonoOn_w_fst_cornerDenom_pos {n : ℕ} {μ : Measure ℝ}
    [SigmaFinite μ] {E : SignalValueEnv n} (hf : Affiliated E.f) (i j : Fin n) (y : ℝ)
    (hstrict : HasStrictOwnEffect μ E i j y {x : ℝ | 0 < cornerDenom μ E i j x y})
    (hnum : ∀ t : ℝ, FibreIntegrable μ
      (fun z => E.v i (Function.update (Function.update z i t) j y)
        * topDensity E.f i j (Function.update (Function.update z i t) j y))
      (otherRivals i j))
    (hden : ∀ t : ℝ, FibreIntegrable μ
      (fun z => topDensity E.f i j (Function.update (Function.update z i t) j y))
      (otherRivals i j))
    (hcross : ∀ s s' : ℝ, FibreIntegrable μ
      (fun z => E.v i (Function.update (Function.update z i s) j y)
        * topDensity E.f i j (Function.update (Function.update z i s') j y))
      (otherRivals i j)) :
    StrictMonoOn (fun x => w μ E i j x y) {x : ℝ | 0 < cornerDenom μ E i j x y} :=
  hf.strictMonoOn_w_fst i j y (fun _ ht => ht) hstrict hnum hden hcross

/-! ### The diagonal of the corner conditional value

`bidII μ E i j x = w μ E i j x x` is the corner conditional value on the diagonal. The only
property proved of it here is strict monotonicity. Nothing in this file — or anywhere in the
library — defines a payoff, a best response, or an equilibrium, so no statement here asserts
that `bidII` is an equilibrium bid function of the second-price auction; the name records the
intended reading, not a proved one. -/

/-- Under `HasStrictOwnEffect μ E i j`, `bidII μ E i j` is strictly increasing on any set
`S` on which `cornerDenom μ E i j` is positive at every pair of points.

The pair condition, rather than `{x | 0 < cornerDenom μ E i j x x}`, is what the proof
`w μ E i j x x < w μ E i j x' x ≤ w μ E i j x' x'` consumes: the middle term needs
`0 < cornerDenom μ E i j x' x` at the off-diagonal point `(x', x)`, which does not follow
from positivity on the diagonal. -/
theorem Affiliated.strictMonoOn_bidII {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]
    {E : SignalValueEnv n} (hf : Affiliated E.f) (i j : Fin n) (hij : i ≠ j)
    {S : Set ℝ} (hstrict : ∀ ⦃y : ℝ⦄, y ∈ S → HasStrictOwnEffect μ E i j y S)
    (hnum : ∀ s t : ℝ, FibreIntegrable μ
      (fun z => E.v i (Function.update (Function.update z i s) j t)
        * topDensity E.f i j (Function.update (Function.update z i s) j t))
      (otherRivals i j))
    (hden : ∀ s t : ℝ, FibreIntegrable μ
      (fun z => topDensity E.f i j (Function.update (Function.update z i s) j t))
      (otherRivals i j))
    (hcross : ∀ s s' t : ℝ, FibreIntegrable μ
      (fun z => E.v i (Function.update (Function.update z i s) j t)
        * topDensity E.f i j (Function.update (Function.update z i s') j t))
      (otherRivals i j))
    (hS : ∀ ⦃s : ℝ⦄, s ∈ S → ∀ ⦃t : ℝ⦄, t ∈ S → 0 < cornerDenom μ E i j s t) :
    StrictMonoOn (bidII μ E i j) S := by
  intro x hx x' hx' hxx
  have h₁ : w μ E i j x x < w μ E i j x' x :=
    hf.strictMonoOn_w_fst i j x (fun _ ht => hS ht hx) (hstrict hx)
      (fun t => hnum t x) (fun t => hden t x) (fun s s' => hcross s s' x) hx hx' hxx
  have h₂ : w μ E i j x' x ≤ w μ E i j x' x' :=
    hf.monotoneOn_w_snd i j hij x' (fun t => hnum x' t) (fun t => hden x' t)
      (hS hx' hx) (hS hx' hx') hxx.le
  simpa only [bidII] using h₁.trans_le h₂

/-! ### Strictness from the environment

`SignalValueEnv.v_strictMono_own` says each `E.v i` is strictly increasing in coordinate `i`
with the other coordinates held fixed. For `i ≠ j` the two profiles `z[i↦x][j↦y]` and
`z[i↦x'][j↦y]` differ exactly in coordinate `i`, so the own-signal increment is strictly
positive at every `z` when `x < x'`. Against the nonnegative weight
`topDensity E.f i j (·[i↦x'][j↦y])`, whose iterated marginal is `cornerDenom μ E i j x' y`,
`marginalList_lt_of_lt` upgrades this pointwise strict inequality to a strict inequality of
iterated marginals — which is exactly `0 < ownEffect μ E i j x x' y`. -/

/-- `HasStrictOwnEffect μ E i j y S` is a consequence of the environment, not an extra
assumption: it follows from `SignalValueEnv.v_strictMono_own` together with `i ≠ j`,
positivity of `cornerDenom μ E i j · y` on `S`, and the integrability hypotheses. -/
theorem hasStrictOwnEffect_of_v_strictMono {n : ℕ} {μ : Measure ℝ}
    (E : SignalValueEnv n) (i j : Fin n) (hij : i ≠ j) (y : ℝ) (S : Set ℝ)
    (hS : ∀ ⦃t : ℝ⦄, t ∈ S → 0 < cornerDenom μ E i j t y)
    (hnum : ∀ t : ℝ, FibreIntegrable μ
      (fun z => E.v i (Function.update (Function.update z i t) j y)
        * topDensity E.f i j (Function.update (Function.update z i t) j y))
      (otherRivals i j))
    (hden : ∀ t : ℝ, FibreIntegrable μ
      (fun z => topDensity E.f i j (Function.update (Function.update z i t) j y))
      (otherRivals i j))
    (hcross : ∀ s s' : ℝ, FibreIntegrable μ
      (fun z => E.v i (Function.update (Function.update z i s) j y)
        * topDensity E.f i j (Function.update (Function.update z i s') j y))
      (otherRivals i j)) :
    HasStrictOwnEffect μ E i j y S := by
  intro x hx x' hx' hxx
  have hcomm : ∀ (t : ℝ) (z : Fin n → ℝ),
      Function.update (Function.update z i t) j y
        = Function.update (Function.update z j y) i t :=
    fun t z => (Function.update_comm (Ne.symm hij) y t z).symm
  have hv : ∀ z : Fin n → ℝ,
      E.v i (Function.update (Function.update z i x) j y)
        < E.v i (Function.update (Function.update z i x') j y) := by
    intro z
    rw [hcomm x z, hcomm x' z]
    exact E.v_strictMono_own i (Function.update z j y) hxx
  have hρ0 : (0 : (Fin n → ℝ) → ℝ)
      ≤ fun z : Fin n → ℝ =>
        topDensity E.f i j (Function.update (Function.update z i x') j y) :=
    fun z => topDensity_nonneg (fun X => E.f_nonneg X) i j
      (Function.update (Function.update z i x') j y)
  have hden' : 0 < marginalList μ
      (fun z => topDensity E.f i j (Function.update (Function.update z i x') j y))
      (otherRivals i j) 0 := hS hx'
  have hlt := marginalList_lt_of_lt (μ := μ) (otherRivals i j)
    (ρ := fun z => topDensity E.f i j (Function.update (Function.update z i x') j y))
    (g₁ := fun z => E.v i (Function.update (Function.update z i x) j y))
    (g₂ := fun z => E.v i (Function.update (Function.update z i x') j y))
    0 hρ0 hv hden' (hden x') (hcross x x') (hnum x')
  have hcn : crossNumer μ E i j x x' y < cornerNumer μ E i j x' y := hlt
  have hdec := cornerNumer_eq_crossNumer_add_ownEffect (μ := μ) (E := E) i j x x' y
    (hcross x x') (hnum x')
  linarith

/-- `Affiliated.strictMonoOn_w_fst` with `HasStrictOwnEffect` discharged by
`hasStrictOwnEffect_of_v_strictMono`: the caller supplies `i ≠ j`, positivity of
`cornerDenom μ E i j · y` on `T`, and the integrability hypotheses. -/
theorem Affiliated.strictMonoOn_w_fst_of_v_strictMono {n : ℕ} {μ : Measure ℝ}
    [SigmaFinite μ] {E : SignalValueEnv n} (hf : Affiliated E.f) (i j : Fin n) (hij : i ≠ j)
    (y : ℝ) {T : Set ℝ}
    (hT : ∀ ⦃t : ℝ⦄, t ∈ T → 0 < cornerDenom μ E i j t y)
    (hnum : ∀ t : ℝ, FibreIntegrable μ
      (fun z => E.v i (Function.update (Function.update z i t) j y)
        * topDensity E.f i j (Function.update (Function.update z i t) j y))
      (otherRivals i j))
    (hden : ∀ t : ℝ, FibreIntegrable μ
      (fun z => topDensity E.f i j (Function.update (Function.update z i t) j y))
      (otherRivals i j))
    (hcross : ∀ s s' : ℝ, FibreIntegrable μ
      (fun z => E.v i (Function.update (Function.update z i s) j y)
        * topDensity E.f i j (Function.update (Function.update z i s') j y))
      (otherRivals i j)) :
    StrictMonoOn (fun x => w μ E i j x y) T :=
  hf.strictMonoOn_w_fst i j y hT
    (hasStrictOwnEffect_of_v_strictMono E i j hij y T hT hnum hden hcross) hnum hden hcross

/-- `Affiliated.strictMonoOn_w_fst_of_v_strictMono` on the positive-denominator set: no
positivity hypothesis at all beyond the one built into the set. -/
theorem Affiliated.strictMonoOn_w_fst_cornerDenom_pos_of_v_strictMono {n : ℕ} {μ : Measure ℝ}
    [SigmaFinite μ] {E : SignalValueEnv n} (hf : Affiliated E.f) (i j : Fin n) (hij : i ≠ j)
    (y : ℝ)
    (hnum : ∀ t : ℝ, FibreIntegrable μ
      (fun z => E.v i (Function.update (Function.update z i t) j y)
        * topDensity E.f i j (Function.update (Function.update z i t) j y))
      (otherRivals i j))
    (hden : ∀ t : ℝ, FibreIntegrable μ
      (fun z => topDensity E.f i j (Function.update (Function.update z i t) j y))
      (otherRivals i j))
    (hcross : ∀ s s' : ℝ, FibreIntegrable μ
      (fun z => E.v i (Function.update (Function.update z i s) j y)
        * topDensity E.f i j (Function.update (Function.update z i s') j y))
      (otherRivals i j)) :
    StrictMonoOn (fun x => w μ E i j x y) {x : ℝ | 0 < cornerDenom μ E i j x y} :=
  hf.strictMonoOn_w_fst_of_v_strictMono i j hij y (fun _ ht => ht) hnum hden hcross

/-- `Affiliated.strictMonoOn_bidII` with `HasStrictOwnEffect` discharged by
`hasStrictOwnEffect_of_v_strictMono`: the caller supplies `i ≠ j`, positivity of
`cornerDenom μ E i j` at every pair of points of `S`, and the integrability hypotheses. -/
theorem Affiliated.strictMonoOn_bidII_of_v_strictMono {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]
    {E : SignalValueEnv n} (hf : Affiliated E.f) (i j : Fin n) (hij : i ≠ j) {S : Set ℝ}
    (hnum : ∀ s t : ℝ, FibreIntegrable μ
      (fun z => E.v i (Function.update (Function.update z i s) j t)
        * topDensity E.f i j (Function.update (Function.update z i s) j t))
      (otherRivals i j))
    (hden : ∀ s t : ℝ, FibreIntegrable μ
      (fun z => topDensity E.f i j (Function.update (Function.update z i s) j t))
      (otherRivals i j))
    (hcross : ∀ s s' t : ℝ, FibreIntegrable μ
      (fun z => E.v i (Function.update (Function.update z i s) j t)
        * topDensity E.f i j (Function.update (Function.update z i s') j t))
      (otherRivals i j))
    (hS : ∀ ⦃s : ℝ⦄, s ∈ S → ∀ ⦃t : ℝ⦄, t ∈ S → 0 < cornerDenom μ E i j s t) :
    StrictMonoOn (bidII μ E i j) S :=
  hf.strictMonoOn_bidII i j hij
    (fun y hy => hasStrictOwnEffect_of_v_strictMono E i j hij y S (fun _ ht => hS ht hy)
      (fun t => hnum t y) (fun t => hden t y) (fun s s' => hcross s s' y))
    hnum hden hcross hS

end Auction.Affiliation

end
