module

public import Auctionlib.Auction.Affiliation.SecondPrice
public import Auctionlib.Auction.Affiliation.Linkage
public import Auctionlib.Auction.Affiliation.LogSupermodular
public import Mathlib

/-! # Worked examples of the affiliation hypotheses

## Main results

* `Auction.Affiliation.Examples.boxInd`, `Auction.Affiliation.Examples.cap` : the unit
  interval indicator and the fibre `cap t u = boxInd u * 1[u ≤ t]` of the top-rival density
  in one non-corner coordinate, with `Auction.Affiliation.Examples.cap_integral` :
  `∫ u, cap t u = t`.
* `Auction.Affiliation.Examples.Ebox` : the uniform product density on `[0,1]ⁿ` with
  exponential private values `v i X = exp (X i)`, and
  `Auction.Affiliation.Examples.Ebox_affiliated`.
* `Auction.Affiliation.Examples.Etri` : the uniform density on `[0,1]ⁿ` times the indicator
  of the sublattice `{z | z 1 ≤ z 0}`, and `Auction.Affiliation.Examples.Etri_affiliated`
  via `Affiliated.mul` and `affiliated_indicator_of_isSublattice`.
* `Auction.Affiliation.Examples.Etri_strictly_affiliated` : at `x = (0.6, 0.2)`,
  `y = (0.2, 0.6)`, `f x * f y = 0 < 1 = f (x ⊔ y) * f (x ⊓ y)`.
* `Auction.Affiliation.Examples.Elow` : the uniform density on `[0,1]³` times the indicator
  of the sublattice `{z | z 2 ≤ z 0}`, with
  `Auction.Affiliation.Examples.Elow_affiliated` and
  `Auction.Affiliation.Examples.Elow_strictly_affiliated`.
* `Auction.Affiliation.Examples.pivotalOptimal_tri_two`,
  `Auction.Affiliation.Examples.pivotalOptimal_three`,
  `Auction.Affiliation.Examples.pivotalOptimal_four`,
  `Auction.Affiliation.Examples.pivotalOptimal_low` :
  `Affiliated.bidII_pivotalOptimal` instantiated at `Etri 2`, `Ebox 3`, `Ebox 4` and `Elow`.
* `Auction.Affiliation.Examples.expectedPayII_mono_tri_two`,
  `Auction.Affiliation.Examples.expectedPayII_mono_low` :
  `Affiliated.expectedPayII_mono` instantiated at `Etri 2` and `Elow`, with
  `Auction.Affiliation.Examples.hB_tri_two` and `Auction.Affiliation.Examples.hB_low`
  discharging its positivity hypothesis at the larger signal over the lower region.
* `Auction.Affiliation.Examples.expectedPayII_le_bidII_tri_two`,
  `Auction.Affiliation.Examples.expectedPayII_le_bidII_low` :
  `Affiliated.expectedPayII_le_bidII` instantiated at the same two environments.
* `Auction.Affiliation.Examples.bidII_tri_two`, `Auction.Affiliation.Examples.bidII_three`,
  `Auction.Affiliation.Examples.bidII_low` : the diagonal corner value equals the bidder's
  own value `exp x` on the signal box — the bid-your-value benchmark, recovered rather than
  assumed.
* `Auction.Affiliation.Examples.cornerDenom_three`,
  `Auction.Affiliation.Examples.cornerDenom_four` :
  `cornerDenom volume (Ebox n) 0 1 x y = boxInd x * boxInd y * y ^ (n - 2)` for `n = 3, 4`.
* `Auction.Affiliation.Examples.cornerDenom_low` :
  `cornerDenom mu0 Elow 0 1 x y = min x y` on the box — not a product of a function of `x`
  and a function of `y`.
* `Auction.Affiliation.Examples.pivotalGain_integrand_three`,
  `Auction.Affiliation.Examples.pivotalGain_three_closed` : the `n = 3` pivotal integrand is
  `y * (exp x - exp y)`.
* `Auction.Affiliation.Examples.expectedPayII_tri_two`,
  `Auction.Affiliation.Examples.expectedPayII_low` : the winner's conditional expected
  payment in closed form, `(exp a - 1) / a` and `((a - 1) * exp a + 1) / (a ^ 2 / 2)`, with
  the monotonicity corollaries `expectedPayII_mono_tri_two_closed` and
  `expectedPayII_mono_low_closed`.
* `Auction.Affiliation.Examples.bidII_three_at_zero` : `bidII volume (Ebox 3) 0 1 0 = 0`,
  while `exp 0 = 1`.
* `Auction.Affiliation.Examples.monotoneOn_bidII_low_lib`,
  `Auction.Affiliation.Examples.bidII_low_not_monotoneOn_above` : what the library's own
  route `Affiliated.monotoneOn_bidII` actually yields at `Elow`, namely
  `MonotoneOn (bidII mu0 Elow 0 1) (Set.Ioc 0 1)`. This does **not** discharge the caller
  obligation `hbid` of `Affiliated.expectedPayII_mono`, which demands monotonicity on a
  `Set.Iic x'`; `Set.Ioc 0 1` is not of that form, and on `Set.Iic x'` with `x' > 1` the
  conclusion is false outright (`bidII_low_not_monotoneOn_above`). The `hbid` actually fed
  to `expectedPayII_mono_low` is the hand-proved `monotoneOn_bidII_low`.
* `Auction.Affiliation.Examples.logSupermodularOn_signalBox_Ebox`,
  `Auction.Affiliation.Examples.logSupermodularOn_Etri`,
  `Auction.Affiliation.Examples.logSupermodularOn_Elow` : the localized characterization
  `affiliatedOn_iff_logSupermodularOn` applied to the three densities above, on the
  sublattice where each is positive (the signal box, and the box met with the triangle).
* `Auction.Affiliation.Examples.Ecoup`, `Auction.Affiliation.Examples.Ecoup_affiliated`,
  `Auction.Affiliation.Examples.logSupermodularOn_signalBox_Ecoup`,
  `Auction.Affiliation.Examples.logSupermodularOn_Ecoup_two_strict` : an environment whose
  density is `exp (X₀ X₁)` on the box, so that its log is **non-constant** there and the
  localized log-supermodularity is strict at an exhibited pair.
* `Auction.Affiliation.Examples.mu0`, `Auction.Affiliation.Examples.restrict_Iic_mu0`,
  `Auction.Affiliation.Examples.integrableOn_Iic_mu0`,
  `Auction.Affiliation.Examples.integral_Iic_mu0` : the uniform measure on the signal box
  and the two reusable recipes for the winning-event side conditions.

Concrete environments in which the headline hypotheses of
`Auction.Affiliation.SecondPrice` and `Auction.Affiliation.Linkage` are discharged
simultaneously, so that the headline theorems have nonempty instances and the objects they
speak about have closed forms.

Three things these examples are meant to settle. First, affiliation is **strict** in
`Etri` and `Elow`: a product density satisfies the four-functions inequality with equality,
so it alone is no evidence that the hypothesis has content, and
`Etri_strictly_affiliated` / `Elow_strictly_affiliated` exhibit points where the inequality
is strict. Second, `n = 2` is **doubly degenerate** — `otherRivals 0 1 = []`, so the
`FibreIntegrable` hypotheses reduce to `True`, and `maxAt 0 1` is everything, so
`topDensity E.f 0 1 = E.f`; the instantiations at `n = 3` and `n = 4` are the ones that
exercise the marginalization. Third, `Etri 2` has a further degeneracy that `Elow` repairs:
coupling the two corner coordinates forces `cornerDenom μ (Etri 2) 0 1 x y = 0` for `y > x`,
so the upward half of `pivotalOptimal_tri_two` concerns a null region, whereas
`cornerDenom mu0 Elow 0 1 x y = min x y` is positive on both sides of the diagonal.

Two traps recorded here. At `n ≥ 3` the corner denominator vanishes at the bottom of the
box, so `bidII` is `0` there while `exp` is `1`: the product `bidII y * cornerDenom x y`
matches its naive closed form only after a case split at the floor (see
`bidII_three_at_zero`, and the splits inside `linkNumer_low` and
`integrableOn_bidII_mul_low`). And the hypothesis
`hB : 0 < ∫ y in Set.Iic x, cornerDenom μ E i j x' y ∂μ` of `Affiliated.expectedPayII_mono`
— the corner denominator at the larger signal, integrated over the lower winning event — is
the one hypothesis TP2 does not supply; for a product density it collapses to `linkDenom` by
factorization, so it is discharged here at the two non-product environments (`hB_tri_two`,
`hB_low`). That discharge is honest but it is **not yet a stress test**: at both
environments the integral still evaluates independently of the larger signal,
`integral_cornerDenom_tri_two` giving `a` and `integral_cornerDenom_low` giving `a ^ 2 / 2`
for every `c ≥ a` in the box, so it coincides numerically with `linkDenom` at the smaller
signal (`linkDenom_tri_two`, `linkDenom_low`) exactly as in the product case. Being
non-product is therefore not by itself enough to separate `hB` from `linkDenom`; an
environment in which the two genuinely differ is not exhibited here and remains open.

No mechanism, equilibrium, revenue, or format comparison is defined or claimed here; these
are instances of the existing statements.
-/

@[expose] public section

open MeasureTheory

namespace Auction.Affiliation.Examples

noncomputable section

/-! ## The unit-interval indicator -/

/-- `boxInd t = 1` on `[0,1]` and `0` off it. -/
def boxInd (t : ℝ) : ℝ := if 0 ≤ t ∧ t ≤ 1 then 1 else 0

/-- `0 ≤ boxInd t`. -/
theorem boxInd_nonneg (t : ℝ) : 0 ≤ boxInd t := by unfold boxInd; split <;> norm_num

/-- `t ∉ Set.Icc 0 1` implies `boxInd t = 0`. -/
theorem boxInd_eq_zero {t : ℝ} (h : t ∉ Set.Icc (0:ℝ) 1) : boxInd t = 0 := by
  unfold boxInd; rw [if_neg]; simpa [Set.mem_Icc] using h

/-- `t ∈ Set.Icc 0 1` implies `boxInd t = 1`. -/
theorem boxInd_eq_one {t : ℝ} (h : t ∈ Set.Icc (0:ℝ) 1) : boxInd t = 1 := by
  unfold boxInd; rw [if_pos]; simpa [Set.mem_Icc] using h

/-- `0 < boxInd t ↔ t ∈ Set.Icc 0 1`. -/
theorem boxInd_pos_iff {t : ℝ} : 0 < boxInd t ↔ t ∈ Set.Icc (0:ℝ) 1 := by
  unfold boxInd; split <;> simp_all [Set.mem_Icc]

/-- `boxInd = (Set.Icc 0 1).indicator 1`. -/
theorem boxInd_eq_indicator : boxInd = Set.indicator (Set.Icc (0:ℝ) 1) 1 := by
  funext t
  by_cases h : t ∈ Set.Icc (0:ℝ) 1
  · rw [boxInd_eq_one h, Set.indicator_of_mem h]; rfl
  · rw [boxInd_eq_zero h, Set.indicator_of_notMem h]

/-! ## The uniform product environment on `[0,1]ⁿ` -/

/-- The uniform product density on the box `[0,1]ⁿ`. -/
def unifDens (n : ℕ) : (Fin n → ℝ) → ℝ := fun X => ∏ k, boxInd (X k)

/-- Exponential private values, `v i X = exp (X i)`. -/
def expVal (n : ℕ) : Fin n → (Fin n → ℝ) → ℝ := fun i X => Real.exp (X i)

/-- The uniform box environment: `n` bidders, signals uniform and independent on `[0,1]`,
private values `v i X = exp (X i)`. -/
def Ebox (n : ℕ) : SignalValueEnv n where
  x_lo := 0
  x_hi := 1
  x_lo_le_hi := by norm_num
  f := unifDens n
  f_nonneg := fun X => Finset.prod_nonneg (fun _ _ => boxInd_nonneg _)
  f_support := by
    rintro X ⟨i, hi⟩
    exact Finset.prod_eq_zero (Finset.mem_univ i) (boxInd_eq_zero hi)
  v := expVal n
  v_nonneg := fun i X => (Real.exp_pos _).le
  v_continuous := fun i => Real.continuous_exp.comp (continuous_apply i)
  v_mono := fun i X Y h => Real.exp_le_exp.2 (h i)
  v_strictMono_own := fun i _ a b hab => by
    simp only [expVal, Function.update_self]; exact Real.exp_lt_exp.2 hab

/-- `Affiliated (Ebox n).f`: a product density is affiliated. -/
theorem Ebox_affiliated (n : ℕ) : Affiliated (Ebox n).f :=
  factors_affiliated (g := fun _ => boxInd) (fun _ => rfl)

/-! ## The strictly affiliated (non-product) environment

The uniform box density multiplied by the indicator of the sublattice
`{z | z 1 ≤ z 0}`. Every product density satisfies the four-functions inequality with
*equality*, so a product density alone is no evidence that the affiliation hypotheses have
content; this one satisfies it strictly at an exhibited pair of points
(`Etri_strictly_affiliated`). -/

/-- The lower triangle `{z | z 1 ≤ z 0}` — a sublattice of `Fin n → ℝ` that is not a
product set. -/
def triSet (n : ℕ) [NeZero n] : Set (Fin n → ℝ) := {z | z 1 ≤ z 0}

/-- `IsSublattice (triSet n)`. -/
theorem isSublattice_triSet (n : ℕ) [NeZero n] : IsSublattice (triSet n) where
  supClosed x hx y hy := by
    simp only [triSet, Set.mem_setOf_eq, Pi.sup_apply] at *
    exact sup_le_sup hx hy
  infClosed x hx y hy := by
    simp only [triSet, Set.mem_setOf_eq, Pi.inf_apply] at *
    exact inf_le_inf hx hy

/-- The uniform box density restricted to the sublattice `triSet n`. For `n ≥ 2` this
density does **not** factor as a product over the coordinates: the constraint `X 1 ≤ X 0`
couples two distinct coordinates. The qualification is needed — at `n = 1` the indices `0`
and `1` of `Fin 1` coincide, `triSet 1` is all of `Fin 1 → ℝ`, and `triDens 1` is the
product density `fun X => boxInd (X 0)`. -/
def triDens (n : ℕ) [NeZero n] : (Fin n → ℝ) → ℝ :=
  fun X => (∏ k, boxInd (X k)) * (triSet n).indicator 1 X

/-- `0 ≤ triDens n`. -/
theorem triDens_nonneg (n : ℕ) [NeZero n] (X : Fin n → ℝ) : 0 ≤ triDens n X :=
  mul_nonneg (Finset.prod_nonneg fun _ _ => boxInd_nonneg _)
    (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

/-- The strictly affiliated environment: uniform on the box `[0,1]ⁿ` intersected with the
lower triangle `{z | z 1 ≤ z 0}`, private values `v i X = exp (X i)`. -/
def Etri (n : ℕ) [NeZero n] : SignalValueEnv n where
  x_lo := 0
  x_hi := 1
  x_lo_le_hi := by norm_num
  f := triDens n
  f_nonneg := triDens_nonneg n
  f_support := by
    rintro X ⟨i, hi⟩
    have h : (∏ k, boxInd (X k)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (boxInd_eq_zero hi)
    simp [triDens, h]
  v := expVal n
  v_nonneg := fun i X => (Real.exp_pos _).le
  v_continuous := fun i => Real.continuous_exp.comp (continuous_apply i)
  v_mono := fun i X Y h => Real.exp_le_exp.2 (h i)
  v_strictMono_own := fun i _ a b hab => by
    simp only [expVal, Function.update_self]; exact Real.exp_lt_exp.2 hab

/-- `Affiliated (Etri n).f`, by `Affiliated.mul` of the product part with the sublattice
indicator. -/
theorem Etri_affiliated (n : ℕ) [NeZero n] : Affiliated (Etri n).f :=
  (factors_affiliated (g := fun _ => boxInd) (fun _ => rfl)).mul
    (affiliated_indicator_of_isSublattice (isSublattice_triSet n))
    (fun _ => Finset.prod_nonneg fun _ _ => boxInd_nonneg _)
    (indicator_one_nonneg _)

/-- The affiliation inequality holds **strictly** for `Etri 2` at the pair
`x = (0.6, 0.2)`, `y = (0.2, 0.6)`:
`f x * f y = 0 < 1 = f (x ⊔ y) * f (x ⊓ y)`.
Every product density satisfies this inequality with equality, so this witnesses that
`Etri 2` is off the independence knife-edge. -/
theorem Etri_strictly_affiliated :
    triDens 2 ![0.6, 0.2] * triDens 2 ![0.2, 0.6]
      < triDens 2 (![(0.6:ℝ), 0.2] ⊔ ![(0.2:ℝ), 0.6])
        * triDens 2 (![(0.6:ℝ), 0.2] ⊓ ![(0.2:ℝ), 0.6]) := by
  have hb : triDens 2 ![(0.2:ℝ), 0.6] = 0 := by
    simp [triDens, triSet, Set.indicator_apply]
    norm_num
  rw [hb, mul_zero]
  have hsup : (![(0.6:ℝ), 0.2] ⊔ ![(0.2:ℝ), 0.6]) = ![(0.6:ℝ), 0.6] := by
    funext k; fin_cases k <;> simp [Pi.sup_apply] <;> norm_num
  have hinf : (![(0.6:ℝ), 0.2] ⊓ ![(0.2:ℝ), 0.6]) = ![(0.2:ℝ), 0.2] := by
    funext k; fin_cases k <;> simp [Pi.inf_apply] <;> norm_num
  rw [hsup, hinf]
  have h1 : triDens 2 ![(0.6:ℝ), 0.6] = 1 := by
    simp [triDens, triSet, Fin.prod_univ_two, boxInd]
    norm_num
  have h2 : triDens 2 ![(0.2:ℝ), 0.2] = 1 := by
    simp [triDens, triSet, Fin.prod_univ_two, boxInd]
    norm_num
  rw [h1, h2]; norm_num

/-! ## `n = 2`: the doubly degenerate case

At `n = 2` the corner objects carry no integral at all: `otherRivals 0 1 = []`, so the
`FibreIntegrable` hypotheses of `Affiliated.bidII_pivotalOptimal` are literally `True`, and
`maxAt 0 1` is everything, so `topDensity E.f 0 1 = E.f`. The instantiation below is
therefore evidence only about the *shape* of the statement; the genuine tests are the
`n ≥ 3` ones. -/

/-- `otherRivals (0 : Fin 2) 1 = []`: at `n = 2` there is no third bidder to marginalize. -/
theorem otherRivals_two : otherRivals (0 : Fin 2) 1 = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro k hk; rw [mem_otherRivals_iff] at hk; fin_cases k <;> simp at hk

/-- At `n = 2` every profile lies in `maxAt 0 1`. -/
theorem maxAt_two (z : Fin 2 → ℝ) : z ∈ maxAt (0 : Fin 2) 1 := by
  intro k hk0 hk1; fin_cases k <;> simp_all

section StrictTwo

variable (μ : Measure ℝ)

/-- `cornerDenom μ (Etri 2) 0 1 x y = boxInd x * boxInd y * 1[y ≤ x]`. The `1[y ≤ x]` factor
is the sublattice constraint: this is **not** a product of a function of `x` and a function
of `y`. -/
theorem cornerDenom_tri_two (x y : ℝ) :
    cornerDenom μ (Etri 2) 0 1 x y = boxInd x * boxInd y * (if y ≤ x then 1 else 0) := by
  rw [cornerDenom, otherRivals_two]
  show topDensity (Etri 2).f 0 1 _ = _
  rw [topDensity_of_mem _ _ _ (maxAt_two _)]
  show triDens 2 _ = _
  rw [triDens, Fin.prod_univ_two]
  simp [triSet, Set.indicator_apply]

/-- `cornerNumer μ (Etri 2) 0 1 x y = exp x * cornerDenom μ (Etri 2) 0 1 x y`. -/
theorem cornerNumer_tri_two (x y : ℝ) :
    cornerNumer μ (Etri 2) 0 1 x y
      = Real.exp x * (boxInd x * boxInd y * (if y ≤ x then 1 else 0)) := by
  rw [cornerNumer, otherRivals_two]
  show (Etri 2).v 0 _ * topDensity (Etri 2).f 0 1 _ = _
  rw [topDensity_of_mem _ _ _ (maxAt_two _)]
  show Real.exp _ * triDens 2 _ = _
  rw [triDens, Fin.prod_univ_two]
  simp [triSet, Set.indicator_apply]

/-- **The bid-your-value benchmark, recovered.** On the signal box the diagonal corner
value equals the bidder's own value, `bidII μ (Etri 2) 0 1 x = exp x`; off the box it is
`0`. Nothing here assumes it. -/
theorem bidII_tri_two (x : ℝ) :
    bidII μ (Etri 2) 0 1 x = if x ∈ Set.Icc (0:ℝ) 1 then Real.exp x else 0 := by
  rw [bidII, w, cornerNumer_tri_two, cornerDenom_tri_two, if_pos (le_refl x)]
  by_cases hx : x ∈ Set.Icc (0:ℝ) 1
  · rw [boxInd_eq_one hx, if_pos hx]; norm_num
  · rw [boxInd_eq_zero hx, if_neg hx]; norm_num

/-- The `hden` hypothesis of `Affiliated.bidII_pivotalOptimal` at `n = 2`: vacuous. -/
theorem hden_tri_two : ∀ s t : ℝ, FibreIntegrable μ
    (fun z => topDensity (Etri 2).f 0 1 (Function.update (Function.update z 0 s) 1 t))
    (otherRivals (0 : Fin 2) 1) := by
  intro s t; rw [otherRivals_two]; trivial

/-- The `hnum` hypothesis of `Affiliated.bidII_pivotalOptimal` at `n = 2`: vacuous. -/
theorem hnum_tri_two : ∀ s t : ℝ, FibreIntegrable μ
    (fun z => (Etri 2).v 0 (Function.update (Function.update z 0 s) 1 t)
      * topDensity (Etri 2).f 0 1 (Function.update (Function.update z 0 s) 1 t))
    (otherRivals (0 : Fin 2) 1) := by
  intro s t; rw [otherRivals_two]; trivial

/-- The support-regularity hypothesis `hreg` of `Affiliated.bidII_pivotalOptimal`. -/
theorem hreg_tri_two (x : ℝ) : ∀ y : ℝ, x < y →
    0 < cornerDenom μ (Etri 2) 0 1 x y → 0 < cornerDenom μ (Etri 2) 0 1 y y := by
  intro y _ hpos
  rw [cornerDenom_tri_two] at hpos ⊢
  have hy0 : boxInd y ≠ 0 := by
    rintro h; rw [h, mul_zero, zero_mul] at hpos; exact lt_irrefl _ hpos
  have hy : y ∈ Set.Icc (0:ℝ) 1 :=
    boxInd_pos_iff.1 (lt_of_le_of_ne (boxInd_nonneg y) (Ne.symm hy0))
  rw [boxInd_eq_one hy, if_pos (le_refl y)]; norm_num

end StrictTwo

/-- **Pivotal optimality of the diagonal bid, at a strictly affiliated density.**
`Affiliated.bidII_pivotalOptimal` instantiated at `Etri 2`: deviating above the diagonal
bid never gains, deviating below never loses. -/
theorem pivotalOptimal_tri_two (x : ℝ) :
    ∀ x₂ : ℝ,
      (x ≤ x₂ → pivotalGain (volume : Measure ℝ) (Etri 2) 0 1 x x x₂ ≤ 0)
      ∧ (x₂ ≤ x → 0 ≤ pivotalGain (volume : Measure ℝ) (Etri 2) 0 1 x x₂ x) :=
  (Etri_affiliated 2).bidII_pivotalOptimal 0 1 (hreg_tri_two volume x) (hnum_tri_two volume)
    (hden_tri_two volume)

/-! ## Caller-facing helpers for the winning-event integrals

Every hypothesis of `Affiliated.expectedPayII_mono` that is stated over `Set.Iic x` costs
the same six lines: rewrite the restricted measure through `Measure.restrict_restrict` and a
set identity, then compare with a continuous representative on the resulting compact
interval. The two lemmas here do that once. -/

/-- The uniform probability measure on the signal box `[0,1]`. -/
def mu0 : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1)

instance : IsFiniteMeasure mu0 := by rw [mu0]; exact ⟨by simp [Real.volume_Icc]⟩

/-- `Set.Iic a ∩ Set.Icc 0 1 = Set.Icc 0 a` for `a ∈ Set.Icc 0 1`. -/
theorem Iic_inter_Icc {a : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) :
    Set.Iic a ∩ Set.Icc (0:ℝ) 1 = Set.Icc 0 a := by
  ext y; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
  exact ⟨fun ⟨h, h0, _⟩ => ⟨h0, h⟩, fun ⟨h0, h⟩ => ⟨h, h0, le_trans h ha.2⟩⟩

/-- `mu0.restrict (Set.Iic a) = volume.restrict (Set.Icc 0 a)` for `a ∈ Set.Icc 0 1`: the
winning event, seen inside the signal box, is the compact interval `[0, a]`. -/
theorem restrict_Iic_mu0 {a : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) :
    mu0.restrict (Set.Iic a) = volume.restrict (Set.Icc 0 a) := by
  rw [mu0, Measure.restrict_restrict measurableSet_Iic, Iic_inter_Icc ha]

/-- **Helper for the four `IntegrableOn` side conditions.** To integrate `F` over the
winning event `Set.Iic a`, exhibit a continuous `g` agreeing with `F` on `[0, a]`. -/
theorem integrableOn_Iic_mu0 {a : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) {F g : ℝ → ℝ}
    (hg : Continuous g) (h : ∀ y ∈ Set.Icc (0:ℝ) a, g y = F y) :
    IntegrableOn F (Set.Iic a) mu0 := by
  rw [IntegrableOn, restrict_Iic_mu0 ha, ← IntegrableOn]
  exact IntegrableOn.congr_fun hg.integrableOn_Icc h measurableSet_Icc

/-- **Helper for the winning-event integrals.** `∫ y in Set.Iic a, F y ∂mu0` is the
interval integral of any `g` agreeing with `F` on `[0, a]`. -/
theorem integral_Iic_mu0 {a : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) (F g : ℝ → ℝ)
    (h : ∀ y ∈ Set.Icc (0:ℝ) a, F y = g y) :
    ∫ y in Set.Iic a, F y ∂mu0 = ∫ y in (0:ℝ)..a, g y := by
  rw [MeasureTheory.integral_def, ← MeasureTheory.integral_def, restrict_Iic_mu0 ha,
    setIntegral_congr_fun measurableSet_Icc h, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le ha.1]

/-! ## The linkage effect at the strictly affiliated density: the `hB` test

`Affiliated.expectedPayII_mono` carries the hypothesis
`hB : 0 < ∫ y in Set.Iic x, cornerDenom μ E i j x' y ∂μ` — the corner denominator at the
**larger** signal `x'`, integrated over the **lower** winning event `Set.Iic x`. The
`Linkage` module docstring flags this as the one hypothesis TP2 does not supply. For a
product density it collapses to `linkDenom` by factorization, so a product example does not
test it. Here it is discharged for the non-product `Etri 2`, where the mixed
`(x', y)` dependence is real: the sublattice constraint `y ≤ x'` is what has to be
defeated, and it is defeated by `y ≤ x ≤ x'`. -/

/-- On the box, below the diagonal, the corner denominator of `Etri 2` is `1`. -/
theorem cornerDenom_tri_two_eq_one {c y : ℝ} (hc : c ∈ Set.Icc (0:ℝ) 1)
    (hy : y ∈ Set.Icc (0:ℝ) 1) (hyc : y ≤ c) :
    cornerDenom mu0 (Etri 2) 0 1 c y = 1 := by
  rw [cornerDenom_tri_two, boxInd_eq_one hc, boxInd_eq_one hy, if_pos hyc]; norm_num

/-- `∫ y in Set.Iic a, cornerDenom mu0 (Etri 2) 0 1 c y ∂mu0 = a` whenever `a ≤ c` in the
box. Taking `c = a` gives `linkDenom`; taking `c = x'` and `a = x` gives `hB`. -/
theorem integral_cornerDenom_tri_two {a c : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1)
    (hc : c ∈ Set.Icc (0:ℝ) 1) (hac : a ≤ c) :
    ∫ y in Set.Iic a, cornerDenom mu0 (Etri 2) 0 1 c y ∂mu0 = a := by
  rw [integral_Iic_mu0 ha (fun y => cornerDenom mu0 (Etri 2) 0 1 c y) (fun _ => (1:ℝ))
    (fun y hy => cornerDenom_tri_two_eq_one hc ⟨hy.1, le_trans hy.2 ha.2⟩
      (le_trans hy.2 hac))]
  simp

/-- **The `hB` hypothesis of `Affiliated.expectedPayII_mono`, discharged at a non-product
density.** -/
theorem hB_tri_two {x x' : ℝ} (hx0 : 0 < x) (hxx : x ≤ x') (hx1 : x' ≤ 1) :
    0 < ∫ y in Set.Iic x, cornerDenom mu0 (Etri 2) 0 1 x' y ∂mu0 := by
  rw [integral_cornerDenom_tri_two ⟨hx0.le, le_trans hxx hx1⟩ ⟨le_trans hx0.le hxx, hx1⟩ hxx]
  exact hx0

/-- `linkDenom mu0 (Etri 2) 0 1 a = a`. -/
theorem linkDenom_tri_two {a : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) :
    linkDenom mu0 (Etri 2) 0 1 a = a := integral_cornerDenom_tri_two ha ha le_rfl

/-- `linkNumer mu0 (Etri 2) 0 1 a = exp a - 1`. -/
theorem linkNumer_tri_two {a : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) :
    linkNumer mu0 (Etri 2) 0 1 a = Real.exp a - 1 := by
  rw [linkNumer, integral_Iic_mu0 ha
    (fun y => bidII mu0 (Etri 2) 0 1 y * cornerDenom mu0 (Etri 2) 0 1 a y)
    (fun y => Real.exp y) (fun y hy => by
      have hmem : y ∈ Set.Icc (0:ℝ) 1 := ⟨hy.1, le_trans hy.2 ha.2⟩
      dsimp only
      rw [cornerDenom_tri_two_eq_one ha hmem hy.2, bidII_tri_two, if_pos hmem, mul_one]),
    integral_exp]
  simp

/-- The winner's conditional expected payment in closed form:
`expectedPayII mu0 (Etri 2) 0 1 a = (exp a - 1) / a`. -/
theorem expectedPayII_tri_two {a : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) :
    expectedPayII mu0 (Etri 2) 0 1 a = (Real.exp a - 1) / a := by
  rw [expectedPayII, linkNumer_tri_two ha, linkDenom_tri_two ha]

/-- The caller obligation `hbid` of `Affiliated.expectedPayII_mono`, on `Set.Iic x'` for
`x' ≤ x_hi = 1`. -/
theorem monotoneOn_bidII_tri_two {x' : ℝ} (hx' : x' ≤ 1) :
    MonotoneOn (bidII mu0 (Etri 2) 0 1) (Set.Iic x') := by
  intro a ha b hb hab
  rw [bidII_tri_two, bidII_tri_two]
  by_cases h : a ∈ Set.Icc (0:ℝ) 1
  · have hb' : b ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans h.1 hab, le_trans (Set.mem_Iic.1 hb) hx'⟩
    rw [if_pos h, if_pos hb']
    exact Real.exp_le_exp.2 hab
  · rw [if_neg h]
    split
    · exact (Real.exp_pos _).le
    · exact le_rfl

/-- The `IntegrableOn` side conditions on the corner denominator. -/
theorem integrableOn_cornerDenom_tri_two {a c : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1)
    (hc : c ∈ Set.Icc (0:ℝ) 1) (hac : a ≤ c) :
    IntegrableOn (fun y => cornerDenom mu0 (Etri 2) 0 1 c y) (Set.Iic a) mu0 :=
  integrableOn_Iic_mu0 ha (g := fun _ => (1:ℝ)) continuous_const (fun _ hy =>
    (cornerDenom_tri_two_eq_one hc ⟨hy.1, le_trans hy.2 ha.2⟩ (le_trans hy.2 hac)).symm)

/-- The `IntegrableOn` side conditions on the price-weighted corner denominator. -/
theorem integrableOn_bidII_mul_tri_two {a c : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1)
    (hc : c ∈ Set.Icc (0:ℝ) 1) (hac : a ≤ c) :
    IntegrableOn (fun y => bidII mu0 (Etri 2) 0 1 y * cornerDenom mu0 (Etri 2) 0 1 c y)
      (Set.Iic a) mu0 :=
  integrableOn_Iic_mu0 ha (g := fun y => Real.exp y) Real.continuous_exp (fun y hy => by
    have hmem : y ∈ Set.Icc (0:ℝ) 1 := ⟨hy.1, le_trans hy.2 ha.2⟩
    rw [cornerDenom_tri_two_eq_one hc hmem (le_trans hy.2 hac), bidII_tri_two, if_pos hmem,
      mul_one])

/-- **The linkage effect at a strictly affiliated (non-product) density.**
`Affiliated.expectedPayII_mono` instantiated at `Etri 2`, with `hB` discharged by
`hB_tri_two` rather than by factorization. -/
theorem expectedPayII_mono_tri_two {x x' : ℝ} (hx0 : 0 < x) (hxx : x ≤ x') (hx1 : x' ≤ 1) :
    expectedPayII mu0 (Etri 2) 0 1 x ≤ expectedPayII mu0 (Etri 2) 0 1 x' := by
  have hmemx : x ∈ Set.Icc (0:ℝ) 1 := ⟨hx0.le, le_trans hxx hx1⟩
  have hmemx' : x' ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans hx0.le hxx, hx1⟩
  exact (Etri_affiliated 2).expectedPayII_mono 0 1 hxx (monotoneOn_bidII_tri_two hx1)
    (hden_tri_two mu0)
    (integrableOn_cornerDenom_tri_two hmemx hmemx le_rfl)
    (integrableOn_bidII_mul_tri_two hmemx hmemx le_rfl)
    (integrableOn_cornerDenom_tri_two hmemx' hmemx' le_rfl)
    (integrableOn_bidII_mul_tri_two hmemx' hmemx' le_rfl)
    (by rw [linkDenom_tri_two hmemx]; exact hx0)
    (hB_tri_two hx0 hxx hx1)
    (by rw [linkDenom_tri_two hmemx']; exact lt_of_lt_of_le hx0 hxx)

/-- The linkage effect in closed form: `(exp x - 1) / x` is nondecreasing on `(0, 1]`,
obtained by instantiating `Affiliated.expectedPayII_mono` at `Etri 2`. -/
theorem expectedPayII_mono_tri_two_closed {x x' : ℝ} (hx0 : 0 < x) (hxx : x ≤ x')
    (hx1 : x' ≤ 1) :
    (Real.exp x - 1) / x ≤ (Real.exp x' - 1) / x' := by
  have h := expectedPayII_mono_tri_two hx0 hxx hx1
  rwa [expectedPayII_tri_two ⟨hx0.le, le_trans hxx hx1⟩,
    expectedPayII_tri_two ⟨le_trans hx0.le hxx, hx1⟩] at h

/-- The winner's-margin corollary at `Etri 2`: `expectedPayII ≤ bidII`. -/
theorem expectedPayII_le_bidII_tri_two {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    expectedPayII mu0 (Etri 2) 0 1 x ≤ bidII mu0 (Etri 2) 0 1 x :=
  Affiliated.expectedPayII_le_bidII 0 1 (monotoneOn_bidII_tri_two hx1)
    (integrableOn_cornerDenom_tri_two ⟨hx0.le, hx1⟩ ⟨hx0.le, hx1⟩ le_rfl)
    (integrableOn_bidII_mul_tri_two ⟨hx0.le, hx1⟩ ⟨hx0.le, hx1⟩ le_rfl)
    (by rw [linkDenom_tri_two ⟨hx0.le, hx1⟩]; exact hx0)

/-! ## The one-dimensional rival-mass integral

`cap t` is the fibre of the top-rival density in one non-corner coordinate: the box
indicator cut at the level `t` of the top rival. Its mass is `t`, and the `n`-th corner
denominator is the `(n-2)`-nd power of that mass. -/

/-- `cap t u = boxInd u * 1[u ≤ t]`, the fibre of `topDensity` in one non-corner
coordinate. -/
def cap (t : ℝ) : ℝ → ℝ := fun u => boxInd u * (if u ≤ t then (1:ℝ) else 0)

/-- `cap t = (Set.Icc 0 1 ∩ Set.Iic t).indicator 1`. -/
theorem cap_eq_indicator (t : ℝ) :
    cap t = Set.indicator (Set.Icc (0:ℝ) 1 ∩ Set.Iic t) (fun _ => (1:ℝ)) := by
  funext u
  by_cases hu : u ∈ Set.Icc (0:ℝ) 1 ∩ Set.Iic t
  · rw [Set.indicator_of_mem hu, cap, boxInd_eq_one hu.1, if_pos (Set.mem_Iic.1 hu.2)]
    norm_num
  · rw [Set.indicator_of_notMem hu, cap]
    rcases Classical.em (u ∈ Set.Icc (0:ℝ) 1) with h1 | h1
    · rw [if_neg (fun hc => hu ⟨h1, Set.mem_Iic.2 hc⟩), mul_zero]
    · rw [boxInd_eq_zero h1, zero_mul]

/-- `cap t` is `volume`-integrable. -/
theorem cap_integrable (t : ℝ) : Integrable (cap t) volume := by
  rw [cap_eq_indicator]
  refine (integrable_indicator_iff (measurableSet_Icc.inter measurableSet_Iic)).2 ?_
  exact integrableOn_const
    (ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_left) (by simp)))

/-- The rival mass: `∫ u, cap t u = t` for `t` in the box. -/
theorem cap_integral (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : ∫ u, cap t u = t := by
  have hset : Set.Icc (0:ℝ) 1 ∩ Set.Iic t = Set.Icc (0:ℝ) t := by
    ext u; simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic]
    exact ⟨fun ⟨⟨h1, _⟩, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h2⟩ => ⟨⟨h1, h2.trans ht.2⟩, h2⟩⟩
  rw [cap_eq_indicator, hset, MeasureTheory.integral_indicator measurableSet_Icc,
    setIntegral_const, Real.volume_real_Icc_of_le ht.1, sub_zero, smul_eq_mul, mul_one]

/-! ## `n = 3`: the first non-degenerate instantiation

At `n = 3`, `otherRivals 0 1 = [2]`: the corner objects carry one genuine integral, so the
`FibreIntegrable` hypotheses of `Affiliated.bidII_pivotalOptimal` are real integrability
statements and `topDensity` is a proper restriction of `E.f`. -/

/-- `otherRivals (0 : Fin 3) 1 = [2]`. -/
theorem otherRivals_three : otherRivals (0 : Fin 3) 1 = [2] := by
  have hset : (Finset.univ.erase (0 : Fin 3)) = insert 1 ({2} : Finset (Fin 3)) := by decide
  have hsort : rivals (0 : Fin 3) = [1, 2] := by
    rw [rivals, hset,
      Finset.sort_insert (r := (· ≤ ·)) (s := ({2} : Finset (Fin 3))) (by decide) (by decide),
      Finset.sort_singleton]
  rw [otherRivals, hsort]; decide

/-- The single genuine fibre of the `n = 3` corner density:
`topDensity (Ebox 3).f 0 1 (z[2↦u][0↦s][1↦t]) = (boxInd s * boxInd t) * cap t u`. -/
theorem fibre_three (z : Fin 3 → ℝ) (s t u : ℝ) :
    topDensity (Ebox 3).f 0 1
        (Function.update (Function.update (Function.update z 2 u) 0 s) 1 t)
      = (boxInd s * boxInd t) * cap t u := by
  set W := Function.update (Function.update (Function.update z 2 u) 0 s) 1 t with hW
  have hw0 : W 0 = s := by
    rw [hW, Function.update_of_ne (by decide), Function.update_self]
  have hw1 : W 1 = t := by rw [hW, Function.update_self]
  have hw2 : W 2 = u := by
    rw [hW, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self]
  have hdens : (Ebox 3).f W = boxInd s * boxInd t * boxInd u := by
    show unifDens 3 W = _
    rw [unifDens, Fin.prod_univ_three, hw0, hw1, hw2]
  have hmem : W ∈ maxAt (0 : Fin 3) 1 ↔ u ≤ t := by
    constructor
    · intro h; have h2 := h 2 (by decide) (by decide); rwa [hw2, hw1] at h2
    · intro h k hk0 hk1
      fin_cases k
      · exact absurd rfl hk0
      · exact absurd rfl hk1
      · rw [hw1]; simpa [hw2] using h
  by_cases hut : u ≤ t
  · rw [topDensity_of_mem _ _ _ (hmem.2 hut), hdens]
    simp only [cap, if_pos hut]; ring
  · rw [topDensity_of_notMem _ _ _ (fun hc => hut (hmem.1 hc))]
    simp only [cap, if_neg hut]; ring

/-- **The corner denominator at `n = 3`, in closed form**:
`cornerDenom volume (Ebox 3) 0 1 x y = boxInd x * boxInd y * y`. The trailing `y` is the
mass of the one remaining rival below the top rival's signal. -/
theorem cornerDenom_three (x y : ℝ) :
    cornerDenom volume (Ebox 3) 0 1 x y = boxInd x * boxInd y * y := by
  rw [cornerDenom, otherRivals_three]
  simp only [marginalList, marginal]
  simp_rw [fibre_three]
  rw [integral_const_mul]
  by_cases hy : y ∈ Set.Icc (0:ℝ) 1
  · rw [cap_integral y hy]
  · rw [boxInd_eq_zero hy]; ring

/-- The corner numerator at `n = 3`, in closed form. -/
theorem cornerNumer_three (x y : ℝ) :
    cornerNumer volume (Ebox 3) 0 1 x y = Real.exp x * (boxInd x * boxInd y * y) := by
  rw [cornerNumer, otherRivals_three]
  simp only [marginalList, marginal]
  have hv : ∀ u : ℝ, (Ebox 3).v 0
      (Function.update (Function.update (Function.update (0 : Fin 3 → ℝ) 2 u) 0 x) 1 y)
      = Real.exp x := by
    intro u
    show Real.exp _ = _
    rw [Function.update_of_ne (by decide), Function.update_self]
  simp_rw [hv, fibre_three]
  rw [show (fun u : ℝ => Real.exp x * (boxInd x * boxInd y * cap y u))
      = (fun u : ℝ => (Real.exp x * (boxInd x * boxInd y)) * cap y u) from by funext u; ring]
  rw [integral_const_mul]
  by_cases hy : y ∈ Set.Icc (0:ℝ) 1
  · rw [cap_integral y hy]; ring
  · rw [boxInd_eq_zero hy]; ring

/-- The corner conditional value at `n = 3` is the bidder's own value, `exp x`. -/
theorem w_three {x y : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1)
    (hy0 : 0 < y) : w volume (Ebox 3) 0 1 x y = Real.exp x := by
  rw [w, cornerNumer_three, cornerDenom_three, boxInd_eq_one hx, boxInd_eq_one hy]
  field_simp

/-- **The bid-your-value benchmark at `n = 3`, recovered**: on the interior of the box,
`bidII volume (Ebox 3) 0 1 x = exp x`. -/
theorem bidII_three {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) (hx0 : 0 < x) :
    bidII volume (Ebox 3) 0 1 x = Real.exp x := w_three hx hx hx0

/-- **The floor trap.** At `n ≥ 3` the corner denominator degenerates at the bottom of the
box (`cornerDenom volume (Ebox 3) 0 1 0 0 = 0`), so `bidII volume (Ebox 3) 0 1 0 = 0` while
`exp 0 = 1`. Consequently the product `bidII y * cornerDenom x y` does **not** rewrite
pointwise to its naive closed form `exp y * (boxInd x * boxInd y * y)`; the two agree only
after a case split at `y = 0` (where both sides are `0` for the *other* reason). Every
integral over a winning event that reaches the floor has to carry that split. -/
theorem bidII_three_at_zero : bidII volume (Ebox 3) 0 1 0 = 0 := by
  rw [bidII, w, cornerDenom_three, mul_zero, div_zero]

/-- The `hden` hypothesis at `n = 3`: a genuine integrability statement. -/
theorem hden_three : ∀ s t : ℝ, FibreIntegrable volume
    (fun z => topDensity (Ebox 3).f 0 1 (Function.update (Function.update z 0 s) 1 t))
    (otherRivals (0 : Fin 3) 1) := by
  intro s t
  rw [otherRivals_three]
  refine ⟨fun z => ?_, trivial⟩
  simp_rw [fibre_three]
  exact (cap_integrable t).const_mul _

/-- The `hnum` hypothesis at `n = 3`: a genuine integrability statement. -/
theorem hnum_three : ∀ s t : ℝ, FibreIntegrable volume
    (fun z => (Ebox 3).v 0 (Function.update (Function.update z 0 s) 1 t)
      * topDensity (Ebox 3).f 0 1 (Function.update (Function.update z 0 s) 1 t))
    (otherRivals (0 : Fin 3) 1) := by
  intro s t
  rw [otherRivals_three]
  refine ⟨fun z => ?_, trivial⟩
  have hv : ∀ u : ℝ, (Ebox 3).v 0
      (Function.update (Function.update (Function.update z 2 u) 0 s) 1 t) = Real.exp s := by
    intro u
    show Real.exp _ = _
    rw [Function.update_of_ne (by decide), Function.update_self]
  simp_rw [hv, fibre_three]
  rw [show (fun u : ℝ => Real.exp s * (boxInd s * boxInd t * cap t u))
      = (fun u : ℝ => (Real.exp s * (boxInd s * boxInd t)) * cap t u) from by funext u; ring]
  exact (cap_integrable t).const_mul _

/-- The support-regularity hypothesis at `n = 3`. -/
theorem hreg_three (x : ℝ) : ∀ y : ℝ, x < y →
    0 < cornerDenom volume (Ebox 3) 0 1 x y → 0 < cornerDenom volume (Ebox 3) 0 1 y y := by
  intro y _ hpos
  rw [cornerDenom_three] at hpos ⊢
  have hby : boxInd y ≠ 0 := by rintro h; rw [h] at hpos; simp at hpos
  have hy : y ∈ Set.Icc (0:ℝ) 1 :=
    boxInd_pos_iff.1 (lt_of_le_of_ne (boxInd_nonneg y) (Ne.symm hby))
  have hy0 : y ≠ 0 := by rintro h; rw [h] at hpos; simp at hpos
  rw [boxInd_eq_one hy]
  simpa using lt_of_le_of_ne hy.1 (Ne.symm hy0)

/-- **Pivotal optimality of the diagonal bid at `n = 3`**, where `otherRivals 0 1 = [2]` is
nonempty and the `FibreIntegrable` families are genuine integrability statements. -/
theorem pivotalOptimal_three (x : ℝ) :
    ∀ x₂ : ℝ,
      (x ≤ x₂ → pivotalGain (volume : Measure ℝ) (Ebox 3) 0 1 x x x₂ ≤ 0)
      ∧ (x₂ ≤ x → 0 ≤ pivotalGain (volume : Measure ℝ) (Ebox 3) 0 1 x x₂ x) :=
  (Ebox_affiliated 3).bidII_pivotalOptimal 0 1 (hreg_three x) hnum_three hden_three

/-- **The pivotal integrand at `n = 3`, in closed form**: on the box interior,
`cornerNumer x y - bidII y * cornerDenom x y = y * (exp x - exp y)`, manifestly of the sign
of `x - y`. -/
theorem pivotalGain_integrand_three {x y : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1)
    (hy : y ∈ Set.Icc (0:ℝ) 1) (hy0 : 0 < y) :
    cornerNumer volume (Ebox 3) 0 1 x y
        - bidII volume (Ebox 3) 0 1 y * cornerDenom volume (Ebox 3) 0 1 x y
      = y * (Real.exp x - Real.exp y) := by
  rw [cornerNumer_three, cornerDenom_three, bidII_three hy hy0,
    boxInd_eq_one hx, boxInd_eq_one hy]
  ring

/-- `pivotalGain` on the upward shell at `n = 3`, in closed form. -/
theorem pivotalGain_three_closed {x x₂ : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) (hx0 : 0 < x)
    (hx2 : x₂ ∈ Set.Icc (0:ℝ) 1) (hle : x ≤ x₂) :
    pivotalGain volume (Ebox 3) 0 1 x x x₂
      = ∫ y in x..x₂, y * (Real.exp x - Real.exp y) := by
  rw [intervalIntegral.integral_of_le hle, pivotalGain]
  refine setIntegral_congr_fun measurableSet_Ioc (fun y hy => ?_)
  have hyb : y ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt (lt_trans hx0 hy.1), hy.2.trans hx2.2⟩
  exact pivotalGain_integrand_three hx hyb (lt_trans hx0 hy.1)

/-! ## `n = 4`: two nested marginals

At `n = 4`, `otherRivals 0 1 = [2, 3]`, so `cornerDenom` is an iterated integral and
`FibreIntegrable` is a two-stage condition: the head fibres of `topDensity` and the head
fibres of its first marginal. -/

/-- `otherRivals (0 : Fin 4) 1 = [2, 3]`. -/
theorem otherRivals_four : otherRivals (0 : Fin 4) 1 = [2, 3] := by
  have hset : (Finset.univ.erase (0 : Fin 4))
      = insert 1 (insert 2 ({3} : Finset (Fin 4))) := by decide
  have h1 : (insert 2 ({3} : Finset (Fin 4))).sort (· ≤ ·) = [2, 3] := by
    rw [Finset.sort_insert (r := (· ≤ ·)) (s := ({3} : Finset (Fin 4))) (by decide) (by decide),
      Finset.sort_singleton]
  have hsort : rivals (0 : Fin 4) = [1, 2, 3] := by
    rw [rivals, hset,
      Finset.sort_insert (r := (· ≤ ·)) (s := insert 2 ({3} : Finset (Fin 4)))
        (by decide) (by decide), h1]
  rw [otherRivals, hsort]; decide

/-- The fully pinned profile at `n = 4`: coordinates `0 ↦ s`, `1 ↦ t`, `2 ↦ p`, `3 ↦ u`. -/
theorem fibre_four (z : Fin 4 → ℝ) (s t p u : ℝ) :
    topDensity (Ebox 4).f 0 1
        (Function.update (Function.update (Function.update (Function.update z 3 u) 2 p) 0 s) 1 t)
      = (boxInd s * boxInd t) * (cap t p * cap t u) := by
  set W := Function.update (Function.update (Function.update (Function.update z 3 u) 2 p) 0 s) 1 t
    with hW
  have hw0 : W 0 = s := by rw [hW, Function.update_of_ne (by decide), Function.update_self]
  have hw1 : W 1 = t := by rw [hW, Function.update_self]
  have hw2 : W 2 = p := by
    rw [hW, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self]
  have hw3 : W 3 = u := by
    rw [hW, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_self]
  have hdens : (Ebox 4).f W = boxInd s * boxInd t * boxInd p * boxInd u := by
    show unifDens 4 W = _
    rw [unifDens, Fin.prod_univ_four, hw0, hw1, hw2, hw3]
  have hmem : W ∈ maxAt (0 : Fin 4) 1 ↔ (p ≤ t ∧ u ≤ t) := by
    constructor
    · intro h
      exact ⟨by have := h 2 (by decide) (by decide); rwa [hw2, hw1] at this,
             by have := h 3 (by decide) (by decide); rwa [hw3, hw1] at this⟩
    · rintro ⟨h2, h3⟩ k hk0 hk1
      fin_cases k
      · exact absurd rfl hk0
      · exact absurd rfl hk1
      · rw [hw1]; simpa [hw2] using h2
      · rw [hw1]; simpa [hw3] using h3
  by_cases hp : p ≤ t
  · by_cases hu : u ≤ t
    · rw [topDensity_of_mem _ _ _ (hmem.2 ⟨hp, hu⟩), hdens]
      simp only [cap, if_pos hp, if_pos hu]; ring
    · rw [topDensity_of_notMem _ _ _ (fun hc => hu (hmem.1 hc).2)]
      simp only [cap, if_neg hu]; ring
  · rw [topDensity_of_notMem _ _ _ (fun hc => hp (hmem.1 hc).1)]
    simp only [cap, if_neg hp]; ring

/-- The first-stage fibre at `n = 4`, with coordinate `3` left at its base value. -/
theorem fibre_four_stage1 (x : Fin 4 → ℝ) (s t u : ℝ) :
    topDensity (Ebox 4).f 0 1
        (Function.update (Function.update (Function.update x 2 u) 0 s) 1 t)
      = (boxInd s * boxInd t) * (cap t u * cap t (x 3)) := by
  have h : Function.update x 2 u = Function.update (Function.update x 3 (x 3)) 2 u := by
    rw [Function.update_eq_self]
  rw [h, fibre_four]

/-- The `hden` hypothesis at `n = 4`: two integrability stages. -/
theorem hden_four : ∀ s t : ℝ, FibreIntegrable volume
    (fun z => topDensity (Ebox 4).f 0 1 (Function.update (Function.update z 0 s) 1 t))
    (otherRivals (0 : Fin 4) 1) := by
  intro s t
  rw [otherRivals_four]
  refine ⟨fun x => ?_, fun x => ?_, trivial⟩
  · simp_rw [fibre_four_stage1]
    rw [show (fun u : ℝ => boxInd s * boxInd t * (cap t u * cap t (x 3)))
        = (fun u : ℝ => (boxInd s * boxInd t * cap t (x 3)) * cap t u) from by funext u; ring]
    exact (cap_integrable t).const_mul _
  · show Integrable (fun u => marginal volume _ 2 (Function.update x 3 u)) volume
    simp only [marginal]
    simp_rw [fibre_four]
    have h : ∀ u : ℝ, (∫ p, boxInd s * boxInd t * (cap t p * cap t u))
        = ((boxInd s * boxInd t) * ∫ p, cap t p) * cap t u := by
      intro u
      rw [show (fun p : ℝ => boxInd s * boxInd t * (cap t p * cap t u))
          = (fun p : ℝ => (boxInd s * boxInd t * cap t u) * cap t p) from by funext p; ring,
        integral_const_mul]
      ring
    simp_rw [h]
    exact (cap_integrable t).const_mul _

/-- The `hnum` hypothesis at `n = 4`: two integrability stages. -/
theorem hnum_four : ∀ s t : ℝ, FibreIntegrable volume
    (fun z => (Ebox 4).v 0 (Function.update (Function.update z 0 s) 1 t)
      * topDensity (Ebox 4).f 0 1 (Function.update (Function.update z 0 s) 1 t))
    (otherRivals (0 : Fin 4) 1) := by
  intro s t
  rw [otherRivals_four]
  have hv : ∀ (z : Fin 4 → ℝ), (Ebox 4).v 0
      (Function.update (Function.update z 0 s) 1 t) = Real.exp s := by
    intro z
    show Real.exp _ = _
    rw [Function.update_of_ne (by decide), Function.update_self]
  refine ⟨fun x => ?_, fun x => ?_, trivial⟩
  · simp_rw [hv, fibre_four_stage1]
    rw [show (fun u : ℝ => Real.exp s * (boxInd s * boxInd t * (cap t u * cap t (x 3))))
        = (fun u : ℝ => (Real.exp s * (boxInd s * boxInd t) * cap t (x 3)) * cap t u)
        from by funext u; ring]
    exact (cap_integrable t).const_mul _
  · show Integrable (fun u => marginal volume _ 2 (Function.update x 3 u)) volume
    simp only [marginal]
    simp_rw [hv, fibre_four]
    have h : ∀ u : ℝ, (∫ p, Real.exp s * (boxInd s * boxInd t * (cap t p * cap t u)))
        = ((Real.exp s * (boxInd s * boxInd t)) * ∫ p, cap t p) * cap t u := by
      intro u
      rw [show (fun p : ℝ => Real.exp s * (boxInd s * boxInd t * (cap t p * cap t u)))
          = (fun p : ℝ => (Real.exp s * (boxInd s * boxInd t) * cap t u) * cap t p)
          from by funext p; ring, integral_const_mul]
      ring
    simp_rw [h]
    exact (cap_integrable t).const_mul _

/-- **The corner denominator at `n = 4`, in closed form**:
`cornerDenom volume (Ebox 4) 0 1 x y = boxInd x * boxInd y * y ^ 2`. The exponent is the
number of rivals other than the top one: the rival mass `y` raised to the power `n - 2`. -/
theorem cornerDenom_four (x y : ℝ) :
    cornerDenom volume (Ebox 4) 0 1 x y = boxInd x * boxInd y * y ^ 2 := by
  rw [cornerDenom, otherRivals_four]
  simp only [marginalList, marginal]
  simp_rw [fibre_four]
  have hin : ∀ u : ℝ, (∫ p, boxInd x * boxInd y * (cap y p * cap y u))
      = ((boxInd x * boxInd y) * ∫ p, cap y p) * cap y u := by
    intro u
    rw [show (fun p : ℝ => boxInd x * boxInd y * (cap y p * cap y u))
        = (fun p : ℝ => (boxInd x * boxInd y * cap y u) * cap y p) from by funext p; ring,
      integral_const_mul]
    ring
  simp_rw [hin]
  rw [integral_const_mul]
  by_cases hy : y ∈ Set.Icc (0:ℝ) 1
  · rw [cap_integral y hy]; ring
  · rw [boxInd_eq_zero hy]; ring

/-- The support-regularity hypothesis at `n = 4`. -/
theorem hreg_four (x : ℝ) : ∀ y : ℝ, x < y →
    0 < cornerDenom volume (Ebox 4) 0 1 x y → 0 < cornerDenom volume (Ebox 4) 0 1 y y := by
  intro y _ hpos
  rw [cornerDenom_four] at hpos ⊢
  have hby : boxInd y ≠ 0 := by rintro h; rw [h] at hpos; simp at hpos
  have hy : y ∈ Set.Icc (0:ℝ) 1 :=
    boxInd_pos_iff.1 (lt_of_le_of_ne (boxInd_nonneg y) (Ne.symm hby))
  have hy0 : y ≠ 0 := by rintro h; rw [h] at hpos; simp at hpos
  rw [boxInd_eq_one hy, one_mul, one_mul]
  exact pow_pos (lt_of_le_of_ne hy.1 (Ne.symm hy0)) 2

/-- **Pivotal optimality of the diagonal bid at `n = 4`**: the coordinate list `[2, 3]` is
marginalized twice. -/
theorem pivotalOptimal_four (x : ℝ) :
    ∀ x₂ : ℝ,
      (x ≤ x₂ → pivotalGain (volume : Measure ℝ) (Ebox 4) 0 1 x x x₂ ≤ 0)
      ∧ (x₂ ≤ x → 0 ≤ pivotalGain (volume : Measure ℝ) (Ebox 4) 0 1 x x₂ x) :=
  (Ebox_affiliated 4).bidII_pivotalOptimal 0 1 (hreg_four x) hnum_four hden_four

/-! ## A strictly affiliated environment at `n = 3`

`Etri` couples the two corner coordinates `0` and `1` directly, which is the only option at
`n = 2` but has a side effect: `cornerDenom μ (Etri 2) 0 1 x y = 0` for `y > x`, so the
upward half of `pivotalOptimal_tri_two` is a statement about a null region. From `n = 3` on
one can put the sublattice constraint between coordinate `0` and a **non-corner**
coordinate, `{z | z 2 ≤ z 0}`. The density is still not a product, affiliation is still
strict, and now nothing degenerates: `cornerDenom mu0 Elow 0 1 x y = min x y` is positive on
both sides of the diagonal, and the corner denominator genuinely mixes `x` and `y`. -/

/-- The sublattice `{z | z 2 ≤ z 0}` of `Fin 3 → ℝ`, coupling the bidder's own coordinate to
a non-corner one. -/
def lowSet : Set (Fin 3 → ℝ) := {z | z 2 ≤ z 0}

/-- `IsSublattice lowSet`. -/
theorem isSublattice_lowSet : IsSublattice lowSet where
  supClosed x hx y hy := by
    simp only [lowSet, Set.mem_setOf_eq, Pi.sup_apply] at *
    exact sup_le_sup hx hy
  infClosed x hx y hy := by
    simp only [lowSet, Set.mem_setOf_eq, Pi.inf_apply] at *
    exact inf_le_inf hx hy

/-- The uniform box density on `[0,1]³` restricted to `lowSet`. -/
def lowDens : (Fin 3 → ℝ) → ℝ := fun X => (∏ k, boxInd (X k)) * lowSet.indicator 1 X

/-- The strictly affiliated, non-degenerate environment at `n = 3`. -/
def Elow : SignalValueEnv 3 where
  x_lo := 0
  x_hi := 1
  x_lo_le_hi := by norm_num
  f := lowDens
  f_nonneg := fun X => mul_nonneg (Finset.prod_nonneg fun _ _ => boxInd_nonneg _)
    (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  f_support := by
    rintro X ⟨i, hi⟩
    have h : (∏ k, boxInd (X k)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (boxInd_eq_zero hi)
    simp [lowDens, h]
  v := expVal 3
  v_nonneg := fun i X => (Real.exp_pos _).le
  v_continuous := fun i => Real.continuous_exp.comp (continuous_apply i)
  v_mono := fun i X Y h => Real.exp_le_exp.2 (h i)
  v_strictMono_own := fun i _ a b hab => by
    simp only [expVal, Function.update_self]; exact Real.exp_lt_exp.2 hab

/-- `Affiliated Elow.f`. -/
theorem Elow_affiliated : Affiliated Elow.f :=
  (factors_affiliated (g := fun _ => boxInd) (fun _ => rfl)).mul
    (affiliated_indicator_of_isSublattice isSublattice_lowSet)
    (fun _ => Finset.prod_nonneg fun _ _ => boxInd_nonneg _)
    (indicator_one_nonneg _)

/-- The affiliation inequality holds **strictly** for `Elow` at
`x = (0.6, 0.5, 0.2)`, `y = (0.2, 0.5, 0.6)`: `f x * f y = 0 < 1 = f (x ⊔ y) * f (x ⊓ y)`. -/
theorem Elow_strictly_affiliated :
    lowDens ![0.6, 0.5, 0.2] * lowDens ![0.2, 0.5, 0.6]
      < lowDens (![(0.6:ℝ), 0.5, 0.2] ⊔ ![(0.2:ℝ), 0.5, 0.6])
        * lowDens (![(0.6:ℝ), 0.5, 0.2] ⊓ ![(0.2:ℝ), 0.5, 0.6]) := by
  have hb : lowDens ![(0.2:ℝ), 0.5, 0.6] = 0 := by
    simp [lowDens, lowSet]
    norm_num
  rw [hb, mul_zero]
  have hsup : (![(0.6:ℝ), 0.5, 0.2] ⊔ ![(0.2:ℝ), 0.5, 0.6]) = ![(0.6:ℝ), 0.5, 0.6] := by
    funext k; fin_cases k <;> simp [Pi.sup_apply] <;> norm_num
  have hinf : (![(0.6:ℝ), 0.5, 0.2] ⊓ ![(0.2:ℝ), 0.5, 0.6]) = ![(0.2:ℝ), 0.5, 0.2] := by
    funext k; fin_cases k <;> simp [Pi.inf_apply] <;> norm_num
  rw [hsup, hinf]
  have h1 : lowDens ![(0.6:ℝ), 0.5, 0.6] = 1 := by
    simp [lowDens, lowSet, Fin.prod_univ_three, boxInd]
    norm_num
  have h2 : lowDens ![(0.2:ℝ), 0.5, 0.2] = 1 := by
    simp [lowDens, lowSet, Fin.prod_univ_three, boxInd]
    norm_num
  rw [h1, h2]; norm_num

/-- `(Set.Icc 0 1).indicator (cap t) = cap t`. -/
theorem indicator_cap (t : ℝ) : Set.indicator (Set.Icc (0:ℝ) 1) (cap t) = cap t := by
  funext u
  by_cases hu : u ∈ Set.Icc (0:ℝ) 1
  · rw [Set.indicator_of_mem hu]
  · rw [Set.indicator_of_notMem hu, cap, boxInd_eq_zero hu, zero_mul]

/-- `cap t` is `mu0`-integrable. -/
theorem cap_integrable_mu0 (t : ℝ) : Integrable (cap t) mu0 := by
  rw [mu0]; exact (cap_integrable t).restrict

/-- The rival mass under `mu0`: `∫ u, cap t u ∂mu0 = t` for `t` in the box. -/
theorem cap_integral_mu0 {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : ∫ u, cap t u ∂mu0 = t := by
  rw [mu0, ← MeasureTheory.integral_indicator measurableSet_Icc, indicator_cap,
    cap_integral t ht]

/-- The genuine fibre of `Elow`: the non-corner coordinate is capped by **both** the top
rival's signal and the bidder's own signal. -/
theorem fibre_low (z : Fin 3 → ℝ) (s t u : ℝ) :
    topDensity Elow.f 0 1
        (Function.update (Function.update (Function.update z 2 u) 0 s) 1 t)
      = (boxInd s * boxInd t) * cap (min s t) u := by
  set W := Function.update (Function.update (Function.update z 2 u) 0 s) 1 t with hW
  have hw0 : W 0 = s := by
    rw [hW, Function.update_of_ne (by decide), Function.update_self]
  have hw1 : W 1 = t := by rw [hW, Function.update_self]
  have hw2 : W 2 = u := by
    rw [hW, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self]
  have hmemlow : W ∈ lowSet ↔ u ≤ s := by
    show W 2 ≤ W 0 ↔ u ≤ s
    rw [hw0, hw2]
  have hlow : lowSet.indicator (1 : (Fin 3 → ℝ) → ℝ) W = if u ≤ s then (1:ℝ) else 0 := by
    by_cases h : u ≤ s
    · rw [Set.indicator_of_mem (hmemlow.2 h), if_pos h]; rfl
    · rw [Set.indicator_of_notMem (fun hc => h (hmemlow.1 hc)), if_neg h]
  have hdens : Elow.f W = boxInd s * boxInd t * boxInd u * (if u ≤ s then (1:ℝ) else 0) := by
    show lowDens W = _
    rw [lowDens, Fin.prod_univ_three, hw0, hw1, hw2, hlow]
  have hmem : W ∈ maxAt (0 : Fin 3) 1 ↔ u ≤ t := by
    constructor
    · intro h; have h2 := h 2 (by decide) (by decide); rwa [hw2, hw1] at h2
    · intro h k hk0 hk1
      fin_cases k
      · exact absurd rfl hk0
      · exact absurd rfl hk1
      · rw [hw1]; simpa [hw2] using h
  by_cases hut : u ≤ t
  · rw [topDensity_of_mem _ _ _ (hmem.2 hut), hdens]
    by_cases hus : u ≤ s
    · rw [if_pos hus]
      simp only [cap, if_pos (le_min hus hut)]; ring
    · rw [if_neg hus]
      simp only [cap, if_neg (fun hc => hus (le_trans hc (min_le_left s t)))]; ring
  · rw [topDensity_of_notMem _ _ _ (fun hc => hut (hmem.1 hc))]
    simp only [cap, if_neg (fun hc => hut (le_trans hc (min_le_right s t)))]; ring

/-- The corner denominator of `Elow`, before evaluating the rival-mass integral. -/
theorem cornerDenom_low_gen (x y : ℝ) :
    cornerDenom mu0 Elow 0 1 x y = (boxInd x * boxInd y) * ∫ u, cap (min x y) u ∂mu0 := by
  rw [cornerDenom, otherRivals_three]
  simp only [marginalList, marginal]
  simp_rw [fibre_low]
  rw [integral_const_mul]

/-- **The corner denominator of `Elow`, in closed form**: on the box it is `min x y`. This
does not factor as a function of `x` times a function of `y` — the hypothesis `hB` of
`Affiliated.expectedPayII_mono` therefore has content here. -/
theorem cornerDenom_low {x y : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1) :
    cornerDenom mu0 Elow 0 1 x y = min x y := by
  rw [cornerDenom_low_gen,
    cap_integral_mu0 (⟨le_min hx.1 hy.1, le_trans (min_le_left x y) hx.2⟩ :
      min x y ∈ Set.Icc (0:ℝ) 1), boxInd_eq_one hx, boxInd_eq_one hy]
  ring

/-- The diagonal corner denominator of `Elow`. -/
theorem cornerDenom_low_diag (x : ℝ) :
    cornerDenom mu0 Elow 0 1 x x = if x ∈ Set.Icc (0:ℝ) 1 then x else 0 := by
  by_cases hx : x ∈ Set.Icc (0:ℝ) 1
  · rw [if_pos hx, cornerDenom_low hx hx, min_self]
  · rw [if_neg hx, cornerDenom_low_gen, boxInd_eq_zero hx]; ring

/-- The corner numerator of `Elow` is `exp x` times its corner denominator. -/
theorem cornerNumer_low (x y : ℝ) :
    cornerNumer mu0 Elow 0 1 x y = Real.exp x * cornerDenom mu0 Elow 0 1 x y := by
  rw [cornerNumer, cornerDenom, otherRivals_three]
  simp only [marginalList, marginal]
  have hv : ∀ u : ℝ, Elow.v 0
      (Function.update (Function.update (Function.update (0 : Fin 3 → ℝ) 2 u) 0 x) 1 y)
      = Real.exp x := by
    intro u
    show Real.exp _ = _
    rw [Function.update_of_ne (by decide), Function.update_self]
  simp_rw [hv]
  rw [integral_const_mul]

/-- **The bid-your-value benchmark at the strictly affiliated `Elow`, recovered**:
`bidII mu0 Elow 0 1 x = exp x` on `(0, 1]`, and `0` elsewhere. -/
theorem bidII_low (x : ℝ) :
    bidII mu0 Elow 0 1 x = if x ∈ Set.Ioc (0:ℝ) 1 then Real.exp x else 0 := by
  by_cases h : x ∈ Set.Ioc (0:ℝ) 1
  · have hm : x ∈ Set.Icc (0:ℝ) 1 := ⟨h.1.le, h.2⟩
    rw [if_pos h, bidII, w, cornerNumer_low, cornerDenom_low_diag, if_pos hm, mul_div_assoc,
      div_self (ne_of_gt h.1), mul_one]
  · rw [if_neg h, bidII, w, cornerNumer_low, cornerDenom_low_diag]
    by_cases hm : x ∈ Set.Icc (0:ℝ) 1
    · have hx0 : x = 0 := le_antisymm (not_lt.1 (fun hp => h ⟨hp, hm.2⟩)) hm.1
      rw [if_pos hm, hx0]; simp
    · rw [if_neg hm]; simp

/-- The `hden` hypothesis at `Elow`. -/
theorem hden_low : ∀ s t : ℝ, FibreIntegrable mu0
    (fun z => topDensity Elow.f 0 1 (Function.update (Function.update z 0 s) 1 t))
    (otherRivals (0 : Fin 3) 1) := by
  intro s t
  rw [otherRivals_three]
  refine ⟨fun z => ?_, trivial⟩
  simp_rw [fibre_low]
  exact (cap_integrable_mu0 (min s t)).const_mul _

/-- The `hnum` hypothesis at `Elow`. -/
theorem hnum_low : ∀ s t : ℝ, FibreIntegrable mu0
    (fun z => Elow.v 0 (Function.update (Function.update z 0 s) 1 t)
      * topDensity Elow.f 0 1 (Function.update (Function.update z 0 s) 1 t))
    (otherRivals (0 : Fin 3) 1) := by
  intro s t
  rw [otherRivals_three]
  refine ⟨fun z => ?_, trivial⟩
  have hv : ∀ u : ℝ, Elow.v 0
      (Function.update (Function.update (Function.update z 2 u) 0 s) 1 t) = Real.exp s := by
    intro u
    show Real.exp _ = _
    rw [Function.update_of_ne (by decide), Function.update_self]
  simp_rw [hv, fibre_low]
  rw [show (fun u : ℝ => Real.exp s * (boxInd s * boxInd t * cap (min s t) u))
      = (fun u : ℝ => (Real.exp s * (boxInd s * boxInd t)) * cap (min s t) u)
      from by funext u; ring]
  exact (cap_integrable_mu0 (min s t)).const_mul _

/-- The support-regularity hypothesis at `Elow`. Unlike at `Etri 2`, this is not vacuous:
the corner denominator is positive above the diagonal too. -/
theorem hreg_low (x : ℝ) : ∀ y : ℝ, x < y →
    0 < cornerDenom mu0 Elow 0 1 x y → 0 < cornerDenom mu0 Elow 0 1 y y := by
  intro y _ hpos
  have hbx : boxInd x ≠ 0 := by
    rintro h; rw [cornerDenom_low_gen, h] at hpos; simp at hpos
  have hby : boxInd y ≠ 0 := by
    rintro h; rw [cornerDenom_low_gen, h] at hpos; simp at hpos
  have hx : x ∈ Set.Icc (0:ℝ) 1 :=
    boxInd_pos_iff.1 (lt_of_le_of_ne (boxInd_nonneg x) (Ne.symm hbx))
  have hy : y ∈ Set.Icc (0:ℝ) 1 :=
    boxInd_pos_iff.1 (lt_of_le_of_ne (boxInd_nonneg y) (Ne.symm hby))
  rw [cornerDenom_low hx hy] at hpos
  rw [cornerDenom_low hy hy, min_self]
  exact lt_of_lt_of_le hpos (min_le_right x y)

/-- **Pivotal optimality of the diagonal bid at a strictly affiliated, non-degenerate
environment**: `n = 3`, non-product density, corner denominator positive on both sides of
the diagonal. -/
theorem pivotalOptimal_low (x : ℝ) :
    ∀ x₂ : ℝ,
      (x ≤ x₂ → pivotalGain mu0 Elow 0 1 x x x₂ ≤ 0)
      ∧ (x₂ ≤ x → 0 ≤ pivotalGain mu0 Elow 0 1 x x₂ x) :=
  Elow_affiliated.bidII_pivotalOptimal 0 1 (hreg_low x) hnum_low hden_low

/-! ### The linkage effect at `Elow`, with `hB` genuinely non-product -/

/-- `∫ y in (0:ℝ)..a, y * exp y = (a - 1) * exp a + 1`. -/
theorem integral_mul_exp (a : ℝ) :
    ∫ y in (0:ℝ)..a, y * Real.exp y = (a - 1) * Real.exp a + 1 := by
  have hd : ∀ y ∈ Set.uIcc (0:ℝ) a,
      HasDerivAt (fun t => (t - 1) * Real.exp t) (y * Real.exp y) y := by
    intro y _
    have h := ((hasDerivAt_id y).sub_const 1).mul (Real.hasDerivAt_exp y)
    convert h using 1
    simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuous_id.mul Real.continuous_exp).intervalIntegrable _ _)]
  simp

/-- `∫ y in Set.Iic a, cornerDenom mu0 Elow 0 1 c y ∂mu0 = a ^ 2 / 2` whenever `a ≤ c` in
the box. Taking `c = a` gives `linkDenom`; taking `c = x'`, `a = x` gives `hB`. The step that
does the work is `min c y = y` for `y ≤ a ≤ c`, which is exactly the mixed dependence a
product density does not have. -/
theorem integral_cornerDenom_low {a c : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1)
    (hc : c ∈ Set.Icc (0:ℝ) 1) (hac : a ≤ c) :
    ∫ y in Set.Iic a, cornerDenom mu0 Elow 0 1 c y ∂mu0 = a ^ 2 / 2 := by
  rw [integral_Iic_mu0 ha (fun y => cornerDenom mu0 Elow 0 1 c y) (fun y => y)
    (fun y hy => by
      dsimp only
      rw [cornerDenom_low hc ⟨hy.1, le_trans hy.2 ha.2⟩,
        min_eq_right (le_trans hy.2 hac)]),
    integral_id]
  ring

/-- **The `hB` hypothesis of `Affiliated.expectedPayII_mono`, discharged at a non-product
density with genuinely mixed corner dependence.** -/
theorem hB_low {x x' : ℝ} (hx0 : 0 < x) (hxx : x ≤ x') (hx1 : x' ≤ 1) :
    0 < ∫ y in Set.Iic x, cornerDenom mu0 Elow 0 1 x' y ∂mu0 := by
  rw [integral_cornerDenom_low ⟨hx0.le, le_trans hxx hx1⟩ ⟨le_trans hx0.le hxx, hx1⟩ hxx]
  exact div_pos (pow_pos hx0 2) two_pos

/-- `linkDenom mu0 Elow 0 1 a = a ^ 2 / 2`. -/
theorem linkDenom_low {a : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) :
    linkDenom mu0 Elow 0 1 a = a ^ 2 / 2 := integral_cornerDenom_low ha ha le_rfl

/-- `linkNumer mu0 Elow 0 1 a = (a - 1) * exp a + 1`. The case split at `y = 0` is the floor
trap: `bidII` is `0` there while `exp 0 = 1`. -/
theorem linkNumer_low {a : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) :
    linkNumer mu0 Elow 0 1 a = (a - 1) * Real.exp a + 1 := by
  rw [linkNumer, integral_Iic_mu0 ha
    (fun y => bidII mu0 Elow 0 1 y * cornerDenom mu0 Elow 0 1 a y)
    (fun y => y * Real.exp y) (fun y hy => by
      have hmem : y ∈ Set.Icc (0:ℝ) 1 := ⟨hy.1, le_trans hy.2 ha.2⟩
      dsimp only
      rw [cornerDenom_low ha hmem, min_eq_right hy.2, bidII_low]
      by_cases h : y ∈ Set.Ioc (0:ℝ) 1
      · rw [if_pos h]; ring
      · rw [if_neg h]
        have hy0 : y = 0 := le_antisymm (not_lt.1 (fun hp => h ⟨hp, hmem.2⟩)) hmem.1
        rw [hy0]; simp),
    integral_mul_exp a]

/-- The winner's conditional expected payment at `Elow`, in closed form. -/
theorem expectedPayII_low {a : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1) :
    expectedPayII mu0 Elow 0 1 a = ((a - 1) * Real.exp a + 1) / (a ^ 2 / 2) := by
  rw [expectedPayII, linkNumer_low ha, linkDenom_low ha]

/-- The caller obligation `hbid` at `Elow`, on `Set.Iic x'` for `x' ≤ x_hi = 1`. -/
theorem monotoneOn_bidII_low {x' : ℝ} (hx' : x' ≤ 1) :
    MonotoneOn (bidII mu0 Elow 0 1) (Set.Iic x') := by
  intro a ha b hb hab
  rw [bidII_low, bidII_low]
  by_cases h : a ∈ Set.Ioc (0:ℝ) 1
  · have hb' : b ∈ Set.Ioc (0:ℝ) 1 := ⟨lt_of_lt_of_le h.1 hab, le_trans (Set.mem_Iic.1 hb) hx'⟩
    rw [if_pos h, if_pos hb']; exact Real.exp_le_exp.2 hab
  · rw [if_neg h]
    split
    · exact (Real.exp_pos _).le
    · exact le_rfl

/-- The `IntegrableOn` side conditions on the corner denominator at `Elow`. -/
theorem integrableOn_cornerDenom_low {a c : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1)
    (hc : c ∈ Set.Icc (0:ℝ) 1) (hac : a ≤ c) :
    IntegrableOn (fun y => cornerDenom mu0 Elow 0 1 c y) (Set.Iic a) mu0 :=
  integrableOn_Iic_mu0 ha (g := fun y => y) continuous_id (fun y hy => by
    dsimp only
    rw [cornerDenom_low hc ⟨hy.1, le_trans hy.2 ha.2⟩, min_eq_right (le_trans hy.2 hac)])

/-- The `IntegrableOn` side conditions on the price-weighted corner denominator at `Elow`. -/
theorem integrableOn_bidII_mul_low {a c : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1)
    (hc : c ∈ Set.Icc (0:ℝ) 1) (hac : a ≤ c) :
    IntegrableOn (fun y => bidII mu0 Elow 0 1 y * cornerDenom mu0 Elow 0 1 c y)
      (Set.Iic a) mu0 :=
  integrableOn_Iic_mu0 ha (g := fun y => y * Real.exp y)
    (continuous_id.mul Real.continuous_exp) (fun y hy => by
      have hmem : y ∈ Set.Icc (0:ℝ) 1 := ⟨hy.1, le_trans hy.2 ha.2⟩
      dsimp only
      rw [cornerDenom_low hc hmem, min_eq_right (le_trans hy.2 hac), bidII_low]
      by_cases h : y ∈ Set.Ioc (0:ℝ) 1
      · rw [if_pos h]; ring
      · rw [if_neg h]
        have hy0 : y = 0 := le_antisymm (not_lt.1 (fun hp => h ⟨hp, hmem.2⟩)) hmem.1
        rw [hy0]; simp)

/-- **The linkage effect at a strictly affiliated, non-degenerate environment.**
`Affiliated.expectedPayII_mono` instantiated at `Elow`, `n = 3`, with `hB` discharged by
`hB_low`. -/
theorem expectedPayII_mono_low {x x' : ℝ} (hx0 : 0 < x) (hxx : x ≤ x') (hx1 : x' ≤ 1) :
    expectedPayII mu0 Elow 0 1 x ≤ expectedPayII mu0 Elow 0 1 x' := by
  have hmemx : x ∈ Set.Icc (0:ℝ) 1 := ⟨hx0.le, le_trans hxx hx1⟩
  have hmemx' : x' ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans hx0.le hxx, hx1⟩
  exact Elow_affiliated.expectedPayII_mono 0 1 hxx (monotoneOn_bidII_low hx1) hden_low
    (integrableOn_cornerDenom_low hmemx hmemx le_rfl)
    (integrableOn_bidII_mul_low hmemx hmemx le_rfl)
    (integrableOn_cornerDenom_low hmemx' hmemx' le_rfl)
    (integrableOn_bidII_mul_low hmemx' hmemx' le_rfl)
    (by rw [linkDenom_low hmemx]; exact div_pos (pow_pos hx0 2) two_pos)
    (hB_low hx0 hxx hx1)
    (by rw [linkDenom_low hmemx']
        exact div_pos (pow_pos (lt_of_lt_of_le hx0 hxx) 2) two_pos)

/-- The linkage effect at `Elow` in closed form. -/
theorem expectedPayII_mono_low_closed {x x' : ℝ} (hx0 : 0 < x) (hxx : x ≤ x') (hx1 : x' ≤ 1) :
    ((x - 1) * Real.exp x + 1) / (x ^ 2 / 2)
      ≤ ((x' - 1) * Real.exp x' + 1) / (x' ^ 2 / 2) := by
  have h := expectedPayII_mono_low hx0 hxx hx1
  rwa [expectedPayII_low ⟨hx0.le, le_trans hxx hx1⟩,
    expectedPayII_low ⟨le_trans hx0.le hxx, hx1⟩] at h

/-- The library's own discharge route for `hbid`: `Affiliated.monotoneOn_bidII` reaches the
set on which the corner denominator is positive at every pair of points, which at `Elow` is
`Set.Ioc 0 1`. The closed box is out of reach, since `cornerDenom mu0 Elow 0 1 x 0 = 0`. -/
theorem monotoneOn_bidII_low_lib : MonotoneOn (bidII mu0 Elow 0 1) (Set.Ioc (0:ℝ) 1) :=
  Elow_affiliated.monotoneOn_bidII 0 1 (by decide) hnum_low hden_low
    (fun s hs t ht => by
      rw [cornerDenom_low ⟨hs.1.le, hs.2⟩ ⟨ht.1.le, ht.2⟩]
      exact lt_min hs.1 ht.1)

/-- The caller obligation `hbid` on `Set.Iic x'` is not merely unproved above the signal box
but false there: `bidII` returns to `0` past `E.x_hi = 1`. -/
theorem bidII_low_not_monotoneOn_above {x' : ℝ} (hx' : 1 < x') :
    ¬ MonotoneOn (bidII mu0 Elow 0 1) (Set.Iic x') := by
  intro h
  have key := h (Set.mem_Iic.2 hx'.le) (Set.mem_Iic.2 le_rfl) hx'.le
  rw [bidII_low, bidII_low, if_pos (by norm_num : (1:ℝ) ∈ Set.Ioc (0:ℝ) 1),
    if_neg (fun hc => absurd hc.2 (not_le.2 hx'))] at key
  linarith [Real.exp_pos (1:ℝ)]

/-- The winner's-margin corollary at `Elow`. -/
theorem expectedPayII_le_bidII_low {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    expectedPayII mu0 Elow 0 1 x ≤ bidII mu0 Elow 0 1 x :=
  Affiliated.expectedPayII_le_bidII 0 1 (monotoneOn_bidII_low hx1)
    (integrableOn_cornerDenom_low ⟨hx0.le, hx1⟩ ⟨hx0.le, hx1⟩ le_rfl)
    (integrableOn_bidII_mul_low ⟨hx0.le, hx1⟩ ⟨hx0.le, hx1⟩ le_rfl)
    (by rw [linkDenom_low ⟨hx0.le, hx1⟩]; exact div_pos (pow_pos hx0 2) two_pos)

/-! ## Log-supermodularity, localized to where the density is positive

`affiliated_iff_logSupermodular` assumes `∀ x, 0 < f x`, which no `SignalValueEnv` density
satisfies (`SignalValueEnv.not_forall_f_pos`): `f_support` kills the density off the signal
box. The localized `affiliatedOn_iff_logSupermodularOn` assumes positivity only on a
sublattice `S`, and every density in this file is positive on a sublattice — the signal box
for `Ebox` and `Ecoup`, the box met with the constraint triangle for `Etri` and `Elow`.
Those instantiations are below.

`Ebox`, `Etri` and `Elow` are constant (equal to `1`) on the sublattice where they are
positive, so for them the localized inequality holds with equality: the statement applies,
but says nothing sharp. `Ecoup` is added precisely to remove that caveat — its log is
`X₀ X₁` on the box, non-constant, and the inequality is strict at an exhibited pair
(`logSupermodularOn_Ecoup_two_strict`). -/

/-- On the signal box every factor of `unifDens` is `1`, so `(Ebox n).f = 1` there. -/
theorem Ebox_f_eq_one_of_mem_signalBox {n : ℕ} {x : Fin n → ℝ}
    (hx : x ∈ (Ebox n).signalBox) : (Ebox n).f x = 1 := by
  have hx' : ∀ k, x k ∈ Set.Icc (0:ℝ) 1 := fun k => ((Ebox n).mem_signalBox_iff x).1 hx k
  show (∏ k, boxInd (x k)) = 1
  exact Finset.prod_eq_one fun k _ => boxInd_eq_one (hx' k)

/-- `0 < (Ebox n).f x` for `x` in the signal box: the positivity hypothesis of
`affiliatedOn_signalBox_iff_logSupermodularOn`, which the global
`affiliated_iff_logSupermodular` asks for everywhere and therefore cannot get. -/
theorem Ebox_f_pos_of_mem_signalBox {n : ℕ} {x : Fin n → ℝ}
    (hx : x ∈ (Ebox n).signalBox) : 0 < (Ebox n).f x := by
  rw [Ebox_f_eq_one_of_mem_signalBox hx]; norm_num

/-- **The localized characterization applied to `Ebox n`.** `log ∘ (Ebox n).f` is
supermodular on the signal box `{x | ∀ k, x k ∈ Set.Icc 0 1}`, obtained from
`Ebox_affiliated` through `affiliatedOn_signalBox_iff_logSupermodularOn`. -/
theorem logSupermodularOn_signalBox_Ebox (n : ℕ) :
    ∀ x ∈ (Ebox n).signalBox, ∀ y ∈ (Ebox n).signalBox,
      Real.log ((Ebox n).f x) + Real.log ((Ebox n).f y) ≤
        Real.log ((Ebox n).f (x ⊔ y)) + Real.log ((Ebox n).f (x ⊓ y)) :=
  (affiliatedOn_signalBox_iff_logSupermodularOn (Ebox n)
      (fun _ hx => Ebox_f_pos_of_mem_signalBox hx)).1
    ((Ebox_affiliated n).affiliatedOn _)

/-- The positive part of `Etri n` is the signal box met with the constraint triangle, and
it is a sublattice: an intersection of two sublattices. -/
theorem isSublattice_signalBox_inter_triSet (n : ℕ) [NeZero n] :
    IsSublattice ((Etri n).signalBox ∩ triSet n) :=
  (Etri n).isSublattice_signalBox.inter (isSublattice_triSet n)

/-- `(Etri n).f = 1` on the box met with the triangle. -/
theorem Etri_f_eq_one_of_mem {n : ℕ} [NeZero n] {x : Fin n → ℝ}
    (hx : x ∈ (Etri n).signalBox ∩ triSet n) : (Etri n).f x = 1 := by
  have hx' : ∀ k, x k ∈ Set.Icc (0:ℝ) 1 :=
    fun k => ((Etri n).mem_signalBox_iff x).1 hx.1 k
  show (∏ k, boxInd (x k)) * (triSet n).indicator 1 x = 1
  rw [Finset.prod_eq_one fun k _ => boxInd_eq_one (hx' k), Set.indicator_of_mem hx.2]
  simp

/-- **The localized characterization applied to `Etri n`**, on the sublattice where the
density is positive. The signal box alone will not do: `(Etri n).f` vanishes on the part of
the box above the diagonal. -/
theorem logSupermodularOn_Etri (n : ℕ) [NeZero n] :
    ∀ x ∈ (Etri n).signalBox ∩ triSet n, ∀ y ∈ (Etri n).signalBox ∩ triSet n,
      Real.log ((Etri n).f x) + Real.log ((Etri n).f y) ≤
        Real.log ((Etri n).f (x ⊔ y)) + Real.log ((Etri n).f (x ⊓ y)) :=
  (affiliatedOn_iff_logSupermodularOn (isSublattice_signalBox_inter_triSet n)
      (fun _ hx => by rw [Etri_f_eq_one_of_mem hx]; norm_num)).1
    ((Etri_affiliated n).affiliatedOn _)

/-- The positive part of `Elow` is the signal box met with `lowSet`, again a sublattice. -/
theorem isSublattice_signalBox_inter_lowSet :
    IsSublattice (Elow.signalBox ∩ lowSet) :=
  Elow.isSublattice_signalBox.inter isSublattice_lowSet

/-- `Elow.f = 1` on the box met with `lowSet`. -/
theorem Elow_f_eq_one_of_mem {x : Fin 3 → ℝ} (hx : x ∈ Elow.signalBox ∩ lowSet) :
    Elow.f x = 1 := by
  have hx' : ∀ k, x k ∈ Set.Icc (0:ℝ) 1 := fun k => (Elow.mem_signalBox_iff x).1 hx.1 k
  show (∏ k, boxInd (x k)) * lowSet.indicator 1 x = 1
  rw [Finset.prod_eq_one fun k _ => boxInd_eq_one (hx' k), Set.indicator_of_mem hx.2]
  simp

/-- **The localized characterization applied to `Elow`**, the strictly affiliated,
non-degenerate `n = 3` environment. -/
theorem logSupermodularOn_Elow :
    ∀ x ∈ Elow.signalBox ∩ lowSet, ∀ y ∈ Elow.signalBox ∩ lowSet,
      Real.log (Elow.f x) + Real.log (Elow.f y) ≤
        Real.log (Elow.f (x ⊔ y)) + Real.log (Elow.f (x ⊓ y)) :=
  (affiliatedOn_iff_logSupermodularOn isSublattice_signalBox_inter_lowSet
      (fun _ hx => by rw [Elow_f_eq_one_of_mem hx]; norm_num)).1
    (Elow_affiliated.affiliatedOn _)

/-! ## An environment with a non-constant positive part

`Ebox`, `Etri` and `Elow` are all constant where they are positive, so the localized
log-supermodularity holds there with equality. `Ecoup` tilts the uniform box density by the
coupling `exp (X₀ X₁)`: on the box its log is `X₀ X₁`, which is genuinely supermodular, so
the localized statement is strict at an exhibited pair. The tilt is also where the *global*
`affiliated_iff_logSupermodular` earns its keep — the factor `exp (X₀ X₁)` is strictly
positive everywhere, so the global theorem applies to it even though it never applies to
the density it is a factor of. -/

/-- Supermodularity of `(a, b) ↦ a * b` on `ℝ × ℝ`:
`a * b + c * d ≤ (a ⊔ c) * (b ⊔ d) + (a ⊓ c) * (b ⊓ d)`. -/
theorem mul_supermodular (a b c d : ℝ) :
    a * b + c * d ≤ (a ⊔ c) * (b ⊔ d) + (a ⊓ c) * (b ⊓ d) := by
  rcases le_total a c with h1 | h1
  · rw [sup_of_le_right h1, inf_of_le_left h1]
    rcases le_total b d with h2 | h2
    · rw [sup_of_le_right h2, inf_of_le_left h2]; nlinarith
    · rw [sup_of_le_left h2, inf_of_le_right h2]; nlinarith
  · rw [sup_of_le_left h1, inf_of_le_right h1]
    rcases le_total b d with h2 | h2
    · rw [sup_of_le_right h2, inf_of_le_left h2]; nlinarith
    · rw [sup_of_le_left h2, inf_of_le_right h2]

/-- The coupling factor `X ↦ exp (X 0 * X 1)` is affiliated. Being **strictly positive
everywhere**, it is one of the objects the global `affiliated_iff_logSupermodular` does
apply to, and the proof goes through it: `log` of the factor is `X₀ X₁`, supermodular by
`mul_supermodular`. -/
theorem affiliated_coupFactor (n : ℕ) [NeZero n] :
    Affiliated (fun X : Fin n → ℝ => Real.exp (X 0 * X 1)) := by
  refine (affiliated_iff_logSupermodular (fun _ => Real.exp_pos _)).2 ?_
  intro x y
  simp only [Real.log_exp, Pi.sup_apply, Pi.inf_apply]
  exact mul_supermodular (x 0) (x 1) (y 0) (y 1)

/-- `coupDens n X = exp (X 0 * X 1) * ∏ k, boxInd (X k)`: the uniform box density tilted by
a coupling between coordinates `0` and `1`. Unlike `unifDens`, `triDens` and `lowDens`, this
density is non-constant on the region where it is positive. -/
def coupDens (n : ℕ) [NeZero n] : (Fin n → ℝ) → ℝ :=
  fun X => Real.exp (X 0 * X 1) * ∏ k, boxInd (X k)

/-- `0 ≤ coupDens n X`. -/
theorem coupDens_nonneg (n : ℕ) [NeZero n] (X : Fin n → ℝ) : 0 ≤ coupDens n X :=
  mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg fun _ _ => boxInd_nonneg _)

/-- The coupled box environment: signals on `[0,1]ⁿ` with density `coupDens n`, private
values `v i X = exp (X i)`. -/
def Ecoup (n : ℕ) [NeZero n] : SignalValueEnv n where
  x_lo := 0
  x_hi := 1
  x_lo_le_hi := by norm_num
  f := coupDens n
  f_nonneg := coupDens_nonneg n
  f_support := by
    rintro X ⟨i, hi⟩
    have h : (∏ k, boxInd (X k)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (boxInd_eq_zero hi)
    simp [coupDens, h]
  v := expVal n
  v_nonneg := fun i X => (Real.exp_pos _).le
  v_continuous := fun i => Real.continuous_exp.comp (continuous_apply i)
  v_mono := fun i X Y h => Real.exp_le_exp.2 (h i)
  v_strictMono_own := fun i _ a b hab => by
    simp only [expVal, Function.update_self]; exact Real.exp_lt_exp.2 hab

/-- `Affiliated (Ecoup n).f`, by `Affiliated.mul` of the coupling factor with the uniform
box product density. -/
theorem Ecoup_affiliated (n : ℕ) [NeZero n] : Affiliated (Ecoup n).f :=
  (affiliated_coupFactor n).mul
    (factors_affiliated (g := fun _ => boxInd) (fun _ => rfl))
    (fun _ => (Real.exp_pos _).le)
    (fun _ => Finset.prod_nonneg fun _ _ => boxInd_nonneg _)

/-- `Real.log ((Ecoup n).f x) = x 0 * x 1` on the signal box. -/
theorem log_Ecoup_f_of_mem_signalBox {n : ℕ} [NeZero n] {x : Fin n → ℝ}
    (hx : x ∈ (Ecoup n).signalBox) : Real.log ((Ecoup n).f x) = x 0 * x 1 := by
  have hx' : ∀ k, x k ∈ Set.Icc (0:ℝ) 1 := fun k => ((Ecoup n).mem_signalBox_iff x).1 hx k
  show Real.log (Real.exp (x 0 * x 1) * ∏ k, boxInd (x k)) = x 0 * x 1
  rw [Finset.prod_eq_one fun k _ => boxInd_eq_one (hx' k), mul_one, Real.log_exp]

/-- `0 < (Ecoup n).f x` on the signal box. -/
theorem Ecoup_f_pos_of_mem_signalBox {n : ℕ} [NeZero n] {x : Fin n → ℝ}
    (hx : x ∈ (Ecoup n).signalBox) : 0 < (Ecoup n).f x := by
  have hx' : ∀ k, x k ∈ Set.Icc (0:ℝ) 1 := fun k => ((Ecoup n).mem_signalBox_iff x).1 hx k
  show 0 < Real.exp (x 0 * x 1) * ∏ k, boxInd (x k)
  rw [Finset.prod_eq_one fun k _ => boxInd_eq_one (hx' k), mul_one]
  exact Real.exp_pos _

/-- **The localized characterization applied to `Ecoup n`**, an environment whose log
density is non-constant on the box. -/
theorem logSupermodularOn_signalBox_Ecoup (n : ℕ) [NeZero n] :
    ∀ x ∈ (Ecoup n).signalBox, ∀ y ∈ (Ecoup n).signalBox,
      Real.log ((Ecoup n).f x) + Real.log ((Ecoup n).f y) ≤
        Real.log ((Ecoup n).f (x ⊔ y)) + Real.log ((Ecoup n).f (x ⊓ y)) :=
  (affiliatedOn_signalBox_iff_logSupermodularOn (Ecoup n)
      (fun _ hx => Ecoup_f_pos_of_mem_signalBox hx)).1
    ((Ecoup_affiliated n).affiliatedOn _)

/-- Membership in the signal box of `Ecoup 2`, for the two-coordinate witnesses below. -/
theorem mem_signalBox_Ecoup_two {a b : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1)
    (hb : b ∈ Set.Icc (0:ℝ) 1) : ![a, b] ∈ (Ecoup 2).signalBox := by
  refine ((Ecoup 2).mem_signalBox_iff _).2 fun k => ?_
  fin_cases k
  · exact ha
  · exact hb

/-- **The localized log-supermodularity of `Ecoup 2` is strict** at `x = (0.6, 0.2)`,
`y = (0.2, 0.6)`, both in the signal box: `0.24 < 0.40`. So the conclusion of
`logSupermodularOn_signalBox_Ecoup` is not an equality in disguise, as it is for the
constant-on-their-support densities `Ebox`, `Etri` and `Elow`. -/
theorem logSupermodularOn_Ecoup_two_strict :
    Real.log ((Ecoup 2).f ![0.6, 0.2]) + Real.log ((Ecoup 2).f ![0.2, 0.6])
      < Real.log ((Ecoup 2).f (![(0.6:ℝ), 0.2] ⊔ ![(0.2:ℝ), 0.6]))
        + Real.log ((Ecoup 2).f (![(0.6:ℝ), 0.2] ⊓ ![(0.2:ℝ), 0.6])) := by
  have h06 : (0.6:ℝ) ∈ Set.Icc (0:ℝ) 1 := by norm_num
  have h02 : (0.2:ℝ) ∈ Set.Icc (0:ℝ) 1 := by norm_num
  have hsup : (![(0.6:ℝ), 0.2] ⊔ ![(0.2:ℝ), 0.6]) = ![(0.6:ℝ), 0.6] := by
    funext k; fin_cases k <;> simp [Pi.sup_apply] <;> norm_num
  have hinf : (![(0.6:ℝ), 0.2] ⊓ ![(0.2:ℝ), 0.6]) = ![(0.2:ℝ), 0.2] := by
    funext k; fin_cases k <;> simp [Pi.inf_apply] <;> norm_num
  rw [hsup, hinf,
    log_Ecoup_f_of_mem_signalBox (mem_signalBox_Ecoup_two h06 h02),
    log_Ecoup_f_of_mem_signalBox (mem_signalBox_Ecoup_two h02 h06),
    log_Ecoup_f_of_mem_signalBox (mem_signalBox_Ecoup_two h06 h06),
    log_Ecoup_f_of_mem_signalBox (mem_signalBox_Ecoup_two h02 h02)]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

end

end Auction.Affiliation.Examples

end
