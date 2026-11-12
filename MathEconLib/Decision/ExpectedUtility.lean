/-
Copyright (c) 2026 Ritik Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ritik Jain
-/
module

public import MathEconLib.Decision.Independence
public import MathEconLib.Decision.Continuity
public import MathEconLib.Preferences.Representation.Finite
public import MathEconLib.Probability.FinDist.Expect
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Expected utility

The *expected utility* of a lottery `p` for a Bernoulli function `v : Z → ℝ` is
`p.expect v = ∑_z p(z) v(z)`. A preference `R` on lotteries has an *expected utility
representation* when some `v` gives `p ≼[R] q ↔ p.expect v ≤ q.expect v` for all lotteries.

## Main definitions

* `HasExpectedUtilityRepresentation`: some expected utility `p ↦ p.expect v` represents `R`.

## Main statements

* `isMixtureIndependent_of_isRepresentedBy`, `isMixtureContinuous_of_isRepresentedBy`:
  **Proposition 3.1**, an expected utility representation gives independence and continuity on
  all lotteries.
* `exists_eq_mul_add_of_isRepresentedBy`, `isRepresentedBy_expect_mul_add`: Bernoulli functions
  are unique up to positive affine maps `w = a v + b`, `a > 0`.
* `hasExpectedUtilityRepresentation_of_isMixtureContinuousOn_of_isMixtureIndependentOn`:
  **Proposition 3.2**, the restricted theorem.
* `hasExpectedUtilityRepresentation_iff_isMixtureContinuous_and_isMixtureIndependent`: **the
  expected utility theorem**, for all lotteries.

## Assumptions

The prizes `Z` are finite and the preference is a `CompletePreference` (complete and transitive).
The restricted theorem, Osborne and Rubinstein's Proposition 3.2, asks for less than the iff:

* continuity in mixtures only among sure prizes, `IsMixtureContinuousOn degenerate`: if
  `[c] ≺ [b] ≺ [a]`, some `α · a ⊕ (1 − α) · c` with `0 < α < 1` is indifferent to `[b]`;
* independence only between a sure prize and a binary lottery, in both orders,
  `IsMixtureIndependentOn degenerate binary` and `IsMixtureIndependentOn binary degenerate`.

The iff assumes continuity `IsMixtureContinuous` and independence `IsMixtureIndependent` on all
lotteries, which imply the restricted hypotheses, and are implied by any representation.

No prize needs to be strictly better than another: when all sure prizes are indifferent, the
representation is given by a constant Bernoulli function. Every Bernoulli function of such a
preference is then constant, by uniqueness.

## References

* M. J. Osborne, A. Rubinstein, *Models in Microeconomic Theory* (2023), Section 3.3
* J. von Neumann, O. Morgenstern, *Theory of Games and Economic Behavior*, 2nd ed. (1947)
-/

@[expose] public section

namespace MathEconLib.Decision

open MathEconLib.Probability MathEconLib.Preferences

universe u

variable {Z : Type u} [Fintype Z] {R : Preference (FinDist Z)} {v w : Z → ℝ}

/-- `R` has an *expected utility representation*: some `p ↦ p.expect v` represents it. -/
def HasExpectedUtilityRepresentation (R : Preference (FinDist Z)) : Prop :=
  ∃ v : Z → ℝ, R.IsRepresentedBy fun p => p.expect v

theorem hasExpectedUtilityRepresentation_iff :
    HasExpectedUtilityRepresentation R ↔ ∃ v : Z → ℝ, R.IsRepresentedBy fun p => p.expect v :=
  Iff.rfl

/-! ### Expected utility implies independence and continuity -/

/-- **Proposition 3.1**: a preference with an expected utility representation is independent. -/
theorem isMixtureIndependent_of_isRepresentedBy (h : R.IsRepresentedBy fun p => p.expect v) :
    IsMixtureIndependent R := by
  rw [isMixtureIndependent_iff]
  intro p q r α hα
  rw [h q p, h (FinDist.mixture α q r) (FinDist.mixture α p r)]
  simp only [FinDist.expect_mixture, smul_eq_mul]
  constructor
  · intro hle; nlinarith
  · intro hle; exact le_of_mul_le_mul_left (by linarith) hα

/-- **Proposition 3.1**: a preference with an expected utility representation is continuous in
mixtures. -/
theorem isMixtureContinuous_of_isRepresentedBy (h : R.IsRepresentedBy fun p => p.expect v) :
    IsMixtureContinuous R := by
  rw [isMixtureContinuous_iff]
  intro p q r hpq hqr
  have hlt : ∀ {x y : FinDist Z}, x ≺[R] y → x.expect v < y.expect v := fun hxy =>
    lt_of_le_not_ge ((h _ _).1 hxy.1) fun h' => hxy.2 ((h _ _).2 h')
  have hqp := hlt hpq
  have hrq := hlt hqr
  have hpr : 0 < p.expect v - r.expect v := by linarith
  let α : unitInterval := ⟨(q.expect v - r.expect v) / (p.expect v - r.expect v),
    unitInterval.div_mem (by linarith) hpr.le (by linarith)⟩
  have he : q.expect v = (FinDist.mixture α p r).expect v := by
    simp only [FinDist.expect_mixture, smul_eq_mul, α]
    field_simp
    ring
  exact ⟨α, div_pos (by linarith) hpr, (div_lt_one hpr).2 (by linarith),
    (h _ _).2 he.le, (h _ _).2 he.ge⟩

theorem HasExpectedUtilityRepresentation.isMixtureIndependent
    (h : HasExpectedUtilityRepresentation R) : IsMixtureIndependent R :=
  let ⟨_, hv⟩ := h; isMixtureIndependent_of_isRepresentedBy hv

theorem HasExpectedUtilityRepresentation.isMixtureContinuous
    (h : HasExpectedUtilityRepresentation R) :
    IsMixtureContinuous R :=
  let ⟨_, hv⟩ := h; isMixtureContinuous_of_isRepresentedBy hv

/-! ### Uniqueness of the Bernoulli function -/

/-- If `v` is a Bernoulli function for `R`, so is `a v + b` for `a > 0`. -/
theorem isRepresentedBy_expect_mul_add (h : R.IsRepresentedBy fun p => p.expect v) {a : ℝ}
    (ha : 0 < a) (b : ℝ) : R.IsRepresentedBy fun p => p.expect fun z => a * v z + b := by
  have key : ∀ p : FinDist Z, p.expect (fun z => a * v z + b) = a * p.expect v + b := by
    intro p
    have e : ∀ z, p.pmf z * (a * v z + b) = a * (p.pmf z * v z) + b * p.pmf z := fun _ => by
      ring
    simp only [FinDist.expect_eq_sum, smul_eq_mul, e, Finset.sum_add_distrib, ← Finset.mul_sum,
      p.sum_one, mul_one]
  have hf : StrictMono fun t : ℝ => a * t + b := fun s t hst => by
    dsimp only
    linarith [mul_lt_mul_of_pos_left hst ha]
  convert h.comp_strictMono hf using 1
  funext p
  exact key p

/-- Two Bernoulli functions for one preference satisfy `w = a v + b` for some `a > 0` and `b`. -/
theorem exists_eq_mul_add_of_isRepresentedBy (hv : R.IsRepresentedBy fun p => p.expect v)
    (hw : R.IsRepresentedBy fun p => p.expect w) :
    ∃ a > (0 : ℝ), ∃ b : ℝ, ∀ z, w z = a * v z + b := by
  classical
  -- If `v` is constant, so is `w`. Otherwise fix `v b < v a` and compare, for each `z`, two
  -- lotteries with equal `v`-utility, which then have equal `w`-utility.
  have K : ∀ p q : FinDist Z, p.expect v = q.expect v → p.expect w = q.expect w :=
    fun p q hpq => le_antisymm ((hw p q).1 ((hv p q).2 hpq.le)) ((hw q p).1 ((hv q p).2 hpq.ge))
  by_cases hconst : ∃ a b, v b < v a
  · obtain ⟨a, b, hba⟩ := hconst
    have hd : 0 < v a - v b := sub_pos.2 hba
    have hwba : w b < w a := by
      by_contra hab
      push Not at hab
      have h1 : FinDist.pure a ≼[R] FinDist.pure b :=
        (hw _ _).2 (by simpa only [FinDist.expect_pure] using hab)
      have h2 := (hv _ _).1 h1
      simp only [FinDist.expect_pure] at h2
      linarith
    refine ⟨(w a - w b) / (v a - v b), div_pos (sub_pos.2 hwba) hd,
      w b - (w a - w b) / (v a - v b) * v b, fun z => ?_⟩
    suffices hkey : (v a - v b) * (w z - w b) = (w a - w b) * (v z - v b) by
      rw [show (w a - w b) / (v a - v b) * v z + (w b - (w a - w b) / (v a - v b) * v b) =
          w b + (w a - w b) * (v z - v b) / (v a - v b) by ring, ← hkey,
        mul_div_cancel_left₀ _ hd.ne']
      ring
    rcases le_or_gt (v b) (v z) with hbz | hzb
    · have hs : 0 < (v z - v b) + (v a - v b) := by linarith
      let ε : unitInterval := ⟨(v a - v b) / ((v z - v b) + (v a - v b)),
        unitInterval.div_mem hd.le hs.le (by linarith)⟩
      let η : unitInterval := ⟨(v z - v b) / ((v z - v b) + (v a - v b)),
        unitInterval.div_mem (by linarith) hs.le (by linarith)⟩
      have h := K (FinDist.mixture ε (FinDist.pure z) (FinDist.pure b))
        (FinDist.mixture η (FinDist.pure a) (FinDist.pure b)) (by
          simp only [FinDist.expect_mixture, FinDist.expect_pure, smul_eq_mul, ε, η]
          field_simp
          ring)
      simp only [FinDist.expect_mixture, FinDist.expect_pure, smul_eq_mul, ε, η] at h
      have h1 : (v a - v b) / ((v z - v b) + (v a - v b)) * (w z - w b) =
          (v z - v b) / ((v z - v b) + (v a - v b)) * (w a - w b) := by linarith
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_left_inj' hs.ne'] at h1
      linear_combination h1
    · have he : 0 < v a - v z := by linarith
      let t : unitInterval := ⟨(v a - v b) / (v a - v z),
        unitInterval.div_mem hd.le he.le (by linarith)⟩
      have h := K (FinDist.mixture t (FinDist.pure z) (FinDist.pure a)) (FinDist.pure b) (by
        simp only [FinDist.expect_mixture, FinDist.expect_pure, smul_eq_mul, t]
        field_simp
        ring)
      simp only [FinDist.expect_mixture, FinDist.expect_pure, smul_eq_mul, t] at h
      have h1 : (v a - v b) / (v a - v z) * (w z - w a) = w b - w a := by linarith
      rw [div_mul_eq_mul_div, div_eq_iff he.ne'] at h1
      linear_combination h1
  · push Not at hconst
    rcases isEmpty_or_nonempty Z with hZ | ⟨⟨z₀⟩⟩
    · exact ⟨1, one_pos, 0, fun z => (IsEmpty.false z).elim⟩
    · refine ⟨1, one_pos, w z₀ - v z₀, fun z => ?_⟩
      have hvz : v z = v z₀ := le_antisymm (hconst z z₀) (hconst z₀ z)
      have hwz : w z = w z₀ := by
        simpa only [FinDist.expect_pure] using
          K (FinDist.pure z) (FinDist.pure z₀) (by simpa only [FinDist.expect_pure] using hvz)
      rw [hwz, hvz]; ring

/-! ### The expected utility theorem -/

/-- **Proposition 3.2**: on finite `Z`, a complete preference that is continuous in mixtures among
sure prizes, and independent between a sure prize and a binary lottery in both orders, has an
expected utility representation. -/
theorem hasExpectedUtilityRepresentation_of_isMixtureContinuousOn_of_isMixtureIndependentOn
    [DecidableEq Z] {R : CompletePreference (FinDist Z)}
    (hC : IsMixtureContinuousOn degenerate R.toPreference)
    (hDB : IsMixtureIndependentOn degenerate binary R.toPreference)
    (hBD : IsMixtureIndependentOn binary degenerate R.toPreference) :
    HasExpectedUtilityRepresentation R.toPreference := by
  rcases isEmpty_or_nonempty Z with hZ | hZ
  · refine ⟨0, fun p _ => ?_⟩
    obtain ⟨z, -⟩ := p.exists_pmf_pos
    exact (IsEmpty.false z).elim
  have hDD : IsMixtureIndependentOn degenerate degenerate R.toPreference :=
    hDB.mono subset_rfl degenerate_subset_binary
  -- With a best prize `a` and a worst `b`, each `p` is indifferent to `mix (U p) [a] [b]`, and
  -- monotonicity ranks these mixtures by `U`.
  obtain ⟨u, hu⟩ := (R.comap FinDist.pure).exists_isRepresentedBy_real
  obtain ⟨a, ha⟩ := Finite.exists_max u
  obtain ⟨b, hb⟩ := Finite.exists_min u
  have hRa : ∀ z, FinDist.pure z ≼[R] FinDist.pure a := fun z => (hu z a).2 (ha z)
  have hRb : ∀ z, FinDist.pure b ≼[R] FinDist.pure z := fun z => (hu b z).2 (hb z)
  by_cases hab : FinDist.pure b ≺[R] FinDist.pure a
  · have hne : a ≠ b := fun h => by subst h; exact R.lt_irrefl _ hab
    have hex : ∀ z, ∃ t : unitInterval,
        FinDist.pure z ~[R] FinDist.mixture t (FinDist.pure a) (FinDist.pure b) := by
      intro z
      by_cases hza : FinDist.pure a ≼[R] FinDist.pure z
      · exact ⟨1, by rw [FinDist.mixture_one]; exact ⟨hRa z, hza⟩⟩
      by_cases hbz : FinDist.pure z ≼[R] FinDist.pure b
      · exact ⟨0, by rw [FinDist.mixture_zero]; exact ⟨hbz, hRb z⟩⟩
      obtain ⟨t, -, -, ht⟩ := hC _ (pure_mem_degenerate a) _ (pure_mem_degenerate z) _
        (pure_mem_degenerate b) ⟨hRa z, hza⟩ ⟨hRb z, hbz⟩
      exact ⟨t, ht⟩
    choose t ht using hex
    let tv : Z → unitInterval := fun z => if z = a then 1 else if z = b then 0 else t z
    let m : Z → FinDist Z := fun z => FinDist.mixture (tv z) (FinDist.pure a) (FinDist.pure b)
    have hma : m a = FinDist.pure a := by simp [m, tv]
    have hmb : m b = FinDist.pure b := by simp [m, tv, Ne.symm hne]
    have hm : ∀ z, FinDist.pure z ~[R] m z := by
      intro z
      by_cases hza : z = a
      · subst hza; rw [hma]
      by_cases hzb : z = b
      · subst hzb; rw [hmb]
      simpa [m, tv, hza, hzb] using ht z
    have hmT : ∀ z y, (m z).pmf y ≠ 0 → y ∈ ({a, b} : Finset Z) := by
      intro z y hy
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_contra hyab
      rw [not_or] at hyab
      apply hy
      simp only [m, FinDist.mixture_pmf, FinDist.pure_pmf, Ne.symm hyab.1, Ne.symm hyab.2,
        ite_false, mul_zero, add_zero]
    have hT : ∀ s ∈ ({a, b} : Finset Z), m s = FinDist.pure s := by
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl
      · exact hma
      · exact hmb
    have hrepl := hDB.antisymmRel_finMixture hBD m {a, b} hm (fun z => mixture_mem_binary _ _ _)
      hmT hT
    let U : FinDist Z → ℝ := fun p => p.expect fun z => (tv z : ℝ)
    have hU : ∀ p, U p ∈ unitInterval := fun p =>
      Set.mem_Icc.2 ⟨FinDist.expect_nonneg p _ fun z => (tv z).2.1,
        (FinDist.expect_mono p _ (fun _ => 1) fun z => (tv z).2.2).trans_eq
          (FinDist.expect_const p 1)⟩
    have hcomp : ∀ p, FinDist.finMixture p m =
        FinDist.mixture ⟨U p, hU p⟩ (FinDist.pure a) (FinDist.pure b) := by
      intro p
      refine FinDist.ext _ _ fun y => ?_
      rw [FinDist.finMixture_pmf, FinDist.mixture_pmf]
      change ∑ s, p.pmf s * (FinDist.mixture (tv s) (FinDist.pure a) (FinDist.pure b)).pmf y =
        (∑ s, p.pmf s • (tv s : ℝ)) * (FinDist.pure a).pmf y +
          (1 - ∑ s, p.pmf s • (tv s : ℝ)) * (FinDist.pure b).pmf y
      simp only [FinDist.mixture_pmf, smul_eq_mul]
      have e : ∀ s, p.pmf s * ((tv s : ℝ) * (FinDist.pure a).pmf y +
          (1 - (tv s : ℝ)) * (FinDist.pure b).pmf y) =
          ((FinDist.pure a).pmf y - (FinDist.pure b).pmf y) * (p.pmf s * (tv s : ℝ)) +
          (FinDist.pure b).pmf y * p.pmf s := fun _ => by ring
      simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, p.sum_one]
      ring
    refine ⟨fun z => (tv z : ℝ), fun p q => ?_⟩
    change p ≼[R] q ↔ U p ≤ U q
    have hp := hrepl p
    have hq := hrepl q
    rw [hcomp] at hp hq
    have hmono := hDD.le_mixture_iff hab ⟨U q, hU q⟩ ⟨U p, hU p⟩
    constructor
    · intro hpq
      exact hmono.1 (R.le_trans (R.le_trans hp.2 hpq) hq.1)
    · intro hle
      exact R.le_trans (R.le_trans hp.1 (hmono.2 hle)) hq.2
  · have hba : FinDist.pure a ≼[R] FinDist.pure b := R.not_lt.1 hab
    have hm : ∀ z, FinDist.pure z ~[R] FinDist.pure b :=
      fun z => ⟨R.le_trans (hRa z) hba, hRb z⟩
    have hrepl := hDB.antisymmRel_finMixture hBD (fun _ => FinDist.pure b) {b} hm
      (fun _ => degenerate_subset_binary (pure_mem_degenerate b))
      (fun _ y hy => by
        rw [Finset.mem_singleton]
        by_contra h
        exact hy (by simp only [FinDist.pure_pmf, Ne.symm h, ite_false]))
      (fun s hs => by rw [Finset.mem_singleton.1 hs])
    refine ⟨fun _ => 0, fun p q => ?_⟩
    simp only [FinDist.expect_const, le_refl, iff_true]
    have hp := hrepl p
    have hq := hrepl q
    rw [FinDist.finMixture_const] at hp hq
    exact R.le_trans hp.1 hq.2

/-- **The expected utility theorem**: on finite `Z`, a complete preference has an expected utility
representation iff it is continuous in mixtures and independent on all lotteries. -/
theorem hasExpectedUtilityRepresentation_iff_isMixtureContinuous_and_isMixtureIndependent
    {R : CompletePreference (FinDist Z)} :
    HasExpectedUtilityRepresentation R.toPreference ↔
      IsMixtureContinuous R.toPreference ∧ IsMixtureIndependent R.toPreference := by
  classical
  exact ⟨fun h => ⟨h.isMixtureContinuous, h.isMixtureIndependent⟩, fun ⟨hC, hI⟩ =>
    hasExpectedUtilityRepresentation_of_isMixtureContinuousOn_of_isMixtureIndependentOn
      (hC.isMixtureContinuousOn _) (hI.isMixtureIndependentOn _ _) (hI.isMixtureIndependentOn _ _)⟩

end MathEconLib.Decision

/-! ### Worked examples -/

section Examples

open MathEconLib.Probability MathEconLib.Decision MathEconLib.Preferences

/-- A lottery paying `3000` with probability `1/4` and `0` otherwise has expected value `750`. -/
example : (FinDist.mixture ⟨0.25, by norm_num, by norm_num⟩ (FinDist.pure (0 : Fin 2))
    (FinDist.pure 1)).expect ![(3000 : ℝ), 0] = 750 := by
  simp [FinDist.expect_mixture, FinDist.expect_pure]
  norm_num

/-- The Allais paradox, with prizes `4000`, `3000` and `0` indexed by `0`, `1` and `2`:
`U(L₁) − U(R₁)` is a quarter of `U(L₂) − U(R₂)` for every `v`. -/
example (v : Fin 3 → ℝ) :
    (FinDist.mixture ⟨0.2, by norm_num, by norm_num⟩ (FinDist.pure 0) (FinDist.pure 2)).expect v -
      (FinDist.mixture ⟨0.25, by norm_num, by norm_num⟩ (FinDist.pure 1)
        (FinDist.pure 2)).expect v =
    ((FinDist.mixture ⟨0.8, by norm_num, by norm_num⟩ (FinDist.pure 0)
        (FinDist.pure 2)).expect v - (FinDist.pure 1).expect v) / 4 := by
  simp only [FinDist.expect_mixture, FinDist.expect_pure, smul_eq_mul]
  ring

example : IsMixtureIndependent (Preference.ofUtility fun p : FinDist (Fin 2) =>
    p.expect fun z => if z = 0 then (1 : ℝ) else 0) :=
  isMixtureIndependent_of_isRepresentedBy (Preference.isRepresentedBy_ofUtility _)

/-- `−v` is not a Bernoulli function for the preference of `v`. -/
example : ¬ (Preference.ofUtility fun p : FinDist (Fin 2) =>
    p.expect fun z => (z : ℝ)).IsRepresentedBy fun p => p.expect fun z => -1 * (z : ℝ) + 0 := by
  intro h
  have := (h (FinDist.pure 0) (FinDist.pure 1)).1 (by
    simp only [Preference.ofUtility_le_iff, FinDist.expect_pure]
    norm_num)
  simp only [FinDist.expect_pure] at this
  norm_num at this

end Examples
