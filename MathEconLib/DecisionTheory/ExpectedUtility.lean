/-
Copyright (c) 2026 Ritik Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ritik Jain
-/
module

public import MathEconLib.DecisionTheory.Independence
public import MathEconLib.DecisionTheory.Continuity
public import MathEconLib.Preference.Utility
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Tactic.LinearCombination
public import MathEconLib.Probability.FinDist.Expect

/-!
# Expected utility

The *expected utility* of a lottery `p` for `v : Z → ℝ` is `∑_z p(z) v(z)`. On a finite set of
prizes, a preference relation has an expected utility representation iff it is continuous and
independent (von Neumann–Morgenstern).

## Main statements

* `isIndependent_of_represents`, `isMixtureContinuous_of_represents`: **Proposition 3.1**.
* `exists_eq_mul_add_of_represents`: Bernoulli functions are unique up to positive affine maps.
* `hasExpectedUtility_of_isIndependentOn`: **Proposition 3.2**.
* `hasExpectedUtility_iff_isMixtureContinuous_and_isIndependent`: the expected utility theorem.

## References

* M. J. Osborne, A. Rubinstein, *Models in Microeconomic Theory* (2023), Section 3.3
* J. von Neumann, O. Morgenstern, *Theory of Games and Economic Behavior*, 2nd ed. (1947)
-/

@[expose] public section

namespace MathEconLib.DecisionTheory

open Convexity MathEconLib.Preference

universe u v

namespace Lottery

variable {Z : Type u} {I : Type v} {R : Lottery Z → Lottery Z → Prop} {v w : Z → ℝ}

/-- The *expected utility* `U(p) = ∑_z p(z) v(z)` for the Bernoulli function `v`. -/
noncomputable def expectedUtility (v : Z → ℝ) (p : Lottery Z) : ℝ := p.iConvexComb v

/-- `≿` is *consistent with expected utility*: some `expectedUtility v` represents it. -/
def HasExpectedUtility (R : Lottery Z → Lottery Z → Prop) : Prop :=
  ∃ v : Z → ℝ, Represents (expectedUtility v) R

/-! ### Interface -/

theorem hasExpectedUtility_iff :
    HasExpectedUtility R ↔ ∃ v : Z → ℝ, Represents (expectedUtility v) R :=
  Iff.rfl

theorem expectedUtility_eq_sum (v : Z → ℝ) (p : Lottery Z) :
    expectedUtility v p = p.weights.sum fun z a => a * v z := by
  simp [expectedUtility]

theorem expectedUtility_eq_sum_fintype [Fintype Z] (v : Z → ℝ) (p : Lottery Z) :
    expectedUtility v p = ∑ z, p.weights z * v z := by
  rw [expectedUtility_eq_sum, Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]

@[simp]
theorem expectedUtility_single (v : Z → ℝ) (z : Z) :
    expectedUtility v (.single z) = v z := by
  simp [expectedUtility]

@[simp]
theorem expectedUtility_mix (v : Z → ℝ) (α : unitInterval) (p q : Lottery Z) :
    expectedUtility v (mix α p q) = α * expectedUtility v p + (1 - α) * expectedUtility v q := by
  have h := (StdSimplex.affineMapMk (R := ℝ) v).isAffineMap.map_convexCombPair
    (unitInterval.nonneg α) (unitInterval.one_sub_nonneg α) (add_sub_cancel _ _) p q
  simp only [StdSimplex.affineMapMk_apply] at h
  rw [expectedUtility, mix, h]
  simp [expectedUtility]

theorem expectedUtility_iConvexComb (v : Z → ℝ) (w : StdSimplex ℝ I) (f : I → Lottery Z) :
    expectedUtility v (w.iConvexComb f) = w.weights.sum fun i a => a * expectedUtility v (f i) := by
  have h := (StdSimplex.affineMapMk (R := ℝ) v).isAffineMap.map_iConvexComb w f
  simp only [StdSimplex.affineMapMk_apply] at h
  rw [expectedUtility, h]
  simp [expectedUtility, StdSimplex.affineMapMk_apply]

theorem isAffineMap_expectedUtility (v : Z → ℝ) : IsAffineMap ℝ (expectedUtility v) :=
  (StdSimplex.affineMapMk (R := ℝ) v).isAffineMap

theorem expectedUtility_mul_add (v : Z → ℝ) (a b : ℝ) (p : Lottery Z) :
    expectedUtility (fun z => a * v z + b) p = a * expectedUtility v p + b := by
  rw [expectedUtility_eq_sum, expectedUtility_eq_sum]
  have h : ∀ z c, c * (a * v z + b) = a * (c * v z) + b * c := fun _ _ => by ring
  simp only [h]
  rw [Finsupp.sum_add, ← Finsupp.mul_sum, ← Finsupp.mul_sum, p.total, mul_one]

@[simp]
theorem expectedUtility_const (b : ℝ) (p : Lottery Z) :
    expectedUtility (fun _ => b) p = b := by
  simpa using expectedUtility_mul_add (fun _ : Z => (0 : ℝ)) 0 b p

/-! ### Expected utility implies independence and continuity -/

/-- **Proposition 3.1**: a relation with expected utility is independent. -/
theorem isIndependent_of_represents (h : Represents (expectedUtility v) R) : IsIndependent R := by
  rw [isIndependent_iff]
  intro p q r α hα
  rw [h p q, h (mix α p r) (mix α q r), expectedUtility_mix, expectedUtility_mix]
  constructor
  · intro hle; nlinarith
  · intro hle; exact le_of_mul_le_mul_left (by linarith) hα

/-- **Proposition 3.1**: a relation with expected utility is continuous in mixtures. -/
theorem isMixtureContinuous_of_represents (h : Represents (expectedUtility v) R) :
    IsMixtureContinuous R := by
  rw [isMixtureContinuous_iff]
  intro p q r hpq hqr
  rw [h.strictPart_iff] at hpq hqr
  have hpr : 0 < expectedUtility v p - expectedUtility v r := by linarith
  refine ⟨⟨(expectedUtility v q - expectedUtility v r) /
      (expectedUtility v p - expectedUtility v r),
    unitInterval.div_mem (by linarith) hpr.le (by linarith)⟩,
    div_pos (by linarith) hpr, (div_lt_one hpr).2 (by linarith), ?_⟩
  rw [h.indiff_iff, expectedUtility_mix]
  field_simp
  ring

theorem HasExpectedUtility.isIndependent (h : HasExpectedUtility R) : IsIndependent R :=
  let ⟨_, hv⟩ := h; isIndependent_of_represents hv

theorem HasExpectedUtility.isMixtureContinuous (h : HasExpectedUtility R) :
    IsMixtureContinuous R :=
  let ⟨_, hv⟩ := h; isMixtureContinuous_of_represents hv

/-! ### Uniqueness of the Bernoulli function -/

/-- If `v` is a Bernoulli function for `≿`, so is `a v + b` for `a > 0`. -/
theorem represents_expectedUtility_mul_add (h : Represents (expectedUtility v) R) {a : ℝ}
    (ha : 0 < a) (b : ℝ) : Represents (expectedUtility fun z => a * v z + b) R := by
  intro p q
  rw [expectedUtility_mul_add, expectedUtility_mul_add]
  exact h.affine ha b p q

/-- Two Bernoulli functions for one relation satisfy `w = a v + b` for some `a > 0` and `b`. -/
theorem exists_eq_mul_add_of_represents (hv : Represents (expectedUtility v) R)
    (hw : Represents (expectedUtility w) R) :
    ∃ a > (0 : ℝ), ∃ b : ℝ, ∀ z, w z = a * v z + b := by
  -- If `v` is constant, so is `w`. Otherwise fix `v b < v a` and compare, for each `z`, two
  -- lotteries with equal `v`-utility, which then have equal `w`-utility.
  have K : ∀ p q, expectedUtility v p = expectedUtility v q →
      expectedUtility w p = expectedUtility w q :=
    fun p q hpq => hw.indiff_iff.1 (hv.indiff_iff.2 hpq)
  by_cases hconst : ∃ a b, v b < v a
  · obtain ⟨a, b, hba⟩ := hconst
    have hd : 0 < v a - v b := sub_pos.2 hba
    have hwba : w b < w a := by
      have hs : StrictPart R (.single a) (.single b) := hv.strictPart_iff.2 (by simpa using hba)
      simpa using hw.strictPart_iff.1 hs
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
      have h := K (mix ε (.single z) (.single b)) (mix η (.single a) (.single b)) (by
        simp only [expectedUtility_mix, expectedUtility_single, ε, η]
        field_simp
        ring)
      simp only [expectedUtility_mix, expectedUtility_single, ε, η] at h
      have h1 : (v a - v b) / ((v z - v b) + (v a - v b)) * (w z - w b) =
          (v z - v b) / ((v z - v b) + (v a - v b)) * (w a - w b) := by linarith
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_left_inj' hs.ne'] at h1
      linear_combination h1
    · have he : 0 < v a - v z := by linarith
      let t : unitInterval := ⟨(v a - v b) / (v a - v z),
        unitInterval.div_mem hd.le he.le (by linarith)⟩
      have h := K (mix t (.single z) (.single a)) (.single b) (by
        simp only [expectedUtility_mix, expectedUtility_single, t]
        field_simp
        ring)
      simp only [expectedUtility_mix, expectedUtility_single, t] at h
      have h1 : (v a - v b) / (v a - v z) * (w z - w a) = w b - w a := by linarith
      rw [div_mul_eq_mul_div, div_eq_iff he.ne'] at h1
      linear_combination h1
  · push Not at hconst
    rcases isEmpty_or_nonempty Z with hZ | ⟨⟨z₀⟩⟩
    · exact ⟨1, one_pos, 0, fun z => (IsEmpty.false z).elim⟩
    · refine ⟨1, one_pos, w z₀ - v z₀, fun z => ?_⟩
      have hvz : v z = v z₀ := le_antisymm (hconst z z₀) (hconst z₀ z)
      have hwz : w z = w z₀ := by simpa using K (.single z) (.single z₀) (by simpa using hvz)
      rw [hwz, hvz]; ring

/-! ### The expected utility theorem -/

/-- **Proposition 3.2**: on finite `Z`, a preference continuous on degenerate lotteries and
independent between degenerate and binary ones, both ways, has expected utility. -/
theorem hasExpectedUtility_of_isIndependentOn [Finite Z] (hR : IsPreferenceRelation R)
    (hC : IsMixtureContinuousOn degenerate R) (hDB : IsIndependentOn degenerate binary R)
    (hBD : IsIndependentOn binary degenerate R) : HasExpectedUtility R := by
  classical
  rcases isEmpty_or_nonempty Z with hZ | hZ
  · exact ⟨0, fun p => absurd p.nonempty (not_nonempty_iff.2 hZ)⟩
  have htrans : IsTransitive (Indiff R) := hR.isTransitive.indiff
  have hDD : IsIndependentOn degenerate degenerate R :=
    hDB.mono subset_rfl degenerate_subset_binary
  -- With a best prize `a` and a worst `b`, each `p` is indifferent to `mix (U p) [a] [b]`, and
  -- monotonicity ranks these mixtures by `U`.
  have hRZ : IsPreferenceRelation fun x y : Z => R (.single x) (.single y) :=
    ⟨isComplete_iff.2 fun x y => hR.total _ _,
      isTransitive_iff.2 fun _ _ _ h₁ h₂ => hR.trans h₁ h₂⟩
  obtain ⟨u, hu⟩ := exists_represents_of_finite hRZ
  obtain ⟨a, ha⟩ := Finite.exists_max u
  obtain ⟨b, hb⟩ := Finite.exists_min u
  have hRa : ∀ z, R (.single a) (.single z) := fun z => (hu a z).2 (ha z)
  have hRb : ∀ z, R (.single z) (.single b) := fun z => (hu z b).2 (hb z)
  by_cases hab : StrictPart R (.single a) (.single b)
  · have hne : a ≠ b := fun h => hab.ne (by rw [h])
    have hex : ∀ z, ∃ t : unitInterval,
        Indiff R (.single z) (mix t (.single a) (.single b)) := by
      intro z
      by_cases hza : R (.single z) (.single a)
      · exact ⟨1, by rw [mix_one]; exact ⟨hza, hRa z⟩⟩
      by_cases hbz : R (.single b) (.single z)
      · exact ⟨0, by rw [mix_zero]; exact ⟨hRb z, hbz⟩⟩
      obtain ⟨t, -, -, ht⟩ := hC _ (single_mem_degenerate a) _ (single_mem_degenerate z) _
        (single_mem_degenerate b) ⟨hRa z, hza⟩ ⟨hRb z, hbz⟩
      exact ⟨t, ht⟩
    choose t ht using hex
    let tv : Z → unitInterval := fun z => if z = a then 1 else if z = b then 0 else t z
    let m : Z → Lottery Z := fun z => mix (tv z) (.single a) (.single b)
    have hma : m a = .single a := by simp [m, tv]
    have hmb : m b = .single b := by simp [m, tv, Ne.symm hne]
    have hm : ∀ z, Indiff R (.single z) (m z) := by
      intro z
      by_cases hza : z = a
      · subst hza; rw [hma]; exact ⟨hR.refl _, hR.refl _⟩
      by_cases hzb : z = b
      · subst hzb; rw [hmb]; exact ⟨hR.refl _, hR.refl _⟩
      simpa [m, tv, hza, hzb] using ht z
    have hmT : ∀ z y, (m z).weights y ≠ 0 → y ∈ ({a, b} : Finset Z) := by
      intro z y hy
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_contra hyab
      rw [not_or] at hyab
      apply hy
      simp [m, Ne.symm hyab.1, Ne.symm hyab.2]
    have hT : ∀ s ∈ ({a, b} : Finset Z), m s = .single s := by
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl
      · exact hma
      · exact hmb
    have hrepl := hDB.indiff_iConvexComb hR hBD m {a, b} hm (fun z => mix_mem_binary _ _ _) hmT hT
    let U : Lottery Z → ℝ := expectedUtility fun z => (tv z : ℝ)
    have hU : ∀ p, (U p) ∈ unitInterval := by
      intro p
      simp only [U, expectedUtility_eq_sum, Finsupp.sum]
      refine Set.mem_Icc.2 ⟨Finset.sum_nonneg fun z _ => mul_nonneg (p.nonneg z) (tv z).2.1, ?_⟩
      calc ∑ z ∈ p.weights.support, p.weights z * (tv z : ℝ)
          ≤ ∑ z ∈ p.weights.support, p.weights z :=
            Finset.sum_le_sum fun z _ => mul_le_of_le_one_right (p.nonneg z) (tv z).2.2
        _ = 1 := p.total
    have hcomp : ∀ p, p.iConvexComb m = mix ⟨U p, hU p⟩ (.single a) (.single b) := by
      intro p
      ext y
      rw [weights_iConvexComb_apply, weights_mix]
      simp only [m, weights_mix, U, expectedUtility_eq_sum]
      have e : ∀ z c, c * ((tv z : ℝ) * (StdSimplex.single a : Lottery Z).weights y +
          (1 - (tv z : ℝ)) * (StdSimplex.single b : Lottery Z).weights y) =
          ((StdSimplex.single a : Lottery Z).weights y -
            (StdSimplex.single b : Lottery Z).weights y) * (c * (tv z : ℝ)) +
          (StdSimplex.single b : Lottery Z).weights y * c := fun _ _ => by ring
      simp only [e]
      rw [Finsupp.sum_add, ← Finsupp.mul_sum, ← Finsupp.mul_sum, p.total]
      ring
    refine ⟨fun z => (tv z : ℝ), fun p q => ?_⟩
    have hp := hrepl p
    have hq := hrepl q
    rw [hcomp] at hp hq
    have hmono := hDD.rel_mix_iff hR.isComplete hab ⟨U p, hU p⟩ ⟨U q, hU q⟩
    constructor
    · intro hpq
      exact hmono.1 (hR.trans (hR.trans hp.2 hpq) hq.1)
    · intro hle
      exact hR.trans (hR.trans hp.1 (hmono.2 hle)) hq.2
  · have hba : R (.single b) (.single a) := by
      by_contra h; exact hab ⟨hRb a, h⟩
    have hm : ∀ z, Indiff R (.single z) (.single b) :=
      fun z => ⟨hRb z, hR.trans hba (hRa z)⟩
    have hrepl := hDB.indiff_iConvexComb hR hBD (fun _ => .single b) {b} hm
      (fun _ => degenerate_subset_binary (single_mem_degenerate b))
      (fun _ y hy => by
        rw [Finset.mem_singleton]
        by_contra h
        exact hy (by simp [Ne.symm h]))
      (fun s hs => by rw [Finset.mem_singleton.1 hs])
    refine ⟨fun _ => 0, fun p q => ?_⟩
    simp only [expectedUtility_const, le_refl, iff_true]
    have hp := hrepl p
    have hq := hrepl q
    rw [iConvexComb_const] at hp hq
    exact hR.trans hp.1 hq.2

/-- **The expected utility theorem**: on finite `Z`, a preference has expected utility iff it is
continuous in mixtures and independent. -/
theorem hasExpectedUtility_iff_isMixtureContinuous_and_isIndependent [Finite Z]
    (hR : IsPreferenceRelation R) :
    HasExpectedUtility R ↔ IsMixtureContinuous R ∧ IsIndependent R :=
  ⟨fun h => ⟨h.isMixtureContinuous, h.isIndependent⟩, fun ⟨hC, hI⟩ =>
    hasExpectedUtility_of_isIndependentOn hR (hC.isMixtureContinuousOn _)
      (hI.isIndependentOn _ _) (hI.isIndependentOn _ _)⟩

open MathEconLib.Probability in
@[simp]
theorem expectedUtility_ofFinDist [Fintype Z] (v : Z → ℝ) (d : FinDist Z) :
    expectedUtility v (ofFinDist d) = d.expect v := by
  simp [expectedUtility_eq_sum_fintype, FinDist.expect_eq_sum]

end Lottery

/-! ### Lotteries over a finite set of prizes -/

section FinDist

open MathEconLib.Probability

variable {Z : Type u} [Fintype Z] {R : FinDist Z → FinDist Z → Prop} {v w : Z → ℝ}

/-- `≿` is *consistent with expected utility*: some `p ↦ p.expect v` represents it. -/
def HasExpectedUtility (R : FinDist Z → FinDist Z → Prop) : Prop :=
  ∃ v : Z → ℝ, Represents (fun p : FinDist Z => p.expect v) R

theorem represents_expect_iff_lottery : Represents (fun p : FinDist Z => p.expect v) R ↔
    Represents (Lottery.expectedUtility v) (Lottery.ofFinDist.symm ⁻¹'o R) := by
  simp only [Represents, Lottery.ofFinDist.surjective.forall, Order.Preimage,
    Equiv.symm_apply_apply, Lottery.expectedUtility_ofFinDist]

theorem hasExpectedUtility_iff_lottery :
    HasExpectedUtility R ↔ Lottery.HasExpectedUtility (Lottery.ofFinDist.symm ⁻¹'o R) :=
  exists_congr fun _ => represents_expect_iff_lottery

/-- **Proposition 3.1**: a relation with expected utility is independent. -/
theorem isIndependent_of_represents (h : Represents (fun p : FinDist Z => p.expect v) R) :
    IsIndependent R :=
  isIndependent_iff_lottery.2
    (Lottery.isIndependent_of_represents (represents_expect_iff_lottery.1 h))

/-- **Proposition 3.1**: a relation with expected utility is continuous in mixtures. -/
theorem isMixtureContinuous_of_represents (h : Represents (fun p : FinDist Z => p.expect v) R) :
    IsMixtureContinuous R :=
  isMixtureContinuous_iff_lottery.2
    (Lottery.isMixtureContinuous_of_represents (represents_expect_iff_lottery.1 h))

theorem HasExpectedUtility.isIndependent (h : HasExpectedUtility R) : IsIndependent R :=
  let ⟨_, hv⟩ := h; isIndependent_of_represents hv

theorem HasExpectedUtility.isMixtureContinuous (h : HasExpectedUtility R) :
    IsMixtureContinuous R :=
  let ⟨_, hv⟩ := h; isMixtureContinuous_of_represents hv

/-- If `v` is a Bernoulli function for `≿`, so is `a v + b` for `a > 0`. -/
theorem represents_expect_mul_add (h : Represents (fun p : FinDist Z => p.expect v) R) {a : ℝ}
    (ha : 0 < a) (b : ℝ) :
    Represents (fun p : FinDist Z => p.expect fun z => a * v z + b) R :=
  represents_expect_iff_lottery.2
    (Lottery.represents_expectedUtility_mul_add (represents_expect_iff_lottery.1 h) ha b)

/-- Two Bernoulli functions for one relation satisfy `w = a v + b` for some `a > 0` and `b`. -/
theorem exists_eq_mul_add_of_represents (hv : Represents (fun p : FinDist Z => p.expect v) R)
    (hw : Represents (fun p : FinDist Z => p.expect w) R) :
    ∃ a > (0 : ℝ), ∃ b : ℝ, ∀ z, w z = a * v z + b :=
  Lottery.exists_eq_mul_add_of_represents (represents_expect_iff_lottery.1 hv)
    (represents_expect_iff_lottery.1 hw)

/-- **Proposition 3.2**: a preference continuous on degenerate lotteries and independent between
degenerate and binary ones, both ways, has expected utility. -/
theorem hasExpectedUtility_of_isIndependentOn [DecidableEq Z] (hR : IsPreferenceRelation R)
    (hC : IsMixtureContinuousOn degenerate R) (hDB : IsIndependentOn degenerate binary R)
    (hBD : IsIndependentOn binary degenerate R) : HasExpectedUtility R := by
  have := hR.isComplete.toTotal
  have := hR.isTransitive.toIsTrans
  rw [isMixtureContinuousOn_iff_lottery, image_ofFinDist_degenerate] at hC
  rw [isIndependentOn_iff_lottery, image_ofFinDist_degenerate, image_ofFinDist_binary] at hDB hBD
  exact hasExpectedUtility_iff_lottery.2
    (Lottery.hasExpectedUtility_of_isIndependentOn ⟨isComplete_of_total, isTransitive_of_isTrans⟩
      hC hDB hBD)

/-- **The expected utility theorem**: a preference has expected utility iff it is continuous in
mixtures and independent. -/
theorem hasExpectedUtility_iff_isMixtureContinuous_and_isIndependent
    (hR : IsPreferenceRelation R) :
    HasExpectedUtility R ↔ IsMixtureContinuous R ∧ IsIndependent R := by
  rw [hasExpectedUtility_iff_lottery, isMixtureContinuous_iff_lottery, isIndependent_iff_lottery]
  have := hR.isComplete.toTotal
  have := hR.isTransitive.toIsTrans
  exact Lottery.hasExpectedUtility_iff_isMixtureContinuous_and_isIndependent
    ⟨isComplete_of_total, isTransitive_of_isTrans⟩

end FinDist

end MathEconLib.DecisionTheory

/-! ### Worked examples -/

section Examples

open MathEconLib.DecisionTheory (Lottery)
open MathEconLib.DecisionTheory.Lottery MathEconLib.Preference Convexity

example : expectedUtility (fun x : ℝ => x)
    (mix ⟨0.25, by norm_num, by norm_num⟩ (.single 3000) (.single 0)) = 750 := by
  simp; norm_num

/-- The Allais paradox: `U(L₁) − U(R₁)` is a quarter of `U(L₂) − U(R₂)` for every `v`. -/
example (v : ℝ → ℝ) :
    expectedUtility v (mix ⟨0.2, by norm_num, by norm_num⟩ (.single 4000) (.single 0)) -
      expectedUtility v (mix ⟨0.25, by norm_num, by norm_num⟩ (.single 3000) (.single 0)) =
    (expectedUtility v (mix ⟨0.8, by norm_num, by norm_num⟩ (.single 4000) (.single 0)) -
      expectedUtility v (.single 3000)) / 4 := by
  simp; ring

example : IsIndependent (UtilityRel fun p : Lottery (Fin 2) =>
    expectedUtility (fun z => if z = 0 then 1 else 0) p) :=
  isIndependent_of_represents (represents_utilityRel _)

/-- `−v` is not a Bernoulli function for the relation of `v`. -/
example : ¬ Represents (expectedUtility fun z : Fin 2 => -1 * (z : ℝ) + 0)
    (UtilityRel (expectedUtility fun z : Fin 2 => (z : ℝ))) := by
  intro h
  have := (h (.single 1) (.single 0)).1 (by simp)
  norm_num at this

end Examples
