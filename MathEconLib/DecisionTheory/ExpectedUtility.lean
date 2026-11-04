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

/-!
# Expected utility

The *expected utility* of a lottery `p` with respect to a function `v : Z → ℝ` (the Bernoulli
function) is `U(p) = ∑_z p(z) v(z)`. A relation `≿` over lotteries is *consistent with expected
utility* if some `U` of this form represents it. Such relations satisfy independence and
continuity, and their Bernoulli function is unique up to a positive affine transformation.
Conversely, on a finite set of prizes, a continuous and independent preference relation is
consistent with expected utility: the expected utility theorem of von Neumann and Morgenstern.

## Main definitions

* `MathEconLib.DecisionTheory.expectedUtility v p`: `∑_z p(z) v(z)`.
* `MathEconLib.DecisionTheory.HasExpectedUtility R`: some `expectedUtility v` represents `R`. That
  `v` is a Bernoulli function for `R` is `Represents (expectedUtility v) R`.

## Main statements

* `expectedUtility_single`, `expectedUtility_mix`, `expectedUtility_iConvexComb`,
  `isAffineMap_expectedUtility`: `U([z]) = v(z)` and `U` is affine.
* `isIndependent_of_represents`, `isMixtureContinuous_of_represents` (Proposition 3.1): a relation
  consistent with expected utility satisfies independence and continuity, for all lotteries.
* `represents_expectedUtility_mul_add`, `exists_eq_mul_add_of_represents` (the Comment after
  Proposition 3.2): `a v + b` with `a > 0` is a Bernoulli function whenever `v` is, and any two
  Bernoulli functions for the same relation are related in this way.
* `hasExpectedUtility_of_isIndependentOn` (Proposition 3.2): on a finite set of prizes, a
  preference relation that is continuous on degenerate lotteries and satisfies independence
  between degenerate and binary lotteries, in both orientations, is consistent with expected
  utility.
* `hasExpectedUtility_iff_isMixtureContinuous_and_isIndependent`: on a finite set of prizes, a
  preference relation is consistent with expected utility if and only if it is continuous in
  mixtures and independent.

## Implementation notes

* `expectedUtility v p` is Mathlib's `p.iConvexComb v` into `ℝ`, the affine extension
  `StdSimplex.affineMapMk v` of `v`; `expectedUtility_eq_sum` gives the sum.
* `hasExpectedUtility_of_isIndependentOn` assumes Osborne and Rubinstein's Definition 3.2
  (continuity among degenerate lotteries) and Definition 3.4 (independence with a degenerate
  lottery on the left) together with its mirror image, which their proof also uses.

## References

Martin J. Osborne and Ariel Rubinstein (2023), *Models in Microeconomic Theory*, expanded second
edition, Open Book Publishers, Section 3.3 (Definition 3.5, Propositions 3.1 and 3.2, and the
Comment after Proposition 3.2). [DOI: 10.11647/OBP.0361](https://doi.org/10.11647/OBP.0361).

John von Neumann and Oskar Morgenstern (1947), *Theory of Games and Economic Behavior*, second
edition, Princeton University Press, pages 15–29 and 617–628.

## Tags

expected utility, von Neumann–Morgenstern, Bernoulli function, independence axiom, lottery
-/

@[expose] public section

namespace MathEconLib.DecisionTheory

open Convexity MathEconLib.Preference Lottery

universe u v

variable {Z : Type u} {I : Type v} {R : Lottery Z → Lottery Z → Prop} {v w : Z → ℝ}

/-- The *expected utility* `U(p) = ∑_z p(z) v(z)` of the lottery `p` with respect to the Bernoulli
function `v : Z → ℝ` (Mathlib's `p.iConvexComb v`). -/
noncomputable def expectedUtility (v : Z → ℝ) (p : Lottery Z) : ℝ := p.iConvexComb v

/-- `≿` is *consistent with expected utility*: some expected utility function
`U(p) = ∑_z p(z) v(z)` represents it. -/
def HasExpectedUtility (R : Lottery Z → Lottery Z → Prop) : Prop :=
  ∃ v : Z → ℝ, Represents (expectedUtility v) R

/-! ### Interface -/

theorem hasExpectedUtility_iff :
    HasExpectedUtility R ↔ ∃ v : Z → ℝ, Represents (expectedUtility v) R :=
  Iff.rfl

/-- `U(p) = ∑_z p(z) v(z)`. -/
theorem expectedUtility_eq_sum (v : Z → ℝ) (p : Lottery Z) :
    expectedUtility v p = p.weights.sum fun z a => a * v z := by
  simp [expectedUtility]

theorem expectedUtility_eq_sum_fintype [Fintype Z] (v : Z → ℝ) (p : Lottery Z) :
    expectedUtility v p = ∑ z, p.weights z * v z := by
  rw [expectedUtility_eq_sum, Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]

/-- `U([z]) = v(z)`. -/
@[simp]
theorem expectedUtility_single (v : Z → ℝ) (z : Z) :
    expectedUtility v (.single z) = v z := by
  simp [expectedUtility]

/-- `U(α · p ⊕ (1 − α) · q) = α U(p) + (1 − α) U(q)`. -/
@[simp]
theorem expectedUtility_mix (v : Z → ℝ) (α : Set.Icc (0 : ℝ) 1) (p q : Lottery Z) :
    expectedUtility v (mix α p q) = α * expectedUtility v p + (1 - α) * expectedUtility v q := by
  have h := (StdSimplex.affineMapMk (R := ℝ) v).isAffineMap.map_convexCombPair
    α.2.1 (sub_nonneg.2 α.2.2) (add_sub_cancel _ _) p q
  simp only [StdSimplex.affineMapMk_apply] at h
  rw [expectedUtility, mix, h]
  simp [expectedUtility]

/-- The expected utility of a compound lottery is the weighted sum of the expected utilities. -/
theorem expectedUtility_iConvexComb (v : Z → ℝ) (w : StdSimplex ℝ I) (f : I → Lottery Z) :
    expectedUtility v (w.iConvexComb f) = w.weights.sum fun i a => a * expectedUtility v (f i) := by
  have h := (StdSimplex.affineMapMk (R := ℝ) v).isAffineMap.map_iConvexComb w f
  simp only [StdSimplex.affineMapMk_apply] at h
  rw [expectedUtility, h]
  simp [expectedUtility, StdSimplex.affineMapMk_apply]

/-- Expected utility is affine on lotteries. -/
theorem isAffineMap_expectedUtility (v : Z → ℝ) : IsAffineMap ℝ (expectedUtility v) :=
  (StdSimplex.affineMapMk (R := ℝ) v).isAffineMap

/-- The expected utility for `a v + b` is `a U + b`. -/
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

/-- **Proposition 3.1 (independence).** A relation represented by an expected utility function
satisfies the independence property for all lotteries. -/
theorem isIndependent_of_represents (h : Represents (expectedUtility v) R) : IsIndependent R := by
  rw [isIndependent_iff]
  intro p q r α hα
  rw [h p q, h (mix α p r) (mix α q r), expectedUtility_mix, expectedUtility_mix]
  constructor
  · intro hle; nlinarith
  · intro hle; exact le_of_mul_le_mul_left (by linarith) hα

/-- **Proposition 3.1 (continuity).** A relation represented by an expected utility function is
continuous in mixtures, for all lotteries. -/
theorem isMixtureContinuous_of_represents (h : Represents (expectedUtility v) R) :
    IsMixtureContinuous R := by
  rw [isMixtureContinuous_iff]
  intro p q r hpq hqr
  rw [h.strictPart_iff] at hpq hqr
  have hpr : 0 < expectedUtility v p - expectedUtility v r := by linarith
  refine ⟨⟨(expectedUtility v q - expectedUtility v r) /
      (expectedUtility v p - expectedUtility v r),
    Set.mem_Icc.2 ⟨div_nonneg (by linarith) hpr.le, (div_le_one hpr).2 (by linarith)⟩⟩,
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

/-- **Section 3.3, Comment.** If `v` is a Bernoulli function for `≿`, so is `a v + b` for every
`a > 0` and every `b`. -/
theorem represents_expectedUtility_mul_add (h : Represents (expectedUtility v) R) {a : ℝ}
    (ha : 0 < a) (b : ℝ) : Represents (expectedUtility fun z => a * v z + b) R := by
  intro p q
  rw [expectedUtility_mul_add, expectedUtility_mul_add]
  exact h.affine ha b p q

/-- **Section 3.3, Comment.** Two Bernoulli functions `v`, `w` for the same relation differ by a
positive affine transformation: `w = a v + b` for some `a > 0` and `b`. Osborne and Rubinstein omit
the proof. -/
theorem exists_eq_mul_add_of_represents (hv : Represents (expectedUtility v) R)
    (hw : Represents (expectedUtility w) R) :
    ∃ a > (0 : ℝ), ∃ b : ℝ, ∀ z, w z = a * v z + b := by
  -- If `v` is constant, so is `w`. Otherwise fix `v b < v a`; for each `z`,
  -- `(v a − v b)(w z − w b) = (w a − w b)(v z − v b)` follows from two lotteries with equal
  -- `v`-utility, which then have equal `w`-utility.
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
    · -- `ε · [z] ⊕ (1 − ε) · [b]` and `η · [a] ⊕ (1 − η) · [b]` have equal `v`-utility
      have hs : 0 < (v z - v b) + (v a - v b) := by linarith
      let ε : Set.Icc (0 : ℝ) 1 := ⟨(v a - v b) / ((v z - v b) + (v a - v b)),
        Set.mem_Icc.2 ⟨div_nonneg hd.le hs.le, (div_le_one hs).2 (by linarith)⟩⟩
      let η : Set.Icc (0 : ℝ) 1 := ⟨(v z - v b) / ((v z - v b) + (v a - v b)),
        Set.mem_Icc.2 ⟨div_nonneg (by linarith) hs.le, (div_le_one hs).2 (by linarith)⟩⟩
      have h := K (mix ε (.single z) (.single b)) (mix η (.single a) (.single b)) (by
        simp only [expectedUtility_mix, expectedUtility_single, ε, η]
        field_simp
        ring)
      simp only [expectedUtility_mix, expectedUtility_single, ε, η] at h
      have h1 : (v a - v b) / ((v z - v b) + (v a - v b)) * (w z - w b) =
          (v z - v b) / ((v z - v b) + (v a - v b)) * (w a - w b) := by linarith
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_left_inj' hs.ne'] at h1
      linear_combination h1
    · -- `t · [z] ⊕ (1 − t) · [a]` and `[b]` have equal `v`-utility
      have he : 0 < v a - v z := by linarith
      let t : Set.Icc (0 : ℝ) 1 := ⟨(v a - v b) / (v a - v z),
        Set.mem_Icc.2 ⟨div_nonneg hd.le he.le, (div_le_one he).2 (by linarith)⟩⟩
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

/-- **Proposition 3.2 (von Neumann and Morgenstern).** Let `Z` be a finite set of prizes and `≿` a
preference relation over lotteries on `Z` that is continuous on degenerate lotteries and satisfies
the independence property between degenerate and binary lotteries, in both orientations. Then `≿`
is consistent with expected utility. Osborne and Rubinstein's Definition 3.4 states one
orientation; their proof uses both. -/
theorem hasExpectedUtility_of_isIndependentOn [Finite Z] (hR : IsPreferenceRelation R)
    (hC : IsMixtureContinuousOn degenerate R) (hDB : IsIndependentOn degenerate binary R)
    (hBD : IsIndependentOn binary degenerate R) : HasExpectedUtility R := by
  classical
  rcases isEmpty_or_nonempty Z with hZ | hZ
  · exact ⟨0, fun p => absurd p.nonempty (not_nonempty_iff.2 hZ)⟩
  have htrans : IsTransitive (Indiff R) := hR.isTransitive.indiff
  have hDD : IsIndependentOn degenerate degenerate R :=
    hDB.mono subset_rfl degenerate_subset_binary
  -- a best prize `a` and a worst prize `b`
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
    -- every prize is indifferent to a mixture of `a` and `b` (the only use of continuity)
    have hex : ∀ z, ∃ t : Set.Icc (0 : ℝ) 1,
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
    let tv : Z → Set.Icc (0 : ℝ) 1 := fun z => if z = a then 1 else if z = b then 0 else t z
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
    -- `p ∼ ∑_z p(z) · m z`, by independence
    have hrepl := hDB.indiff_iConvexComb hR hBD m {a, b} hm (fun z => mix_mem_binary _ _ _) hmT hT
    -- the compound lottery is a mixture of `a` and `b` with probability `U(p)`
    let U : Lottery Z → ℝ := expectedUtility fun z => (tv z : ℝ)
    have hU : ∀ p, (U p) ∈ Set.Icc (0 : ℝ) 1 := by
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
    -- by monotonicity, `p ≿ q` if and only if `U q ≤ U p`
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
  · -- all prizes are indifferent, hence all lotteries are
    have hba : R (.single b) (.single a) := by
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

/-- **The expected utility theorem.** On a finite set of prizes, a preference relation over
lotteries is consistent with expected utility if and only if it is continuous in mixtures and
satisfies the independence property. -/
theorem hasExpectedUtility_iff_isMixtureContinuous_and_isIndependent [Finite Z]
    (hR : IsPreferenceRelation R) :
    HasExpectedUtility R ↔ IsMixtureContinuous R ∧ IsIndependent R :=
  ⟨fun h => ⟨h.isMixtureContinuous, h.isIndependent⟩, fun ⟨hC, hI⟩ =>
    hasExpectedUtility_of_isIndependentOn hR (hC.isMixtureContinuousOn _)
      (hI.isIndependentOn _ _) (hI.isIndependentOn _ _)⟩

end MathEconLib.DecisionTheory

/-! ### Worked examples -/

section Examples

open MathEconLib.DecisionTheory MathEconLib.DecisionTheory.Lottery MathEconLib.Preference Convexity

example : expectedUtility (fun x : ℝ => x)
    (mix ⟨0.25, by norm_num, by norm_num⟩ (.single 3000) (.single 0)) = 750 := by
  simp; norm_num

/-- The Allais lotteries: under every Bernoulli function, `U(L₁) − U(R₁)` is a quarter of
`U(L₂) − U(R₂)`, with `L₁ = 0.2 · 4000 ⊕ 0.8 · 0`, `R₁ = 0.25 · 3000 ⊕ 0.75 · 0`,
`L₂ = 0.8 · 4000 ⊕ 0.2 · 0`, `R₂ = [3000]`; so no expected utility relation has `L₁ ≻ R₁` and
`R₂ ≻ L₂`. -/
example (v : ℝ → ℝ) :
    expectedUtility v (mix ⟨0.2, by norm_num, by norm_num⟩ (.single 4000) (.single 0)) -
      expectedUtility v (mix ⟨0.25, by norm_num, by norm_num⟩ (.single 3000) (.single 0)) =
    (expectedUtility v (mix ⟨0.8, by norm_num, by norm_num⟩ (.single 4000) (.single 0)) -
      expectedUtility v (.single 3000)) / 4 := by
  simp; ring

/-- The relation "more probability on the prize `0` is better" has the Bernoulli function
`1_{z = 0}`, so it satisfies independence (Proposition 3.1). -/
example : IsIndependent (UtilityRel fun p : Lottery (Fin 2) =>
    expectedUtility (fun z => if z = 0 then 1 else 0) p) :=
  isIndependent_of_represents (represents_utilityRel _)

/-- `−v` is not a Bernoulli function for the relation of `v`: for `v = id` on `Fin 2` it reverses
`[1] ≻ [0]`. -/
example : ¬ Represents (expectedUtility fun z : Fin 2 => -1 * (z : ℝ) + 0)
    (UtilityRel (expectedUtility fun z : Fin 2 => (z : ℝ))) := by
  intro h
  have := (h (.single 1) (.single 0)).1 (by simp)
  norm_num at this

end Examples
