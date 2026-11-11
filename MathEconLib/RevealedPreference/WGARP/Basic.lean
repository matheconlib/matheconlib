/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLib.RevealedPreference.Basic

/-!
# Weak generalized revealed preference

WGARP excludes a weak direct comparison followed by a strict reverse comparison.
It allows ties and longer revealed-preference cycles. A numerical preference function
need not be transitive. Its rationalization requires a nonnegative comparison against
every affordable bundle, not just the absence of a strictly preferred alternative.

The preference properties below hold on the entire bundle space; observed budgets
remain restricted to nonnegative bundles. Neither a positive dimension nor nonzero
observed choices is required.

## References and provenance

Victor H. Aguiar, Per Hjertstrand, Roberto Serrano, and Özgür Evren (2026),
*A Rationalization of the Weak Axiom of Revealed Preference*,
[arXiv:1906.00296v2](https://arxiv.org/abs/1906.00296v2), revised August 12, 2026,
Theorem 1(i), (iv), and its necessity lemma.
Adapted from the Apache-2.0 [WGARP Lean](https://github.com/vaguiarl/wgarp-lean)
modules `Data` and `Necessity`. The finite rationalization equivalence is proved in
`WGARP.Characterization`; the matrix/simplex normal form is outside this contribution.
-/

@[expose] public section

set_option autoImplicit false

namespace MathEconLib.RevealedPreference

variable {L : ℕ} {T : Type*}

/-- A numerical comparison of two bundles, without a transitivity requirement. -/
abbrev PreferenceFunction (L : ℕ) := Bundle L → Bundle L → ℝ

/-- Strict increase in the first bundle under coordinatewise dominance with inequality. -/
def StrictlyIncreasingFirst (r : PreferenceFunction L) : Prop :=
  ∀ ⦃x z : Bundle L⦄ (y : Bundle L), StrictDominates x z → r z y < r x y

/-- Both sign implications in the paper's asymmetry condition, including ties. -/
def SignAsymmetric (r : PreferenceFunction L) : Prop :=
  (∀ x y, 0 ≤ r x y → r y x ≤ 0) ∧ (∀ x y, 0 < r x y → r y x < 0)

/-- Joint continuity of a numerical preference function. -/
def ContinuousPreference (r : PreferenceFunction L) : Prop :=
  Continuous (Function.uncurry r)

/-- Each observed bundle weakly dominates every bundle in its observed budget. -/
def PreferenceRationalizes (D : Dataset L T) (r : PreferenceFunction L) : Prop :=
  ∀ t y, Affordable D t y → 0 ≤ r (D.choice t) y

/-- A weak direct comparison cannot have a strict direct reverse comparison. -/
def WGARP (D : Dataset L T) : Prop :=
  ∀ s t, 0 ≤ expenditureGap D t s → expenditureGap D s t ≤ 0

/-- WGARP rules out exactly the weak/strict binary revealed-preference cycles. -/
theorem wgarp_iff_no_binary_cycle (D : Dataset L T) :
    WGARP D ↔ ∀ s t, ¬(0 ≤ expenditureGap D t s ∧ 0 < expenditureGap D s t) := by
  constructor
  · intro h s t hcycle
    exact (not_lt_of_ge (h s t hcycle.1)) hcycle.2
  · intro h s t hweak
    exact le_of_not_gt fun hstrict => h s t ⟨hweak, hstrict⟩

/-- Empty and singleton observation types satisfy WGARP. -/
theorem wgarp_of_subsingleton [Subsingleton T] (D : Dataset L T) : WGARP D := by
  intro s t
  have hst : s = t := Subsingleton.elim s t
  subst t
  simp

/-- A continuous, strictly increasing, asymmetric preference rationalization exists. -/
def HasRegularPreferenceRationalization (D : Dataset L T) : Prop :=
  ∃ r : PreferenceFunction L,
    ContinuousPreference r ∧ StrictlyIncreasingFirst r ∧ SignAsymmetric r ∧
      PreferenceRationalizes D r

/-- Necessity uses only strict increase, sign asymmetry, and budget rationalization. -/
theorem wgarp_of_asymmetric_strictlyIncreasing_rationalization
    (D : Dataset L T) (r : PreferenceFunction L)
    (hasym : SignAsymmetric r) (hinc : StrictlyIncreasingFirst r)
    (hrat : PreferenceRationalizes D r) : WGARP D := by
  intro s t hts
  by_contra hnot
  have hst : 0 < expenditureGap D s t := lt_of_not_ge hnot
  have hxt : Affordable D t (D.choice s) := by
    refine ⟨D.choice_nonneg s, ?_⟩
    rw [expenditureGap_eq] at hts
    linarith
  have hweak := hrat t (D.choice s) hxt
  obtain ⟨z, hzdom, hzbudget⟩ := exists_strictDominating_affordable D s t hst
  have hsweak := hrat s z hzbudget
  have hzpos : 0 < r z (D.choice s) :=
    lt_of_le_of_lt hweak (hinc (D.choice s) hzdom)
  exact (not_lt_of_ge hsweak) (hasym.2 z (D.choice s) hzpos)

end MathEconLib.RevealedPreference
