/-
Copyright (c) 2026 Ritik Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ritik Jain
-/
module

public import MathEconLib.Decision.Lottery
public import MathEconLib.Preferences.Representation.Basic

/-!
# The independence property

A preference `R` over lotteries is *mixture independent on `(P, Q)`* if
`q ≼[R] p ↔ α · q ⊕ (1 − α) · r ≼[R] α · p ⊕ (1 − α) · r` for `p ∈ P`, `q ∈ Q`, every lottery `r`
and `0 < α ≤ 1`. Mixing both sides with a common lottery `r` does not change their comparison.

## Main definitions

* `IsMixtureIndependentOn`: the independence property for `p ∈ P` and `q ∈ Q`.
* `IsMixtureIndependent`: the independence property for all lotteries.

## Main statements

* `IsMixtureIndependentOn.lt_mixture_iff`: **Lemma 3.1**, monotonicity in the probability.
* `IsMixtureIndependentOn.antisymmRel_finMixture`: replacing prizes by indifferent binary
  lotteries.

## Implementation notes

* Osborne and Rubinstein's Definition 3.4 is `IsMixtureIndependentOn degenerate binary`: `p` is a
  sure prize and `q` a binary lottery. Their proof of Proposition 3.2 also uses the reverse
  comparison, `IsMixtureIndependentOn binary degenerate`, which is assumed here explicitly.
* `α = 0` is excluded, since then both mixtures are `r`.

## References

* M. J. Osborne, A. Rubinstein, *Models in Microeconomic Theory* (2023), Sections 3.2 and 3.3
-/

@[expose] public section

namespace MathEconLib.Decision

open MathEconLib.Probability MathEconLib.Preferences

universe u

variable {Z : Type u} [Fintype Z] {R : Preference (FinDist Z)} {P Q P' Q' : Set (FinDist Z)}

/-- The *independence property on `(P, Q)`*: for `p ∈ P`, `q ∈ Q` and `0 < α ≤ 1`,
`q ≼[R] p ↔ α · q ⊕ (1 − α) · r ≼[R] α · p ⊕ (1 − α) · r`. -/
def IsMixtureIndependentOn (P Q : Set (FinDist Z)) (R : Preference (FinDist Z)) : Prop :=
  ∀ p ∈ P, ∀ q ∈ Q, ∀ (r : FinDist Z) (α : unitInterval), 0 < (α : ℝ) →
    (q ≼[R] p ↔ FinDist.mixture α q r ≼[R] FinDist.mixture α p r)

/-- The *independence property* on all lotteries. -/
def IsMixtureIndependent (R : Preference (FinDist Z)) : Prop :=
  IsMixtureIndependentOn Set.univ Set.univ R

theorem isMixtureIndependentOn_iff : IsMixtureIndependentOn P Q R ↔
    ∀ p ∈ P, ∀ q ∈ Q, ∀ (r : FinDist Z) (α : unitInterval), 0 < (α : ℝ) →
      (q ≼[R] p ↔ FinDist.mixture α q r ≼[R] FinDist.mixture α p r) :=
  Iff.rfl

theorem isMixtureIndependent_iff : IsMixtureIndependent R ↔
    ∀ (p q r : FinDist Z) (α : unitInterval), 0 < (α : ℝ) →
      (q ≼[R] p ↔ FinDist.mixture α q r ≼[R] FinDist.mixture α p r) :=
  ⟨fun h p q => h p trivial q trivial, fun h p _ q _ => h p q⟩

theorem IsMixtureIndependentOn.le_iff (h : IsMixtureIndependentOn P Q R) {p q : FinDist Z}
    (hp : p ∈ P) (hq : q ∈ Q) (r : FinDist Z) {α : unitInterval} (hα : 0 < (α : ℝ)) :
    q ≼[R] p ↔ FinDist.mixture α q r ≼[R] FinDist.mixture α p r :=
  h p hp q hq r α hα

theorem IsMixtureIndependentOn.mono (h : IsMixtureIndependentOn P Q R) (hP : P' ⊆ P)
    (hQ : Q' ⊆ Q) :
    IsMixtureIndependentOn P' Q' R :=
  fun p hp q hq => h p (hP hp) q (hQ hq)

theorem IsMixtureIndependent.isMixtureIndependentOn (h : IsMixtureIndependent R)
    (P Q : Set (FinDist Z)) :
    IsMixtureIndependentOn P Q R :=
  h.mono (Set.subset_univ P) (Set.subset_univ Q)

theorem IsMixtureIndependentOn.lt_iff (hPQ : IsMixtureIndependentOn P Q R)
    (hQP : IsMixtureIndependentOn Q P R)
    {p q : FinDist Z} (hp : p ∈ P) (hq : q ∈ Q) (r : FinDist Z) {α : unitInterval}
    (hα : 0 < (α : ℝ)) :
    q ≺[R] p ↔ FinDist.mixture α q r ≺[R] FinDist.mixture α p r :=
  and_congr (hPQ.le_iff hp hq r hα) (not_congr (hQP.le_iff hq hp r hα))

theorem IsMixtureIndependentOn.antisymmRel_iff (hPQ : IsMixtureIndependentOn P Q R)
    (hQP : IsMixtureIndependentOn Q P R) {p q : FinDist Z} (hp : p ∈ P) (hq : q ∈ Q) (r : FinDist Z)
    {α : unitInterval} (hα : 0 < (α : ℝ)) :
    p ~[R] q ↔ FinDist.mixture α p r ~[R] FinDist.mixture α q r :=
  and_congr (hQP.le_iff hq hp r hα) (hPQ.le_iff hp hq r hα)

/-! ### Monotonicity -/

section Monotonicity

variable [DecidableEq Z]

/-- **Lemma 3.1**: if `[b] ≺ [a]`, then `β · a ⊕ (1 − β) · b ≺ α · a ⊕ (1 − α) · b` iff `β < α`.
-/
theorem IsMixtureIndependentOn.lt_mixture_iff (hI : IsMixtureIndependentOn degenerate degenerate R)
    {a b : Z}
    (hab : FinDist.pure b ≺[R] FinDist.pure a) (α β : unitInterval) :
    (β : ℝ) < α ↔ FinDist.mixture β (FinDist.pure a) (FinDist.pure b) ≺[R]
      FinDist.mixture α (FinDist.pure a) (FinDist.pure b) := by
  have key : ∀ α β : unitInterval, (β : ℝ) < α →
      FinDist.mixture β (FinDist.pure a) (FinDist.pure b) ≺[R]
        FinDist.mixture α (FinDist.pure a) (FinDist.pure b) := by
    intro α β hβα
    rcases lt_or_eq_of_le (show (α : ℝ) - β ≤ 1 by linarith [α.2.2, β.2.1]) with hlt | heq
    · obtain ⟨t, β', ht, h1, h2⟩ := exists_mixture_pure_eq_mixture a b hβα hlt
      rw [h1, h2]
      exact (hI.lt_iff hI (pure_mem_degenerate a) (pure_mem_degenerate b) _
        (by rw [ht]; linarith)).1 hab
    · have hα : (α : ℝ) = 1 := by linarith [α.2.2, β.2.1]
      have hβ : (β : ℝ) = 0 := by linarith [α.2.2, β.2.1]
      rwa [FinDist.mixture_of_coe_eq_one hα, FinDist.mixture_of_coe_eq_zero hβ]
  refine ⟨key α β, fun h => ?_⟩
  by_contra hnot
  rcases (not_lt.1 hnot).lt_or_eq with hlt | heq
  · exact R.lt_asymm (key β α hlt) h
  · exact R.lt_irrefl _ (by rwa [Subtype.ext heq] at h)

/-- For complete `R` with `[b] ≺ [a]`, `β · a ⊕ (1 − β) · b ≼ α · a ⊕ (1 − α) · b` iff `β ≤ α`. -/
theorem IsMixtureIndependentOn.le_mixture_iff {R : CompletePreference (FinDist Z)}
    (hI : IsMixtureIndependentOn degenerate degenerate R.toPreference) {a b : Z}
    (hab : FinDist.pure b ≺[R] FinDist.pure a) (α β : unitInterval) :
    FinDist.mixture β (FinDist.pure a) (FinDist.pure b) ≼[R]
      FinDist.mixture α (FinDist.pure a) (FinDist.pure b) ↔ (β : ℝ) ≤ α := by
  rw [← R.not_lt, ← hI.lt_mixture_iff hab, not_lt]

/-! ### Replacing prizes by indifferent lotteries -/

/-- If each `[z]` is indifferent to a binary lottery `m z` (with `m` fixing a finite `T` holding
all supports), then `p ∼ ∑_z p(z) · m z`. -/
theorem IsMixtureIndependentOn.antisymmRel_finMixture
    (hDB : IsMixtureIndependentOn degenerate binary R)
    (hBD : IsMixtureIndependentOn binary degenerate R) (m : Z → FinDist Z) (T : Finset Z)
    (hm : ∀ z, FinDist.pure z ~[R] m z) (hmB : ∀ z, m z ∈ binary)
    (hmT : ∀ z y, (m z).pmf y ≠ 0 → y ∈ T) (hT : ∀ t ∈ T, m t = FinDist.pure t)
    (p : FinDist Z) :
    p ~[R] FinDist.finMixture p m := by
  have hfix : ∀ q : FinDist Z, (∀ y, q.pmf y ≠ 0 → y ∈ T) → FinDist.finMixture q m = q := by
    intro q hq
    rw [FinDist.finMixture_congr (g := FinDist.pure) fun y hy => hT y (hq y hy),
      FinDist.finMixture_pure_right]
  -- Induction on the number of prizes of `p` outside `T`.
  suffices H : ∀ n : ℕ, ∀ p : FinDist Z,
      (Finset.univ.filter fun y => p.pmf y ≠ 0 ∧ y ∉ T).card ≤ n →
        p ~[R] FinDist.finMixture p m from
    H _ p le_rfl
  intro n
  induction n with
  | zero =>
    intro p hp
    have hsupp : ∀ y, p.pmf y ≠ 0 → y ∈ T := by
      intro y hy
      by_contra hyT
      have : y ∈ Finset.univ.filter fun y => p.pmf y ≠ 0 ∧ y ∉ T :=
        Finset.mem_filter.2 ⟨Finset.mem_univ y, hy, hyT⟩
      rw [Finset.card_eq_zero.1 (Nat.le_zero.1 hp)] at this
      exact absurd this (Finset.notMem_empty y)
    rw [hfix p hsupp]
  | succ n ih =>
    intro p hp
    by_cases hall : ∀ y, p.pmf y ≠ 0 → y ∈ T
    · rw [hfix p hall]
    push Not at hall
    obtain ⟨z, hz, hzT⟩ := hall
    rcases (p.pmf_le_one z).lt_or_eq with hlt | heq
    · obtain ⟨r, hrz, hrsupp, hpr⟩ := p.exists_eq_mixture_pure z hlt
      set α : unitInterval := ⟨p.pmf z, p.nonneg z, hlt.le⟩ with hαdef
      have hα : 0 < (α : ℝ) := lt_of_le_of_ne (p.nonneg z) (Ne.symm hz)
      set q := FinDist.mixture α (m z) r with hq
      have hpq : p ~[R] q := by
        rw [hpr]
        exact ⟨(hBD.le_iff (hmB z) (pure_mem_degenerate z) r hα).1 (hm z).1,
          (hDB.le_iff (pure_mem_degenerate z) (hmB z) r hα).1 (hm z).2⟩
      have hcard : (Finset.univ.filter fun y => q.pmf y ≠ 0 ∧ y ∉ T).card ≤ n := by
        have hsub : (Finset.univ.filter fun y => q.pmf y ≠ 0 ∧ y ∉ T) ⊆
            (Finset.univ.filter fun y => p.pmf y ≠ 0 ∧ y ∉ T).erase z := by
          intro y hy
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
          have hmy : (m z).pmf y = 0 := by
            by_contra h; exact hy.2 (hmT z y h)
          have hry : r.pmf y ≠ 0 := by
            intro h; apply hy.1; rw [hq, FinDist.mixture_pmf, hmy, h]; ring
          refine Finset.mem_erase.2 ⟨?_, Finset.mem_filter.2
            ⟨Finset.mem_univ y, fun h => hry (hrsupp y h), hy.2⟩⟩
          rintro rfl; exact hry hrz
        have hzmem : z ∈ Finset.univ.filter fun y => p.pmf y ≠ 0 ∧ y ∉ T :=
          Finset.mem_filter.2 ⟨Finset.mem_univ z, hz, hzT⟩
        have := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hzmem] at this
        omega
      have hqm := ih q hcard
      have hcomp : FinDist.finMixture q m = FinDist.finMixture p m := by
        have hmz : FinDist.finMixture (m z) m = m z := hfix (m z) (hmT z)
        conv_rhs => rw [hpr]
        rw [hq, FinDist.finMixture_mixture, FinDist.finMixture_mixture, hmz,
          FinDist.finMixture_pure_left]
      rw [← hcomp]
      exact hpq.trans hqm
    · have hp1 : p = FinDist.pure z := FinDist.eq_pure_of_pmf_eq_one heq
      subst hp1
      rw [FinDist.finMixture_pure_left]
      exact hm z

end Monotonicity

end MathEconLib.Decision

/-! ### Worked examples -/

section Examples

open MathEconLib.Probability MathEconLib.Decision MathEconLib.Preferences

/-- Ranking lotteries by the probability of the prize `0` satisfies independence. -/
example : IsMixtureIndependent (Preference.ofUtility fun p : FinDist (Fin 2) => p.pmf 0) := by
  rw [isMixtureIndependent_iff]
  intro p q r α hα
  simp only [Preference.ofUtility_le_iff, FinDist.mixture_pmf]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

example (R : Preference (FinDist (Fin 2))) (hI : IsMixtureIndependentOn degenerate degenerate R)
    (h01 : FinDist.pure 1 ≺[R] FinDist.pure 0) :
    FinDist.mixture ⟨0.2, by norm_num, by norm_num⟩ (FinDist.pure 0) (FinDist.pure 1) ≺[R]
      FinDist.mixture ⟨0.7, by norm_num, by norm_num⟩ (FinDist.pure 0) (FinDist.pure 1) :=
  (hI.lt_mixture_iff h01 _ _).1 (by norm_num)

/-- Why `α = 0` is excluded. -/
example (p q r : FinDist (Fin 2)) : FinDist.mixture 0 p r = FinDist.mixture 0 q r := by simp

end Examples
