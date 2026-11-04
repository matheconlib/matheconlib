/-
Copyright (c) 2026 Ritik Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ritik Jain
-/
module

public import MathEconLib.DecisionTheory.Lottery
public import MathEconLib.Preference.Basic

/-!
# The independence property

`≿` is *independent on `(P, Q)`* if `p ≿ q ↔ α · p ⊕ (1 − α) · r ≿ α · q ⊕ (1 − α) · r` for
`p ∈ P`, `q ∈ Q`, every lottery `r` and `0 < α ≤ 1`.

## Main statements

* `Lottery.IsIndependentOn.strictPart_mix_iff`: **Lemma 3.1**, monotonicity in the probability.
* `Lottery.IsIndependentOn.indiff_iConvexComb`: replacing prizes by indifferent binary lotteries.

## Implementation notes

* Osborne and Rubinstein's Definition 3.4 is `IsIndependentOn degenerate binary`; their proof of
  Proposition 3.2 also uses `IsIndependentOn binary degenerate`, assumed here explicitly.

## References

* M. J. Osborne, A. Rubinstein, *Models in Microeconomic Theory* (2023), Sections 3.2 and 3.3
-/

@[expose] public section

namespace MathEconLib.DecisionTheory

open Convexity MathEconLib.Preference

universe u

namespace Lottery

variable {Z : Type u} {R : Lottery Z → Lottery Z → Prop} {P Q P' Q' : Set (Lottery Z)}

/-- The *independence property on `(P, Q)`*: `p ≿ q ↔ α · p ⊕ (1 − α) · r ≿ α · q ⊕ (1 − α) · r`
for `p ∈ P`, `q ∈ Q` and `0 < α ≤ 1`. -/
def IsIndependentOn (P Q : Set (Lottery Z)) (R : Lottery Z → Lottery Z → Prop) : Prop :=
  ∀ p ∈ P, ∀ q ∈ Q, ∀ (r : Lottery Z) (α : unitInterval), 0 < (α : ℝ) →
    (R p q ↔ R (mix α p r) (mix α q r))

/-- The *independence property* on all lotteries. -/
def IsIndependent (R : Lottery Z → Lottery Z → Prop) : Prop :=
  IsIndependentOn Set.univ Set.univ R

theorem isIndependentOn_iff : IsIndependentOn P Q R ↔
    ∀ p ∈ P, ∀ q ∈ Q, ∀ (r : Lottery Z) (α : unitInterval), 0 < (α : ℝ) →
      (R p q ↔ R (mix α p r) (mix α q r)) :=
  Iff.rfl

theorem isIndependent_iff : IsIndependent R ↔
    ∀ (p q r : Lottery Z) (α : unitInterval), 0 < (α : ℝ) →
      (R p q ↔ R (mix α p r) (mix α q r)) :=
  ⟨fun h p q => h p trivial q trivial, fun h p _ q _ => h p q⟩

theorem IsIndependentOn.rel_iff (h : IsIndependentOn P Q R) {p q : Lottery Z} (hp : p ∈ P)
    (hq : q ∈ Q) (r : Lottery Z) {α : unitInterval} (hα : 0 < (α : ℝ)) :
    R p q ↔ R (mix α p r) (mix α q r) :=
  h p hp q hq r α hα

theorem IsIndependentOn.mono (h : IsIndependentOn P Q R) (hP : P' ⊆ P) (hQ : Q' ⊆ Q) :
    IsIndependentOn P' Q' R :=
  fun p hp q hq => h p (hP hp) q (hQ hq)

theorem IsIndependent.isIndependentOn (h : IsIndependent R) (P Q : Set (Lottery Z)) :
    IsIndependentOn P Q R :=
  h.mono (Set.subset_univ P) (Set.subset_univ Q)

theorem IsIndependentOn.strictPart_iff (hPQ : IsIndependentOn P Q R) (hQP : IsIndependentOn Q P R)
    {p q : Lottery Z} (hp : p ∈ P) (hq : q ∈ Q) (r : Lottery Z) {α : unitInterval}
    (hα : 0 < (α : ℝ)) :
    StrictPart R p q ↔ StrictPart R (mix α p r) (mix α q r) := by
  rw [Preference.strictPart_iff, Preference.strictPart_iff, hPQ.rel_iff hp hq r hα,
    hQP.rel_iff hq hp r hα]

theorem IsIndependentOn.indiff_iff (hPQ : IsIndependentOn P Q R) (hQP : IsIndependentOn Q P R)
    {p q : Lottery Z} (hp : p ∈ P) (hq : q ∈ Q) (r : Lottery Z) {α : unitInterval}
    (hα : 0 < (α : ℝ)) :
    Indiff R p q ↔ Indiff R (mix α p r) (mix α q r) := by
  rw [Preference.indiff_iff, Preference.indiff_iff, hPQ.rel_iff hp hq r hα,
    hQP.rel_iff hq hp r hα]

/-! ### Monotonicity -/

/-- **Lemma 3.1**: if `[a] ≻ [b]`, then `α · a ⊕ (1 − α) · b ≻ β · a ⊕ (1 − β) · b` iff `α > β`.
-/
theorem IsIndependentOn.strictPart_mix_iff (hI : IsIndependentOn degenerate degenerate R) {a b : Z}
    (hab : StrictPart R (.single a) (.single b)) (α β : unitInterval) :
    (β : ℝ) < α ↔ StrictPart R (mix α (.single a) (.single b)) (mix β (.single a) (.single b)) := by
  have key : ∀ α β : unitInterval, (β : ℝ) < α →
      StrictPart R (mix α (.single a) (.single b)) (mix β (.single a) (.single b)) := by
    intro α β hβα
    rcases lt_or_eq_of_le (show (α : ℝ) - β ≤ 1 by linarith [α.2.2, β.2.1]) with hlt | heq
    · obtain ⟨t, β', ht, h1, h2⟩ := mix_mix_single a b hβα hlt
      rw [h1, h2]
      exact (hI.strictPart_iff hI (single_mem_degenerate a) (single_mem_degenerate b) _
        (by rw [ht]; linarith)).1 hab
    · have hα : (α : ℝ) = 1 := by linarith [α.2.2, β.2.1]
      have hβ : (β : ℝ) = 0 := by linarith [α.2.2, β.2.1]
      rwa [mix_of_coe_eq_one hα, mix_of_coe_eq_zero hβ]
  refine ⟨key α β, fun h => ?_⟩
  by_contra hnot
  rcases (not_lt.1 hnot).lt_or_eq with hlt | heq
  · exact (key β α hlt).asymm h
  · exact strictPart_irrefl R _ (by rwa [Subtype.ext heq] at h)

/-- For complete `≿` with `[a] ≻ [b]`, `α · a ⊕ (1 − α) · b ≿ β · a ⊕ (1 − β) · b` iff `α ≥ β`. -/
theorem IsIndependentOn.rel_mix_iff (hI : IsIndependentOn degenerate degenerate R)
    (hC : IsComplete R) {a b : Z} (hab : StrictPart R (.single a) (.single b))
    (α β : unitInterval) :
    R (mix α (.single a) (.single b)) (mix β (.single a) (.single b)) ↔ (β : ℝ) ≤ α := by
  rw [hC.rel_iff_not_strictPart, ← hI.strictPart_mix_iff hab, not_lt]

/-! ### Replacing prizes by indifferent lotteries -/

/-- If each `[z]` is indifferent to a binary lottery `m z` (with `m` fixing a finite `T` holding
all supports), then `p ∼ ∑_z p(z) · m z`. -/
theorem IsIndependentOn.indiff_iConvexComb (hR : IsPreferenceRelation R)
    (hDB : IsIndependentOn degenerate binary R) (hBD : IsIndependentOn binary degenerate R)
    (m : Z → Lottery Z) (T : Finset Z) (hm : ∀ z, Indiff R (.single z) (m z))
    (hmB : ∀ z, m z ∈ binary) (hmT : ∀ z y, (m z).weights y ≠ 0 → y ∈ T)
    (hT : ∀ t ∈ T, m t = .single t) (p : Lottery Z) :
    Indiff R p (p.iConvexComb m) := by
  classical
  have htrans : IsTransitive (Indiff R) := hR.isTransitive.indiff
  have hfix : ∀ q : Lottery Z, (∀ y, q.weights y ≠ 0 → y ∈ T) → q.iConvexComb m = q := by
    intro q hq
    rw [iConvexComb_congr (g := StdSimplex.single) fun y hy => hT y (hq y hy),
      StdSimplex.iConvexComb_single]
  -- Induction on the number of prizes of `p` outside `T`.
  suffices H : ∀ n : ℕ, ∀ p : Lottery Z,
      (p.weights.support.filter (· ∉ T)).card ≤ n → Indiff R p (p.iConvexComb m) from
    H _ p le_rfl
  intro n
  induction n with
  | zero =>
    intro p hp
    have hsupp : ∀ y, p.weights y ≠ 0 → y ∈ T := by
      intro y hy
      by_contra hyT
      have : y ∈ p.weights.support.filter (· ∉ T) :=
        Finset.mem_filter.2 ⟨Finsupp.mem_support_iff.2 hy, hyT⟩
      rw [Finset.card_eq_zero.1 (Nat.le_zero.1 hp)] at this
      exact absurd this (Finset.notMem_empty y)
    rw [hfix p hsupp]
    exact ⟨hR.refl p, hR.refl p⟩
  | succ n ih =>
    intro p hp
    by_cases hall : ∀ y, p.weights y ≠ 0 → y ∈ T
    · rw [hfix p hall]
      exact ⟨hR.refl p, hR.refl p⟩
    push Not at hall
    obtain ⟨z, hz, hzT⟩ := hall
    rcases (StdSimplex.weights_apply_le_one p z).lt_or_eq with hlt | heq
    · obtain ⟨r, hrz, hrsupp, hpr⟩ := exists_eq_mix_single p z hlt
      set α : unitInterval := ⟨p.weights z, Set.mem_Icc.2 ⟨p.nonneg z, hlt.le⟩⟩ with hαdef
      have hα : 0 < (α : ℝ) := lt_of_le_of_ne (p.nonneg z) (Ne.symm hz)
      set q := mix α (m z) r with hq
      have hpq : Indiff R p q := by
        rw [hpr]
        exact ⟨(hDB.rel_iff (single_mem_degenerate z) (hmB z) r hα).1 (hm z).1,
          (hBD.rel_iff (hmB z) (single_mem_degenerate z) r hα).1 (hm z).2⟩
      have hcard : (q.weights.support.filter (· ∉ T)).card ≤ n := by
        have hsub : q.weights.support.filter (· ∉ T) ⊆
            (p.weights.support.filter (· ∉ T)).erase z := by
          intro y hy
          rw [Finset.mem_filter, Finsupp.mem_support_iff] at hy
          have hmy : (m z).weights y = 0 := by
            by_contra h; exact hy.2 (hmT z y h)
          have hry : r.weights y ≠ 0 := by
            intro h; apply hy.1; rw [hq, weights_mix, hmy, h]; ring
          refine Finset.mem_erase.2 ⟨?_, Finset.mem_filter.2
            ⟨Finsupp.mem_support_iff.2 fun h => hry (hrsupp y h), hy.2⟩⟩
          rintro rfl; exact hry hrz
        have hzmem : z ∈ p.weights.support.filter (· ∉ T) :=
          Finset.mem_filter.2 ⟨Finsupp.mem_support_iff.2 hz, hzT⟩
        have := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hzmem] at this
        omega
      have hqm := ih q hcard
      have hcomp : q.iConvexComb m = p.iConvexComb m := by
        have hmz : (m z).iConvexComb m = m z := hfix (m z) (hmT z)
        conv_rhs => rw [hpr]
        rw [hq, iConvexComb_mix, iConvexComb_mix, hmz, Convexity.iConvexComb_single]
      rw [← hcomp]
      exact htrans.trans hpq hqm
    · have hp1 : p = .single z := eq_single_of_weights_eq_one p z heq
      subst hp1
      rw [Convexity.iConvexComb_single]
      exact hm z

end Lottery

/-! ### Lotteries over a finite set of prizes -/

section FinDist

open MathEconLib.Probability

variable {Z : Type u} [Fintype Z] {R : FinDist Z → FinDist Z → Prop} {P Q : Set (FinDist Z)}

/-- The *independence property on `(P, Q)`*, for distributions. -/
def IsIndependentOn (P Q : Set (FinDist Z)) (R : FinDist Z → FinDist Z → Prop) : Prop :=
  ∀ p ∈ P, ∀ q ∈ Q, ∀ (r : FinDist Z) (α : unitInterval), 0 < (α : ℝ) →
    (R p q ↔ R (FinDist.mixture α p r) (FinDist.mixture α q r))

/-- The *independence property* on all distributions. -/
def IsIndependent (R : FinDist Z → FinDist Z → Prop) : Prop :=
  IsIndependentOn Set.univ Set.univ R

/-- Independence on `(P, Q)` is independence on lotteries on the images of `P` and `Q`. -/
theorem isIndependentOn_iff_lottery : IsIndependentOn P Q R ↔
    Lottery.IsIndependentOn (Lottery.ofFinDist '' P) (Lottery.ofFinDist '' Q)
      (Lottery.ofFinDist.symm ⁻¹'o R) := by
  simp only [IsIndependentOn, Lottery.IsIndependentOn, Set.forall_mem_image,
    Lottery.ofFinDist.surjective.forall, ← Lottery.ofFinDist_mixture, Order.Preimage,
    Equiv.symm_apply_apply]

theorem isIndependent_iff_lottery :
    IsIndependent R ↔ Lottery.IsIndependent (Lottery.ofFinDist.symm ⁻¹'o R) := by
  rw [IsIndependent, Lottery.IsIndependent, isIndependentOn_iff_lottery, Set.image_univ,
    Equiv.range_eq_univ]

end FinDist

end MathEconLib.DecisionTheory

/-! ### Worked examples -/

section Examples

open MathEconLib.DecisionTheory (Lottery)
open MathEconLib.DecisionTheory.Lottery MathEconLib.Preference Convexity

/-- Ranking lotteries by the probability of the prize `0` satisfies independence. -/
example : IsIndependent fun p q : Lottery (Fin 2) => q.weights 0 ≤ p.weights 0 := by
  rw [isIndependent_iff]
  intro p q r α hα
  simp only [weights_mix]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

example (R : Lottery (Fin 2) → Lottery (Fin 2) → Prop)
    (hI : IsIndependentOn degenerate degenerate R)
    (h01 : StrictPart R (.single 0) (.single 1)) :
    StrictPart R (mix ⟨0.7, by norm_num, by norm_num⟩ (.single 0) (.single 1))
      (mix ⟨0.2, by norm_num, by norm_num⟩ (.single 0) (.single 1)) :=
  (hI.strictPart_mix_iff h01 _ _).1 (by norm_num)

/-- Why `α = 0` is excluded. -/
example (p q r : Lottery (Fin 2)) : mix 0 p r = mix 0 q r := by simp

end Examples
