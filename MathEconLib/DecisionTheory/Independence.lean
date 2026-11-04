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

A relation `≿` over lotteries satisfies the *independence property* if mixing two lotteries with a
common third lottery does not change their ranking: `p ≿ q` if and only if
`α · p ⊕ (1 − α) · r ≿ α · q ⊕ (1 − α) · r`, for every lottery `r` and every `α ∈ (0, 1]`.

The property can be required for all pairs of lotteries (`IsIndependent`), or only for `p` in a set
`P` and `q` in a set `Q` (`IsIndependentOn P Q`), as `MonotoneOn` restricts `Monotone`. It is
defined for lotteries over a finite set of prizes as distributions `FinDist Z`, and in the
namespace `Lottery` for finitely supported lotteries over any set of prizes; `Lottery.ofFinDist`
transfers one to the other (`isIndependentOn_iff_lottery`).

## Main definitions

* `MathEconLib.DecisionTheory.IsIndependentOn P Q R`: for `p ∈ P`, `q ∈ Q`, every `r` and
  `α ∈ (0, 1]`, `p ≿ q ↔ α · p ⊕ (1 − α) · r ≿ α · q ⊕ (1 − α) · r`, for `FinDist Z`.
* `MathEconLib.DecisionTheory.IsIndependent R`: the same for all lotteries.
* `MathEconLib.DecisionTheory.Lottery.IsIndependentOn`, `Lottery.IsIndependent`: the same for
  `Lottery Z`.

## Main statements

* `isIndependentOn_iff_lottery`, `isIndependent_iff_lottery`: the two definitions agree under
  `Lottery.ofFinDist`.
* `Lottery.IsIndependentOn.mono`, `Lottery.IsIndependent.isIndependentOn`: restriction to smaller
  sets.
* `Lottery.IsIndependentOn.strictPart_iff`, `Lottery.IsIndependentOn.indiff_iff`: with both
  orientations, strict preference and indifference are transferred too.
* `Lottery.IsIndependentOn.strictPart_mix_iff` (Lemma 3.1): if `≿` satisfies independence between
  degenerate lotteries and `[a] ≻ [b]`, then `α · a ⊕ (1 − α) · b ≻ β · a ⊕ (1 − β) · b` if and
  only if `α > β`; `Lottery.IsIndependentOn.rel_mix_iff`: for a complete `≿`, `≿` between such
  lotteries is `≥` between the probabilities of `a`.
* `Lottery.IsIndependentOn.indiff_iConvexComb`: for a preference relation with independence between
  degenerate and binary lotteries in both orientations, if every prize `z` is indifferent to a
  binary lottery `m z`, and `m` fixes the prizes of a finite set `T` containing the supports of
  all `m z`, then every lottery `p` is indifferent to the compound lottery `∑_z p(z) · m z` (the
  replacement step of the proof of Proposition 3.2).

## Implementation notes

* `IsIndependentOn P Q R` has `p ∈ P` on the left of `≿`. Osborne and Rubinstein's Definition 3.4
  is `IsIndependentOn degenerate binary R`; their proof of Proposition 3.2 also uses the other
  orientation, `IsIndependentOn binary degenerate R`, which the theorems here assume explicitly.
  For `IsIndependent` the two orientations coincide.
* `α = 1` is allowed and trivial (`1 · p ⊕ 0 · r = p`). `α = 0` is excluded: for a reflexive `≿`
  it would make any two lotteries indifferent.
* Completeness and transitivity are not part of the property; theorems that use them assume them.

## References

Martin J. Osborne and Ariel Rubinstein (2023), *Models in Microeconomic Theory*, expanded second
edition, Open Book Publishers, Section 3.2 (Definition 3.4, Lemma 3.1) and Section 3.3 (proof of
Proposition 3.2). [DOI: 10.11647/OBP.0361](https://doi.org/10.11647/OBP.0361).

## Tags

independence axiom, expected utility, monotonicity, lottery
-/

@[expose] public section

namespace MathEconLib.DecisionTheory

open Convexity MathEconLib.Preference

universe u

namespace Lottery

variable {Z : Type u} {R : Lottery Z → Lottery Z → Prop} {P Q P' Q' : Set (Lottery Z)}

/-- `≿` satisfies the *independence property on `(P, Q)`*: for every `p ∈ P`, `q ∈ Q`, every
lottery `r` and every `α` with `0 < α ≤ 1`, `p ≿ q` if and only if
`α · p ⊕ (1 − α) · r ≿ α · q ⊕ (1 − α) · r`. -/
def IsIndependentOn (P Q : Set (Lottery Z)) (R : Lottery Z → Lottery Z → Prop) : Prop :=
  ∀ p ∈ P, ∀ q ∈ Q, ∀ (r : Lottery Z) (α : unitInterval), 0 < (α : ℝ) →
    (R p q ↔ R (mix α p r) (mix α q r))

/-- `≿` satisfies the *independence property*: for all lotteries `p`, `q`, `r` and every `α` with
`0 < α ≤ 1`, `p ≿ q` if and only if `α · p ⊕ (1 − α) · r ≿ α · q ⊕ (1 − α) · r`. -/
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

/-- With both orientations, independence transfers the strict preference. -/
theorem IsIndependentOn.strictPart_iff (hPQ : IsIndependentOn P Q R) (hQP : IsIndependentOn Q P R)
    {p q : Lottery Z} (hp : p ∈ P) (hq : q ∈ Q) (r : Lottery Z) {α : unitInterval}
    (hα : 0 < (α : ℝ)) :
    StrictPart R p q ↔ StrictPart R (mix α p r) (mix α q r) := by
  rw [Preference.strictPart_iff, Preference.strictPart_iff, hPQ.rel_iff hp hq r hα,
    hQP.rel_iff hq hp r hα]

/-- With both orientations, independence transfers indifference. -/
theorem IsIndependentOn.indiff_iff (hPQ : IsIndependentOn P Q R) (hQP : IsIndependentOn Q P R)
    {p q : Lottery Z} (hp : p ∈ P) (hq : q ∈ Q) (r : Lottery Z) {α : unitInterval}
    (hα : 0 < (α : ℝ)) :
    Indiff R p q ↔ Indiff R (mix α p r) (mix α q r) := by
  rw [Preference.indiff_iff, Preference.indiff_iff, hPQ.rel_iff hp hq r hα,
    hQP.rel_iff hq hp r hα]

/-! ### Monotonicity -/

/-- **Lemma 3.1.** If `≿` satisfies independence between degenerate lotteries and `[a] ≻ [b]`, then
`α · a ⊕ (1 − α) · b ≻ β · a ⊕ (1 − β) · b` if and only if `α > β`. Osborne and Rubinstein
assume a preference relation with the independence property of Definition 3.4, which implies this
hypothesis (`degenerate_subset_binary`); completeness and transitivity are not used. -/
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

/-- **Monotonicity.** If `≿` is complete, satisfies independence between degenerate lotteries and
`[a] ≻ [b]`, then `α · a ⊕ (1 − α) · b ≿ β · a ⊕ (1 − β) · b` if and only if `α ≥ β`. -/
theorem IsIndependentOn.rel_mix_iff (hI : IsIndependentOn degenerate degenerate R)
    (hC : IsComplete R) {a b : Z} (hab : StrictPart R (.single a) (.single b))
    (α β : unitInterval) :
    R (mix α (.single a) (.single b)) (mix β (.single a) (.single b)) ↔ (β : ℝ) ≤ α := by
  rw [hC.rel_iff_not_strictPart, ← hI.strictPart_mix_iff hab, not_lt]

/-! ### Replacing prizes by indifferent lotteries -/

/-- **Replacement.** Let `≿` be a preference relation that satisfies independence between
degenerate and binary lotteries in both orientations. Let `m z` be a binary lottery indifferent to
`[z]` for each prize `z`, with `m t = [t]` for the prizes `t` of a finite set `T` that contains
the supports of all `m z`. Then every lottery `p` is indifferent to the compound lottery
`∑_z p(z) · m z`. -/
theorem IsIndependentOn.indiff_iConvexComb (hR : IsPreferenceRelation R)
    (hDB : IsIndependentOn degenerate binary R) (hBD : IsIndependentOn binary degenerate R)
    (m : Z → Lottery Z) (T : Finset Z) (hm : ∀ z, Indiff R (.single z) (m z))
    (hmB : ∀ z, m z ∈ binary) (hmT : ∀ z y, (m z).weights y ≠ 0 → y ∈ T)
    (hT : ∀ t ∈ T, m t = .single t) (p : Lottery Z) :
    Indiff R p (p.iConvexComb m) := by
  classical
  have htrans : IsTransitive (Indiff R) := hR.isTransitive.indiff
  -- `m` fixes every lottery supported in `T`
  have hfix : ∀ q : Lottery Z, (∀ y, q.weights y ≠ 0 → y ∈ T) → q.iConvexComb m = q := by
    intro q hq
    rw [iConvexComb_congr (g := StdSimplex.single) fun y hy => hT y (hq y hy),
      StdSimplex.iConvexComb_single]
  -- strong induction on the number of prizes of `p` outside `T`
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
      -- `q` has fewer prizes outside `T`
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

/-- `≿` satisfies the *independence property on `(P, Q)`*: for every `p ∈ P`, `q ∈ Q`, every
lottery `r` and every `α` with `0 < α ≤ 1`, `p ≿ q` if and only if
`α · p ⊕ (1 − α) · r ≿ α · q ⊕ (1 − α) · r`. -/
def IsIndependentOn (P Q : Set (FinDist Z)) (R : FinDist Z → FinDist Z → Prop) : Prop :=
  ∀ p ∈ P, ∀ q ∈ Q, ∀ (r : FinDist Z) (α : unitInterval), 0 < (α : ℝ) →
    (R p q ↔ R (FinDist.mixture α p r) (FinDist.mixture α q r))

/-- `≿` satisfies the *independence property*: for all lotteries `p`, `q`, `r` and every `α` with
`0 < α ≤ 1`, `p ≿ q` if and only if `α · p ⊕ (1 − α) · r ≿ α · q ⊕ (1 − α) · r`. -/
def IsIndependent (R : FinDist Z → FinDist Z → Prop) : Prop :=
  IsIndependentOn Set.univ Set.univ R

/-- Independence on `(P, Q)` is independence of the same relation on lotteries, on the images of
`P` and `Q`. -/
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

/-- Ranking lotteries by the probability of the prize `0` satisfies independence: mixing both
sides with `r` adds `(1 − α) r(0)` to both probabilities and scales the rest by `α > 0`. -/
example : IsIndependent fun p q : Lottery (Fin 2) => q.weights 0 ≤ p.weights 0 := by
  rw [isIndependent_iff]
  intro p q r α hα
  simp only [weights_mix]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- Monotonicity applied: with `[0] ≻ [1]`, the lottery `0.7 · 0 ⊕ 0.3 · 1` is strictly preferred to
`0.2 · 0 ⊕ 0.8 · 1`. -/
example (R : Lottery (Fin 2) → Lottery (Fin 2) → Prop)
    (hI : IsIndependentOn degenerate degenerate R)
    (h01 : StrictPart R (.single 0) (.single 1)) :
    StrictPart R (mix ⟨0.7, by norm_num, by norm_num⟩ (.single 0) (.single 1))
      (mix ⟨0.2, by norm_num, by norm_num⟩ (.single 0) (.single 1)) :=
  (hI.strictPart_mix_iff h01 _ _).1 (by norm_num)

/-- Why `α = 0` is excluded: `0 · p ⊕ 1 · r = 0 · q ⊕ 1 · r` for all `p` and `q`. -/
example (p q r : Lottery (Fin 2)) : mix 0 p r = mix 0 q r := by simp

end Examples
