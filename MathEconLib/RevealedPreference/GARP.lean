/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLib.RevealedPreference.Basic

/-!
# Finite GARP and positive-multiplier Afriat inequalities

`GraphGARP` uses the reflexive transitive closure of direct revealed preference.
Its equivalence with positive-multiplier `AfriatInequalities` requires only finitely
many observations; prices and bundles need no sign restrictions in this algebraic
statement. The dataset corollary retains the restrictions of `Dataset`.

The proof constructs geometric utility levels using cardinalities of reachability
sets. This is a classical noncomputable witness construction, not an executable
numerical solver.

## References and provenance

Sidney N. Afriat (1967), *The Construction of Utility Functions from Expenditure Data*,
International Economic Review **8**(1), 67–77.
[DOI: 10.2307/2525382](https://doi.org/10.2307/2525382).

Hal R. Varian (1982), *The Nonparametric Approach to Demand Analysis*,
Econometrica **50**(4), 945–973.
[DOI: 10.2307/1912771](https://doi.org/10.2307/1912771).

Ported from Victor H. Aguiar's Apache-2.0 Lean development
[WGARP Lean](https://github.com/vaguiarl/wgarp-lean), module `GARP`.
The finite classical Afriat result is covered; the pairwise WGARP and infinite-data
extensions are outside this module's scope.
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace MathEconLib.RevealedPreference

variable {L : ℕ} {T : Type*}

/-- Direct revealed preference for arbitrary observed prices and choices. -/
def DirectRP (p q : T → Bundle L) (s t : T) : Prop :=
  dot (p s) (q t) ≤ dot (p s) (q s)

/-- Revealed preference is the reflexive-transitive closure of direct revealed
preference. -/
def RevealedPref (p q : T → Bundle L) : T → T → Prop :=
  Relation.ReflTransGen (DirectRP p q)

/-- Observation `t` is strictly cheaper than the chosen bundle at observation
`s`. -/
def StrictlyCheaperAt (p q : T → Bundle L) (s t : T) : Prop :=
  dot (p s) (q t) < dot (p s) (q s)

/-- Graph form of GARP, independent of the extra regularity fields carried by
`Dataset`. -/
def GraphGARP (p q : T → Bundle L) : Prop :=
  ∀ s t, RevealedPref p q s t → ¬ StrictlyCheaperAt p q t s

/-- GARP for an observed consumer dataset. -/
def SatisfiesGARP (D : Dataset L T) : Prop :=
  GraphGARP D.price D.choice

/-- Short dataset-level name used in theorem statements. -/
abbrev GARP (D : Dataset L T) : Prop := SatisfiesGARP D

theorem directRP_dataset_iff (D : Dataset L T) (s t : T) :
    DirectRP D.price D.choice s t ↔ 0 ≤ expenditureGap D s t := by
  rw [expenditureGap_eq]
  exact sub_nonneg.symm

theorem strictlyCheaperAt_dataset_iff (D : Dataset L T) (s t : T) :
    StrictlyCheaperAt D.price D.choice s t ↔ 0 < expenditureGap D s t := by
  rw [expenditureGap_eq]
  exact sub_pos.symm

/-- Direct revealed preference specialized to a dataset. -/
def DirectRevealed (D : Dataset L T) (s t : T) : Prop :=
  0 ≤ expenditureGap D s t

/-- Strict direct revealed preference specialized to a dataset. -/
def StrictDirectRevealed (D : Dataset L T) (s t : T) : Prop :=
  0 < expenditureGap D s t

/-- Dataset reachability, stated directly in terms of expenditure gaps. -/
def DatasetRevealedPref (D : Dataset L T) : T → T → Prop :=
  RevealedPref D.price D.choice

theorem directRevealed_iff_directRP (D : Dataset L T) (s t : T) :
    DirectRevealed D s t ↔ DirectRP D.price D.choice s t := by
  exact (directRP_dataset_iff D s t).symm

theorem datasetRevealedPref_iff (D : Dataset L T) (s t : T) :
    DatasetRevealedPref D s t ↔ RevealedPref D.price D.choice s t := by
  rfl

theorem garp_dataset_iff (D : Dataset L T) :
    GARP D ↔ ∀ s t, DatasetRevealedPref D s t → ¬ StrictDirectRevealed D t s := by
  simp only [SatisfiesGARP, GraphGARP, StrictDirectRevealed,
    strictlyCheaperAt_dataset_iff, ← datasetRevealedPref_iff]

theorem directRP_revealedPref (p q : T → Bundle L) {s t : T}
    (h : DirectRP p q s t) : RevealedPref p q s t :=
  Relation.ReflTransGen.single h

theorem revealedPref_refl (p q : T → Bundle L) (s : T) :
    RevealedPref p q s s :=
  Relation.ReflTransGen.refl

theorem revealedPref_trans (p q : T → Bundle L) {s t v : T}
    (hst : RevealedPref p q s t) (htv : RevealedPref p q t v) :
    RevealedPref p q s v :=
  hst.trans htv

/-- The finite set reachable from an observation. -/
noncomputable def reachFinset [Fintype T] (p q : T → Bundle L) (s : T) : Finset T := by
  classical
  exact Finset.univ.filter fun t => RevealedPref p q s t

/-- Reachability rank used by the geometric Afriat construction. -/
noncomputable def reachRank [Fintype T] (p q : T → Bundle L) (s : T) : ℕ :=
  (reachFinset p q s).card

theorem mem_reachFinset_iff [Fintype T] (p q : T → Bundle L) {s t : T} :
    t ∈ reachFinset p q s ↔ RevealedPref p q s t := by
  classical
  simp [reachFinset]

theorem reachRank_pos [Fintype T] (p q : T → Bundle L) (s : T) :
    1 ≤ reachRank p q s := by
  classical
  apply Finset.one_le_card.mpr
  exact ⟨s, (mem_reachFinset_iff p q).2 (revealedPref_refl p q s)⟩

theorem reachRank_mono [Fintype T] (p q : T → Bundle L) {s t : T}
    (hst : RevealedPref p q s t) :
    reachRank p q t ≤ reachRank p q s := by
  classical
  apply Finset.card_le_card
  intro v hv
  rw [mem_reachFinset_iff] at hv ⊢
  exact hst.trans hv

theorem directRP_reachRank_mono [Fintype T] (p q : T → Bundle L) {s t : T}
    (hst : DirectRP p q s t) :
    reachRank p q t ≤ reachRank p q s :=
  reachRank_mono p q (directRP_revealedPref p q hst)

theorem reverse_of_direct_and_equal_reachRank [Fintype T]
    (p q : T → Bundle L) {s t : T}
    (hst : DirectRP p q s t) (hrank : reachRank p q s = reachRank p q t) :
    RevealedPref p q t s := by
  classical
  have hforward : RevealedPref p q s t := directRP_revealedPref p q hst
  have hsubset : reachFinset p q t ⊆ reachFinset p q s := by
    intro v hv
    rw [mem_reachFinset_iff] at hv ⊢
    exact hforward.trans hv
  by_contra hnot
  have hproper : reachFinset p q t ⊂ reachFinset p q s := by
    refine ⟨hsubset, ?_⟩
    intro heq
    have hs : s ∈ reachFinset p q s :=
      (mem_reachFinset_iff p q).2 (revealedPref_refl p q s)
    have hs' : s ∈ reachFinset p q t := heq hs
    exact hnot ((mem_reachFinset_iff p q).1 hs')
  have hlt : reachRank p q t < reachRank p q s := by
    simpa [reachRank] using Finset.card_lt_card hproper
  exact (not_lt_of_ge (by simp [hrank])) hlt

theorem equal_reachRank_expenditure_ge [Fintype T]
    (p q : T → Bundle L) (hG : GraphGARP p q) {s t : T}
    (hrank : reachRank p q s = reachRank p q t) :
    dot (p s) (q s) ≤ dot (p s) (q t) := by
  apply le_of_not_gt
  intro hcheap
  have hdirect : DirectRP p q s t := le_of_lt hcheap
  have hreverse : RevealedPref p q t s :=
    reverse_of_direct_and_equal_reachRank p q hdirect hrank
  exact hG t s hreverse hcheap

theorem higher_reachRank_expenditure_lt [Fintype T]
    (p q : T → Bundle L) {s t : T}
    (hrank : reachRank p q s < reachRank p q t) :
    dot (p s) (q s) < dot (p s) (q t) := by
  apply lt_of_not_ge
  intro hdirect
  exact (not_le_of_gt hrank) (directRP_reachRank_mono p q hdirect)

theorem exists_strictly_higher_reachRank [Fintype T]
    (p q : T → Bundle L)
    (hneq : ¬ ∀ s t, reachRank p q s = reachRank p q t) :
    ∃ s t, reachRank p q s < reachRank p q t := by
  classical
  by_contra hnone
  apply hneq
  intro s t
  by_cases hst : reachRank p q s = reachRank p q t
  · exact hst
  · rcases lt_or_gt_of_ne hst with hlt | hgt
    · exact False.elim (hnone ⟨s, t, hlt⟩)
    · exact False.elim (hnone ⟨t, s, hgt⟩)

/-- Rank-increasing ordered pairs. -/
noncomputable def higherPairs [Fintype T] (p q : T → Bundle L) : Finset (T × T) :=
  (Finset.univ.product Finset.univ).filter
    fun st => reachRank p q st.1 < reachRank p q st.2

/-- Positive expenditure differences on rank-increasing pairs. -/
noncomputable def higherGapVals [Fintype T] (p q : T → Bundle L) : Finset ℝ :=
  (higherPairs p q).image
    fun st => dot (p st.1) (q st.2) - dot (p st.1) (q st.1)

/-- Magnitudes of negative differences on rank-decreasing pairs. -/
noncomputable def lowerNegGapVals [Fintype T] (p q : T → Bundle L) : Finset ℝ :=
  ((Finset.univ.product Finset.univ).filter fun st =>
      reachRank p q st.2 < reachRank p q st.1 ∧
        dot (p st.1) (q st.2) < dot (p st.1) (q st.1)).image
    fun st => dot (p st.1) (q st.1) - dot (p st.1) (q st.2)

theorem higherGapVals_nonempty [Fintype T]
    (p q : T → Bundle L)
    (hneq : ¬ ∀ s t, reachRank p q s = reachRank p q t) :
    (higherGapVals p q).Nonempty := by
  classical
  obtain ⟨s, t, hst⟩ := exists_strictly_higher_reachRank p q hneq
  refine ⟨dot (p s) (q t) - dot (p s) (q s), ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨(s, t), by simp [higherPairs, hst], rfl⟩

theorem mem_higherGapVals_of_lt [Fintype T]
    (p q : T → Bundle L) {s t : T}
    (hst : reachRank p q s < reachRank p q t) :
    dot (p s) (q t) - dot (p s) (q s) ∈ higherGapVals p q := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨(s, t), by simp [higherPairs, hst], rfl⟩

theorem mem_lowerNegGapVals_of_lt_and_neg [Fintype T]
    (p q : T → Bundle L) {s t : T}
    (hst : reachRank p q t < reachRank p q s)
    (hneg : dot (p s) (q t) < dot (p s) (q s)) :
    dot (p s) (q s) - dot (p s) (q t) ∈ lowerNegGapVals p q := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨(s, t), by simp [hst, hneg], rfl⟩

/-- Smallest positive gap on a rank-increasing pair. -/
noncomputable def higherGap [Fintype T] (p q : T → Bundle L)
    (hneq : ¬ ∀ s t, reachRank p q s = reachRank p q t) : ℝ :=
  (higherGapVals p q).min' (higherGapVals_nonempty p q hneq)

/-- Largest relevant negative-gap magnitude, with zero adjoined. -/
noncomputable def maxLowerNegGap [Fintype T] (p q : T → Bundle L) : ℝ :=
  (insert 0 (lowerNegGapVals p q)).max' (by simp)

theorem higherGap_le_gap_of_lt [Fintype T]
    (p q : T → Bundle L)
    (hneq : ¬ ∀ s t, reachRank p q s = reachRank p q t) {s t : T}
    (hst : reachRank p q s < reachRank p q t) :
    higherGap p q hneq ≤ dot (p s) (q t) - dot (p s) (q s) := by
  classical
  exact Finset.min'_le _ _ (mem_higherGapVals_of_lt p q hst)

theorem higherGap_pos [Fintype T]
    (p q : T → Bundle L)
    (hneq : ¬ ∀ s t, reachRank p q s = reachRank p q t) :
    0 < higherGap p q hneq := by
  classical
  have hmem : higherGap p q hneq ∈ higherGapVals p q := Finset.min'_mem _ _
  rcases Finset.mem_image.mp hmem with ⟨st, hstmem, heq⟩
  rcases st with ⟨s, t⟩
  have hst : reachRank p q s < reachRank p q t := by
    simpa [higherPairs] using hstmem
  rw [← heq]
  exact sub_pos.mpr (higher_reachRank_expenditure_lt p q hst)

theorem nonneg_maxLowerNegGap [Fintype T] (p q : T → Bundle L) :
    0 ≤ maxLowerNegGap p q := by
  classical
  exact Finset.le_max' _ 0 (by simp)

theorem gap_le_maxLowerNegGap [Fintype T]
    (p q : T → Bundle L) {s t : T}
    (hst : reachRank p q t < reachRank p q s)
    (hneg : dot (p s) (q t) < dot (p s) (q s)) :
    dot (p s) (q s) - dot (p s) (q t) ≤ maxLowerNegGap p q := by
  classical
  apply Finset.le_max'
  simp [mem_lowerNegGapVals_of_lt_and_neg p q hst hneg]

theorem equal_reachRank_gap_nonneg [Fintype T]
    (p q : T → Bundle L) (hG : GraphGARP p q) {s t : T}
    (hrank : reachRank p q s = reachRank p q t) :
    0 ≤ dot (p s) (q t) - dot (p s) (q s) :=
  sub_nonneg.mpr (equal_reachRank_expenditure_ge p q hG hrank)

theorem neg_maxLowerNegGap_le_gap_of_lower [Fintype T]
    (p q : T → Bundle L) {s t : T}
    (hst : reachRank p q t < reachRank p q s) :
    -maxLowerNegGap p q ≤ dot (p s) (q t) - dot (p s) (q s) := by
  classical
  by_cases hneg : dot (p s) (q t) < dot (p s) (q s)
  · have hgap := gap_le_maxLowerNegGap p q hst hneg
    linarith
  · have hnonneg : dot (p s) (q s) ≤ dot (p s) (q t) := le_of_not_gt hneg
    have hmax := nonneg_maxLowerNegGap p q
    linarith

/-- Afriat support plane based at observation `t`. -/
def globalAfriatSupport (U lam : T → ℝ) (p q : T → Bundle L)
    (t : T) (x : Bundle L) : ℝ :=
  U t + lam t * (dot (p t) x - dot (p t) (q t))

/-- The finite system of global Afriat inequalities. -/
def AfriatInequalities (U lam : T → ℝ) (p q : T → Bundle L) : Prop :=
  ∀ s t, U s ≤ globalAfriatSupport U lam p q t (q s)

/-- Strict positivity of the global Afriat multipliers. -/
def PositiveMultipliers (lam : T → ℝ) : Prop :=
  ∀ t, 0 < lam t

/-- Geometric ratio in the explicit construction. -/
noncomputable def geometricRho [Fintype T] (p q : T → Bundle L)
    (hneq : ¬ ∀ s t, reachRank p q s = reachRank p q t) : ℝ :=
  higherGap p q hneq /
    (maxLowerNegGap p q + 2 * higherGap p q hneq)

/-- Explicit observed utility levels. -/
noncomputable def geometricU [Fintype T] (p q : T → Bundle L)
    (hneq : ¬ ∀ s t, reachRank p q s = reachRank p q t) : T → ℝ :=
  fun s => 1 - geometricRho p q hneq ^ reachRank p q s

/-- Explicit positive Afriat multipliers. -/
noncomputable def geometricLam [Fintype T] (p q : T → Bundle L)
    (hneq : ¬ ∀ s t, reachRank p q s = reachRank p q t) : T → ℝ :=
  fun s => geometricRho p q hneq ^ reachRank p q s / higherGap p q hneq

theorem geometricRho_pos [Fintype T]
    (p q : T → Bundle L)
    (hneq : ¬ ∀ s t, reachRank p q s = reachRank p q t) :
    0 < geometricRho p q hneq := by
  have hgap := higherGap_pos p q hneq
  have hmax := nonneg_maxLowerNegGap p q
  exact div_pos hgap (by linarith)

theorem geometricRho_lt_one [Fintype T]
    (p q : T → Bundle L)
    (hneq : ¬ ∀ s t, reachRank p q s = reachRank p q t) :
    geometricRho p q hneq < 1 := by
  have hgap := higherGap_pos p q hneq
  have hmax := nonneg_maxLowerNegGap p q
  rw [geometricRho]
  exact (div_lt_one (by linarith)).2 (by linarith)

theorem geometricRho_pow_antitone [Fintype T]
    (p q : T → Bundle L)
    (hneq : ¬ ∀ s t, reachRank p q s = reachRank p q t) {a b : ℕ}
    (hab : a ≤ b) :
    geometricRho p q hneq ^ b ≤ geometricRho p q hneq ^ a := by
  exact pow_le_pow_of_le_one (geometricRho_pos p q hneq).le
    (geometricRho_lt_one p q hneq).le hab

theorem maxLowerNegGap_mul_geometricRho_le_higherGap_mul_one_sub
    [Fintype T] (p q : T → Bundle L)
    (hneq : ¬ ∀ s t, reachRank p q s = reachRank p q t) :
    maxLowerNegGap p q * geometricRho p q hneq ≤
      higherGap p q hneq * (1 - geometricRho p q hneq) := by
  have hgap := higherGap_pos p q hneq
  have hmax := nonneg_maxLowerNegGap p q
  have hden : 0 < maxLowerNegGap p q + 2 * higherGap p q hneq := by linarith
  rw [geometricRho]
  field_simp [ne_of_gt hden]
  nlinarith

theorem geometricLam_pos [Fintype T]
    (p q : T → Bundle L)
    (hneq : ¬ ∀ s t, reachRank p q s = reachRank p q t) :
    PositiveMultipliers (geometricLam p q hneq) := by
  intro s
  exact div_pos (pow_pos (geometricRho_pos p q hneq) _)
    (higherGap_pos p q hneq)

theorem geometric_afriatInequalities [Fintype T]
    (p q : T → Bundle L) (hG : GraphGARP p q)
    (hneq : ¬ ∀ s t, reachRank p q s = reachRank p q t) :
    AfriatInequalities (geometricU p q hneq) (geometricLam p q hneq) p q := by
  intro s t
  let rho : ℝ := geometricRho p q hneq
  let B : ℝ := higherGap p q hneq
  let A : ℝ := maxLowerNegGap p q
  have hrho : 0 < rho := geometricRho_pos p q hneq
  have hB : 0 < B := higherGap_pos p q hneq
  have hA : 0 ≤ A := nonneg_maxLowerNegGap p q
  simp only [globalAfriatSupport, geometricU, geometricLam]
  change 1 - rho ^ reachRank p q s ≤
    1 - rho ^ reachRank p q t +
      rho ^ reachRank p q t / B * (dot (p t) (q s) - dot (p t) (q t))
  rcases lt_trichotomy (reachRank p q t) (reachRank p q s) with hts | hts | hts
  · have hgap : B ≤ dot (p t) (q s) - dot (p t) (q t) := by
      simpa [B] using higherGap_le_gap_of_lt p q hneq hts
    have hmain :
        rho ^ reachRank p q t ≤
          (rho ^ reachRank p q t / B) *
            (dot (p t) (q s) - dot (p t) (q t)) := by
      calc
        rho ^ reachRank p q t = (rho ^ reachRank p q t / B) * B := by
          field_simp [ne_of_gt hB]
        _ ≤ _ := mul_le_mul_of_nonneg_left hgap
          (div_nonneg (pow_pos hrho _).le hB.le)
    nlinarith [pow_pos hrho (reachRank p q s)]
  · have hgap : 0 ≤ dot (p t) (q s) - dot (p t) (q t) := by
      simpa using equal_reachRank_gap_nonneg p q hG hts
    have hmain : 0 ≤ (rho ^ reachRank p q t / B) *
        (dot (p t) (q s) - dot (p t) (q t)) :=
      mul_nonneg (div_nonneg (pow_pos hrho _).le hB.le) hgap
    have hpowequal : rho ^ reachRank p q s = rho ^ reachRank p q t := by
      simp [hts]
    nlinarith
  · have hgap : -A ≤ dot (p t) (q s) - dot (p t) (q t) := by
      simpa [A] using neg_maxLowerNegGap_le_gap_of_lower p q hts
    have htpos : 0 < reachRank p q t :=
      lt_of_lt_of_le Nat.zero_lt_one (reachRank_pos p q t)
    have hpowMono : rho ^ (reachRank p q t - 1) ≤ rho ^ reachRank p q s := by
      simpa [rho] using geometricRho_pow_antitone p q hneq
        (Nat.le_pred_of_lt hts)
    have hpowSucc : rho ^ reachRank p q t =
        rho ^ (reachRank p q t - 1) * rho := by
      conv_lhs => rw [show reachRank p q t = reachRank p q t - 1 + 1 by omega]
      rw [pow_succ]
    have hdrop : rho ^ reachRank p q t - rho ^ reachRank p q s ≤
        -(rho ^ (reachRank p q t - 1) * (1 - rho)) := by
      nlinarith
    have hratio : A * rho / B ≤ 1 - rho := by
      have hbalance : A * rho ≤ B * (1 - rho) := by
        simpa [A, B, rho] using
          maxLowerNegGap_mul_geometricRho_le_higherGap_mul_one_sub p q hneq
      exact (div_le_iff₀ hB).2 (by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hbalance)
    have hlamA : (rho ^ reachRank p q t / B) * A ≤
        rho ^ (reachRank p q t - 1) * (1 - rho) := by
      rw [hpowSucc]
      calc
        (rho ^ (reachRank p q t - 1) * rho / B) * A =
            rho ^ (reachRank p q t - 1) * (A * rho / B) := by
          field_simp [ne_of_gt hB]
        _ ≤ _ := mul_le_mul_of_nonneg_left hratio (pow_pos hrho _).le
    have hmain : -((rho ^ reachRank p q t / B) * A) ≤
        (rho ^ reachRank p q t / B) *
          (dot (p t) (q s) - dot (p t) (q t)) := by
      have hcoeff : 0 ≤ rho ^ reachRank p q t / B :=
        div_nonneg (pow_pos hrho _).le hB.le
      have := mul_le_mul_of_nonneg_left hgap hcoeff
      simpa [neg_mul, mul_comm, mul_left_comm, mul_assoc] using this
    nlinarith

/-- GARP constructively produces positive multipliers and global Afriat
numbers. -/
theorem graphGARP_implies_afriatInequalities [Finite T]
    (p q : T → Bundle L) (hG : GraphGARP p q) :
    ∃ U lam, PositiveMultipliers lam ∧ AfriatInequalities U lam p q := by
  let := Fintype.ofFinite T
  by_cases hneq : ¬ ∀ s t, reachRank p q s = reachRank p q t
  · exact ⟨geometricU p q hneq, geometricLam p q hneq,
      geometricLam_pos p q hneq, geometric_afriatInequalities p q hG hneq⟩
  · refine ⟨fun _ => 1, fun _ => 1, by intro; positivity, ?_⟩
    intro s t
    have hgap : 0 ≤ dot (p t) (q s) - dot (p t) (q t) :=
      equal_reachRank_gap_nonneg p q hG (not_not.mp hneq t s)
    simp only [globalAfriatSupport]
    linarith

theorem directRP_monotone_of_afriat
    (U lam : T → ℝ) (p q : T → Bundle L)
    (hA : AfriatInequalities U lam p q) (hpos : PositiveMultipliers lam)
    {s t : T} (hst : DirectRP p q s t) :
    U t ≤ U s := by
  have hineq := hA t s
  have hgap : dot (p s) (q t) - dot (p s) (q s) ≤ 0 := sub_nonpos.mpr hst
  have hscaled : lam s * (dot (p s) (q t) - dot (p s) (q s)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (hpos s).le hgap
  simp only [globalAfriatSupport] at hineq
  linarith

theorem revealedPref_monotone_of_afriat
    (U lam : T → ℝ) (p q : T → Bundle L)
    (hA : AfriatInequalities U lam p q) (hpos : PositiveMultipliers lam)
    {s t : T} (hst : RevealedPref p q s t) :
    U t ≤ U s := by
  refine Relation.ReflTransGen.head_induction_on hst ?_ ?_
  · exact le_rfl
  · intro a b hab _hbc ih
    exact ih.trans (directRP_monotone_of_afriat U lam p q hA hpos hab)

theorem afriatInequalities_imply_graphGARP
    (U lam : T → ℝ) (p q : T → Bundle L)
    (hA : AfriatInequalities U lam p q) (hpos : PositiveMultipliers lam) :
    GraphGARP p q := by
  intro s t hst hcheap
  have hmon : U t ≤ U s :=
    revealedPref_monotone_of_afriat U lam p q hA hpos hst
  have hineq := hA s t
  have hscaled : lam t * (dot (p t) (q s) - dot (p t) (q t)) < 0 :=
    mul_neg_of_pos_of_neg (hpos t) (sub_neg.mpr hcheap)
  simp only [globalAfriatSupport] at hineq
  linarith

/-- Finite GARP is equivalent to feasibility of the global Afriat
inequalities with strictly positive multipliers. -/
theorem graphGARP_iff_exists_afriatInequalities [Finite T]
    (p q : T → Bundle L) :
    GraphGARP p q ↔
      ∃ U lam, PositiveMultipliers lam ∧ AfriatInequalities U lam p q := by
  constructor
  · exact graphGARP_implies_afriatInequalities p q
  · rintro ⟨U, lam, hpos, hA⟩
    exact afriatInequalities_imply_graphGARP U lam p q hA hpos

/-- Dataset specialization of the finite Afriat-inequality theorem. -/
theorem garp_iff_exists_afriatInequalities [Finite T]
    (D : Dataset L T) :
    GARP D ↔
      ∃ U lam, PositiveMultipliers lam ∧
        AfriatInequalities U lam D.price D.choice :=
  graphGARP_iff_exists_afriatInequalities D.price D.choice

end MathEconLib.RevealedPreference
