/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLib.RevealedPreference.Afriat
public import MathEconLib.RevealedPreference.WGARP.Basic

/-!
# Apply finite Afriat to each observation pair

A two-observation restriction uses `Bool`, allowing repeated endpoints. Every
reflexive relation on two points is transitive, so its revealed-preference closure
adds no comparisons. WGARP is therefore exactly GARP on every such restriction.
The existing finite Afriat theorem supplies a continuous, concave, strictly increasing
utility rationalizing both endpoint budgets. No symmetry of selected pair utilities
is asserted or needed by the row/column coalition construction.

## References

Victor H. Aguiar, Per Hjertstrand, Roberto Serrano, and Özgür Evren (2026),
*A Rationalization of the Weak Axiom of Revealed Preference*,
[arXiv:1906.00296v2](https://arxiv.org/abs/1906.00296v2), revised August 12, 2026,
Theorem 1, pairwise Afriat step; see [WGARP Lean](https://github.com/vaguiarl/wgarp-lean).
For the reused finite Afriat theorem and bibliography, see `RevealedPreference.Afriat`.
-/

@[expose] public section

set_option autoImplicit false

namespace MathEconLib.RevealedPreference

variable {L : ℕ} {T : Type*}

/-- The observations `s` and `t`, with `false` selecting `s` and `true` selecting `t`. -/
def pairDataset (D : Dataset L T) (s t : T) : Dataset L Bool where
  price b := if b then D.price t else D.price s
  choice b := if b then D.choice t else D.choice s
  price_pos b i := by cases b <;> simpa using D.price_pos _ i
  choice_nonneg b i := by cases b <;> simpa using D.choice_nonneg _ i

@[simp] theorem pairDataset_affordable_false (D : Dataset L T) (s t : T) (y : Bundle L) :
    Affordable (pairDataset D s t) false y ↔ Affordable D s y := Iff.rfl

@[simp] theorem pairDataset_affordable_true (D : Dataset L T) (s t : T) (y : Bundle L) :
    Affordable (pairDataset D s t) true y ↔ Affordable D t y := Iff.rfl

/-- On two observations the direct relation is already reflexive and transitive. -/
theorem revealedPreferred_bool_iff_directlyRevealedPreferred
    (p q : Bool → Bundle L) (s t : Bool) :
    RevealedPreferred p q s t ↔ DirectlyRevealedPreferred p q s t := by
  constructor
  · intro h
    refine Relation.ReflTransGen.head_induction_on h ?_ ?_
    · exact le_rfl
    · intro a b hab _hbt ih
      cases a <;> cases b <;> cases t <;> first | exact hab | exact ih | exact le_rfl
  · exact directlyRevealedPreferred_revealedPreferred p q

/-- Any GARP dataset satisfies the pairwise restriction WGARP. -/
theorem wgarp_of_garp (D : Dataset L T) (h : GARP D) : WGARP D := by
  intro s t hts
  apply le_of_not_gt
  intro hst
  exact h t s
    (directlyRevealedPreferred_revealedPreferred _ _
      ((directlyRevealedPreferred_iff_expenditureGap_nonneg D t s).mpr hts))
    ((strictlyCheaperAt_iff_expenditureGap_pos D s t).mpr hst)

/-- GARP and WGARP coincide on the two-point observation carrier, including duplicates. -/
theorem garp_bool_iff_wgarp (D : Dataset L Bool) : GARP D ↔ WGARP D := by
  constructor
  · exact wgarp_of_garp D
  · intro h s t hst hcheap
    have hd := (revealedPreferred_bool_iff_directlyRevealedPreferred D.price D.choice s t).mp hst
    have hw := (directlyRevealedPreferred_iff_expenditureGap_nonneg D s t).mp hd
    have hs := (strictlyCheaperAt_iff_expenditureGap_pos D t s).mp hcheap
    exact (not_lt_of_ge (h t s hw)) hs

/-- WGARP is exactly GARP on every two-observation restriction; no global finiteness is used. -/
theorem wgarp_iff_pairwise_garp (D : Dataset L T) :
    WGARP D ↔ ∀ s t, GARP (pairDataset D s t) := by
  constructor
  · intro h s t
    apply (garp_bool_iff_wgarp _).mpr
    intro a b
    cases a <;> cases b <;> exact h _ _
  · intro h s t hts
    exact ((garp_bool_iff_wgarp _).mp (h s t)) false true hts

/-- Pairwise application of the existing finite Afriat theorem. -/
theorem exists_regular_pairUtility (D : Dataset L T) (h : WGARP D) (s t : T) :
    ∃ u : Utility L,
      Continuous u ∧ ConcaveOn ℝ Set.univ u ∧ StrictlyIncreasing u ∧
        (∀ y, Affordable D s y → u y ≤ u (D.choice s)) ∧
        (∀ y, Affordable D t y → u y ≤ u (D.choice t)) := by
  obtain ⟨u, hc, hconc, hi, hr⟩ :=
    hasRegularUtilityRationalization_of_garp (pairDataset D s t)
      ((wgarp_iff_pairwise_garp D).mp h s t)
  exact ⟨u, hc, hconc, hi, hr false, hr true⟩

end MathEconLib.RevealedPreference
