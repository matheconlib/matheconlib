/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLib.RevealedPreference.RenyData
public import MathEconLib.RevealedPreference.AfriatGeometry

/-!
# Finite Afriat rationalization with free goods

The graph-theoretic Afriat theorem applies to arbitrary raw observations. This
file derives the finite economic conclusion under Reny's weaker admissibility
conditions: prices are nonnegative and nonzero, while choices may be zero.
Empty finite observation sets are included when there is at least one good.
This is the finite input to an infinite-data proof, not that proof itself.

Mathematical references: Afriat's finite theorem and Philip J. Reny,
"A Characterization of Rationalizable Consumer Behavior", Econometrica 83
(2015), 175–192, doi:10.3982/ECTA12345.

## References and Lean provenance

Ported from Victor H. Aguiar's Apache-2.0 Lean development
[WGARP Lean](https://github.com/vaguiarl/wgarp-lean), module `RenyFinite`.
-/

@[expose] public section

set_option autoImplicit false

namespace MathEconLib.RevealedPreference

variable {L : ℕ} {T : Type*}

/-- A nonnegative price vector defines a coordinatewise nondecreasing linear
functional; the bundles themselves need not be nonnegative. -/
theorem dot_monotone_of_nonnegative {p : Bundle L} (hp : Nonnegative p) :
    Monotone (dot p) := by
  intro x y hxy
  unfold dot
  exact Finset.sum_le_sum fun i _hi => mul_le_mul_of_nonneg_left (hxy i) (hp i)

/-- A nonzero nonnegative price vector assigns positive weight to some good. -/
theorem exists_positive_coordinate_of_nonnegative_ne_zero
    {p : Bundle L} (hp : Nonnegative p) (hne : p ≠ 0) :
    ∃ i, 0 < p i := by
  by_contra hnone
  apply hne
  funext i
  have hle : p i ≤ 0 := by
    apply le_of_not_gt
    intro hi
    exact hnone ⟨i, hi⟩
  exact le_antisymm hle (hp i)

/-- With a nonzero nonnegative price, raising every good strictly raises
expenditure, even if some goods have zero price. -/
theorem dot_lt_of_all_coordinates_lt
    {p x y : Bundle L} (hp : Nonnegative p) (hne : p ≠ 0)
    (hxy : ∀ i, x i < y i) : dot p x < dot p y := by
  unfold dot
  apply Finset.sum_lt_sum
  · intro i _hi
    exact mul_le_mul_of_nonneg_left (hxy i).le (hp i)
  · obtain ⟨i, hi⟩ := exists_positive_coordinate_of_nonnegative_ne_zero hp hne
    exact ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left (hxy i) hi⟩

/-- Nonnegative prices and positive multipliers make every affine support
coordinatewise nondecreasing. -/
theorem globalAfriatSupport_monotone
    (p q : T → Bundle L) (U lam : T → ℝ)
    (hprice : ∀ t, Nonnegative (p t)) (hpos : PositiveMultipliers lam) (t : T) :
    Monotone (globalAfriatSupport U lam p q t) := by
  intro x y hxy
  have hdot := dot_monotone_of_nonnegative (hprice t) hxy
  unfold globalAfriatSupport
  have hscaled := mul_le_mul_of_nonneg_left
    (sub_le_sub_right hdot (dot (p t) (q t))) (hpos t).le
  linarith

/-- The finite Afriat envelope is coordinatewise nondecreasing even with
zero-price goods. -/
theorem globalAfriatUtility_monotone [Fintype T] [Nonempty T]
    (p q : T → Bundle L) (U lam : T → ℝ)
    (hprice : ∀ t, Nonnegative (p t)) (hpos : PositiveMultipliers lam) :
    Monotone (globalAfriatUtility U lam p q) := by
  intro x y hxy
  apply le_globalAfriatUtility_of_le_supports
  intro t
  exact (globalAfriatUtility_le_support U lam p q t x).trans
    (globalAfriatSupport_monotone p q U lam hprice hpos t hxy)

/-- Each nonzero nonnegative support price gives the semistrict commodity
comparison required by Reny's finite and infinite statements. -/
theorem globalAfriatSupport_lt_of_all_coordinates_lt
    (p q : T → Bundle L) (U lam : T → ℝ)
    (hprice : RenyPriceAdmissible p) (hpos : PositiveMultipliers lam)
    (t : T) {x y : Bundle L} (hxy : ∀ i, x i < y i) :
    globalAfriatSupport U lam p q t x < globalAfriatSupport U lam p q t y := by
  have hdot := dot_lt_of_all_coordinates_lt (hprice t).1 (hprice t).2 hxy
  unfold globalAfriatSupport
  have hscaled := mul_lt_mul_of_pos_left
    (sub_lt_sub_right hdot (dot (p t) (q t))) (hpos t)
  linarith

/-- The finite lower envelope preserves semistrict increase because each of
the finitely many supports is strictly increasing in this comparison. -/
theorem globalAfriatUtility_semiStrictlyIncreasingOnNonnegative
    [Fintype T] [Nonempty T]
    (p q : T → Bundle L) (U lam : T → ℝ)
    (hprice : RenyPriceAdmissible p) (hpos : PositiveMultipliers lam) :
    SemiStrictlyIncreasingOnNonnegative (globalAfriatUtility U lam p q) := by
  intro x y _hx _hy hxy
  unfold globalAfriatUtility
  rw [Finset.lt_inf'_iff]
  intro t _ht
  exact (Finset.inf'_le _ (Finset.mem_univ t)).trans_lt
    (globalAfriatSupport_lt_of_all_coordinates_lt p q U lam hprice hpos t hxy)

/-- A positive Afriat certificate yields both weak and strict affordability
comparisons for raw data, without assuming positive prices or nonzero choices. -/
theorem globalAfriatUtility_rawRenyRationalizes [Fintype T] [Nonempty T]
    (p q : T → Bundle L) (U lam : T → ℝ)
    (hA : AfriatInequalities U lam p q) (hpos : PositiveMultipliers lam) :
    rawRenyRationalizes p q (globalAfriatUtility U lam p q) := by
  intro t y _hy
  exact ⟨globalAfriatUtility_le_observed_of_dot_le U lam p q hA t (hpos t).le,
    globalAfriatUtility_lt_observed_of_dot_lt U lam p q hA t (hpos t)⟩

/-- The full regular finite-Afriat conclusion under Reny's raw-data
admissibility conventions. -/
def HasFiniteRegularRenyRationalization (p q : T → Bundle L) : Prop :=
  ∃ u : Utility L,
    Continuous u ∧
    ConcaveOn ℝ Set.univ u ∧
    MonotoneOn u {x | Nonnegative x} ∧
    SemiStrictlyIncreasingOnNonnegative u ∧
    rawRenyRationalizes p q u

/-- Finite GARP yields continuous, concave, nondecreasing, semistrictly
increasing utility. This includes empty observations and zero-price goods. -/
theorem finiteRenyRationalization_of_graphGARP [Finite T]
    (hL : 0 < L) (p q : T → Bundle L)
    (hprice : RenyPriceAdmissible p) (hgarp : GraphGARP p q) :
    HasFiniteRegularRenyRationalization p q := by
  classical
  let : Fintype T := Fintype.ofFinite T
  by_cases hT : Nonempty T
  · let : Nonempty T := hT
    obtain ⟨U, lam, hpos, hA⟩ := graphGARP_implies_afriatInequalities p q hgarp
    exact ⟨globalAfriatUtility U lam p q,
      globalAfriatUtility_continuous U lam p q,
      globalAfriatUtility_concaveOn U lam p q,
      (globalAfriatUtility_monotone p q U lam (fun t => (hprice t).1) hpos).monotoneOn _,
      globalAfriatUtility_semiStrictlyIncreasingOnNonnegative p q U lam hprice hpos,
      globalAfriatUtility_rawRenyRationalizes p q U lam hA hpos⟩
  · let u : Utility L := dot (fun _ => 1)
    have hprice_one : Nonnegative (fun _ : Fin L => (1 : ℝ)) := fun _ => zero_le_one
    have hone_ne : (fun _ : Fin L => (1 : ℝ)) ≠ 0 := by
      intro heq
      have hcoord := congrFun heq ⟨0, hL⟩
      norm_num at hcoord
    have hconcave : ConcaveOn ℝ Set.univ u := by
      refine ⟨convex_univ, ?_⟩
      intro x _hx y _hy a b _ha _hb _hab
      dsimp [u]
      rw [dot_add_smul]
    refine ⟨u, continuous_dot _, hconcave,
      (dot_monotone_of_nonnegative hprice_one).monotoneOn _, ?_, ?_⟩
    · intro x y _hx _hy hxy
      exact dot_lt_of_all_coordinates_lt hprice_one hone_ne hxy
    · intro t
      exact (hT ⟨t⟩).elim

/-- Full finite Afriat equivalence on raw data with Reny's admissibility,
including zero prices, zero choices, and empty observation sets. -/
theorem finite_graphGARP_iff_regularRenyRationalization [Finite T]
    (hL : 0 < L) (p q : T → Bundle L)
    (hprice : RenyPriceAdmissible p) (hchoice : RenyChoiceAdmissible q) :
    GraphGARP p q ↔ HasFiniteRegularRenyRationalization p q := by
  constructor
  · exact finiteRenyRationalization_of_graphGARP hL p q hprice
  · rintro ⟨u, _hcont, _hconcave, _hmono, _hsemi, hrat⟩
    exact graphGARP_of_rawRenyRationalizes p q u hchoice hrat

/-- Every finite restriction admits a regular finite-Afriat utility exactly
when the entire, possibly infinite, observed graph satisfies GARP. The utility
in this assertion is permitted to depend on the finite restriction. -/
theorem graphGARP_iff_all_finite_regularRenyRationalizations
    (hL : 0 < L) (p q : T → Bundle L)
    (hprice : RenyPriceAdmissible p) (hchoice : RenyChoiceAdmissible q) :
    GraphGARP p q ↔
      ∀ F : Finset T,
        HasFiniteRegularRenyRationalization (fun z : F => p z) (fun z : F => q z) := by
  rw [graphGARP_iff_all_finite_restrictions]
  constructor
  · intro hfinite F
    exact (finite_graphGARP_iff_regularRenyRationalization hL
      (fun z : F => p z) (fun z : F => q z) (fun z => hprice z) (fun z => hchoice z)).mp
      (hfinite F)
  · intro hfinite F
    exact (finite_graphGARP_iff_regularRenyRationalization hL
      (fun z : F => p z) (fun z : F => q z) (fun z => hprice z) (fun z => hchoice z)).mpr
      (hfinite F)

end MathEconLib.RevealedPreference
