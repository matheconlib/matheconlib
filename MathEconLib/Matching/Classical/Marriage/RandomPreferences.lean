/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors, Bo Cowgill
-/
import MathEconLib.Matching.Classical.Marriage.DeferredAcceptanceComputable
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Finite random preference profiles for marriage markets

Rank profiles encode strict complete rankings of the other population. Smaller ranks are
preferred. The adapter to `MarriageMarket` reverses this order and puts every partner above
remaining unmatched. The two population sizes are separate parameters.

The profile representation is adapted from `StableMarriage.Profile` in
`FormalConjecturesForMathlib/Combinatorics/StableMarriage.lean`, formal-conjectures PR #4955,
revision `db05d685417a9c711d7438ea966e42ff605f0413`:
https://github.com/google-deepmind/formal-conjectures/blob/db05d685417a9c711d7438ea966e42ff605f0413/FormalConjecturesForMathlib/Combinatorics/StableMarriage.lean
The original code is copyright 2026 The Formal Conjectures Authors and licensed under Apache 2.0.
Here its single population-size parameter is generalized to two. Stability and deferred acceptance
are supplied by the existing matching library; no conjecture or alternative stability predicate
is imported.
-/

namespace MathEconLib.Matching.MarriageMarket

open scoped BigOperators

/-- Complete strict rank profiles for `m` men and `n` women, with zero-based ranks. -/
structure RankProfile (m n : ℕ) where
  /-- Each man's permutation assigns women distinct ranks. -/
  manRank : Fin m → Equiv.Perm (Fin n)
  /-- Each woman's permutation assigns men distinct ranks. -/
  womanRank : Fin n → Equiv.Perm (Fin m)
  deriving Inhabited, DecidableEq

namespace RankProfile

variable {m n : ℕ}

/-- A rank profile consists of the two unrestricted families of permutations. -/
def equivRanks (m n : ℕ) : RankProfile m n ≃
    ((Fin m → Equiv.Perm (Fin n)) × (Fin n → Equiv.Perm (Fin m))) where
  toFun p := (p.manRank, p.womanRank)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (RankProfile m n) := Fintype.ofEquiv _ (equivRanks m n).symm

/-- The full profile space has `(n!)^m (m!)^n` elements. -/
theorem card (m n : ℕ) : Fintype.card (RankProfile m n) =
    (Nat.factorial n) ^ m * (Nat.factorial m) ^ n := by
  rw [Fintype.card_congr (equivRanks m n)]
  simp [Fintype.card_perm]

/-- One-based partner rank; the outside option is below all `n` partners at rank `n+1`.
This is a position in an ordinal ranking, not a cardinal utility. -/
def rank (r : Equiv.Perm (Fin n)) : Option (Fin n) → ℕ
  | none => n + 1
  | some w => (r w).val + 1

@[simp] theorem rank_none (r : Equiv.Perm (Fin n)) : rank r none = n + 1 := rfl

@[simp] theorem rank_some (r : Equiv.Perm (Fin n)) (w : Fin n) :
    rank r (some w) = (r w).val + 1 := rfl

theorem rank_pos (r : Equiv.Perm (Fin n)) (o : Option (Fin n)) : 0 < rank r o := by
  cases o <;> simp [rank]

theorem rank_some_lt_none (r : Equiv.Perm (Fin n)) (w : Fin n) :
    rank r (some w) < rank r none := by
  simp [rank, (r w).isLt]

theorem rank_injective (r : Equiv.Perm (Fin n)) : Function.Injective (rank r) := by
  intro x y h
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some w => exact False.elim ((rank_some_lt_none r w).ne h.symm)
  | some v =>
    cases y with
    | none => exact False.elim ((rank_some_lt_none r v).ne h)
    | some w =>
      congr 1
      apply r.injective
      exact Fin.ext (Nat.add_right_cancel h)

/-- The existing marriage API prefers larger values, so its order is the dual rank order. -/
def rankOrder (r : Equiv.Perm (Fin n)) : LinearOrder (Option (Fin n)) :=
  LinearOrder.lift' (fun o ↦ OrderDual.toDual (rank r o)) (rank_injective r)

/-- Interpret a rank profile as the existing marriage-market structure. -/
def toMarriageMarket (p : RankProfile m n) : MarriageMarket (Fin m) (Fin n) where
  prefM i := rankOrder (p.manRank i)
  prefW j := rankOrder (p.womanRank j)

@[simp] theorem toMarriageMarket_ltM (p : RankProfile m n) (i : Fin m)
    (x y : Option (Fin n)) :
    p.toMarriageMarket.ltM i x y ↔ rank (p.manRank i) y < rank (p.manRank i) x := Iff.rfl

@[simp] theorem toMarriageMarket_ltW (p : RankProfile m n) (j : Fin n)
    (x y : Option (Fin m)) :
    p.toMarriageMarket.ltW j x y ↔ rank (p.womanRank j) y < rank (p.womanRank j) x := Iff.rfl

@[simp] theorem toMarriageMarket_acceptableM (p : RankProfile m n) (i : Fin m) (j : Fin n) :
    p.toMarriageMarket.AcceptableM i j := rank_some_lt_none _ _

@[simp] theorem toMarriageMarket_acceptableW (p : RankProfile m n) (j : Fin n) (i : Fin m) :
    p.toMarriageMarket.AcceptableW j i := rank_some_lt_none _ _

/-- Discrete measurable structure on the finite profile space. -/
instance : MeasurableSpace (RankProfile m n) := ⊤

/-- Independent uniform rankings for both populations, as the uniform law on all rank profiles.
This adapts `StableMarriage.uniformProfile` from the source cited above. -/
noncomputable def uniformProfile (m n : ℕ) : PMF (RankProfile m n) :=
  PMF.uniformOfFintype (RankProfile m n)

/-- Every full profile has equal mass. -/
theorem uniformProfile_apply (p : RankProfile m n) :
    uniformProfile m n p =
      (((Nat.factorial n) ^ m * (Nat.factorial m) ^ n : ℕ) : ENNReal)⁻¹ := by
  simp [uniformProfile, PMF.uniformOfFintype_apply, card]

/-- The full joint mass factors into the uniform masses of all individual rankings.
Because `equivRanks` is a bijection onto unrestricted ranking families, this characterizes
independent uniform preference lists, rather than only normalization of the joint law. -/
theorem uniformProfile_apply_eq_prod (p : RankProfile m n) :
    uniformProfile m n p =
      (∏ i : Fin m, PMF.uniformOfFintype (Equiv.Perm (Fin n)) (p.manRank i)) *
      (∏ j : Fin n, PMF.uniformOfFintype (Equiv.Perm (Fin m)) (p.womanRank j)) := by
  simp only [uniformProfile, PMF.uniformOfFintype_apply, card, Fintype.card_perm,
    Fintype.card_fin, Finset.prod_const, Finset.card_univ, Nat.cast_mul, Nat.cast_pow]
  rw [ENNReal.mul_inv (a := (n.factorial : ENNReal) ^ m)
    (b := (m.factorial : ENNReal) ^ n) (by simp) (by simp)]
  simp [ENNReal.inv_pow]

/-- The profile law is normalized, including empty populations. -/
theorem uniformProfile_univ (m n : ℕ) :
    (uniformProfile m n).toMeasure Set.univ = 1 := by simp

/-- Balanced rank profiles give complete outcomes under the existing executable proposer DA. -/
theorem isSome_galeShapleyComputable (p : RankProfile n n) (i : Fin n) :
    (p.toMarriageMarket.galeShapleyComputable i).isSome :=
  IsStableMatching.isSome_of_card_eq p.toMarriageMarket
    p.toMarriageMarket.stable_galeShapleyComputable rfl
    p.toMarriageMarket_acceptableM p.toMarriageMarket_acceptableW i

/-- The same balanced DA outcome matches every receiver. -/
theorem isSome_symm_galeShapleyComputable (p : RankProfile n n) (j : Fin n) :
    (p.toMarriageMarket.galeShapleyComputable.symm j).isSome := by
  have h := p.toMarriageMarket.stable_galeShapleyComputable
  exact IsStableMatching.isSome_of_card_eq p.toMarriageMarket.symm
    ((p.toMarriageMarket.isStableMatching_symm _).mpr h) rfl
    p.toMarriageMarket_acceptableW p.toMarriageMarket_acceptableM j

/-- Sum of one-based partner ranks for all proposers. This permits partial matchings,
with `none` assigned rank `n+1`; later matched-agent statistics must exclude unmatched agents. -/
def totalProposerRank (p : RankProfile m n) (μ : Fin m ≃. Fin n) : ℕ :=
  ∑ i, rank (p.manRank i) (μ i)

/-- Average one-based proposer rank in a balanced market. The empty population has average
zero by real division's convention; economic average-rank claims use a positive size.
This statistic measures ordinal position, not cardinal welfare. -/
noncomputable def averageProposerRank (p : RankProfile n n) (μ : Fin n ≃. Fin n) : ℝ :=
  (p.totalProposerRank μ : ℝ) / n

/-- Expected average rank of the existing executable proposer DA under independent uniform
preferences. Randomness is in the profile, not selection among stable outcomes. -/
noncomputable def expectedAverageProposerRank (n : ℕ) : ℝ :=
  ∫ p, p.averageProposerRank p.toMarriageMarket.galeShapleyComputable
    ∂(uniformProfile n n).toMeasure

/-- The expectation is the ordinary average over all finite profiles. -/
theorem expectedAverageProposerRank_eq_sum (n : ℕ) :
    expectedAverageProposerRank n =
      (∑ p : RankProfile n n,
        (p.totalProposerRank p.toMarriageMarket.galeShapleyComputable : ℝ)) /
        ((Fintype.card (RankProfile n n) : ℝ) * n) := by
  rw [expectedAverageProposerRank, PMF.integral_eq_sum]
  simp only [uniformProfile, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul, averageProposerRank]
  simp_rw [div_eq_mul_inv, mul_inv_rev]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- The empty-population average is zero under the documented division convention. -/
@[simp] theorem expectedAverageProposerRank_zero : expectedAverageProposerRank 0 = 0 := by
  rw [expectedAverageProposerRank_eq_sum]
  simp

set_option maxRecDepth 4096 in
/-- Exact finite evaluation of the existing executable DA on all sixteen two-by-two profiles.
Eight profiles have total proposer rank two and eight have total proposer rank three.
The kernel checks this finite calculation; no external computation supplies the proof. -/
theorem sum_totalProposerRank_two :
    (∑ p : RankProfile 2 2,
      p.totalProposerRank p.toMarriageMarket.galeShapleyComputable) = 40 := by
  decide +kernel

/-- Under independent uniform complete strict rankings in the two-by-two marriage market,
the existing executable proposer DA has expected average one-based proposer rank `5/4`.
This is a finite ordinal-rank benchmark, not a cardinal welfare or asymptotic claim. -/
theorem expectedAverageProposerRank_two : expectedAverageProposerRank 2 = 5 / 4 := by
  rw [expectedAverageProposerRank_eq_sum, ← Nat.cast_sum, sum_totalProposerRank_two, card]
  norm_num

end RankProfile
end MathEconLib.Matching.MarriageMarket
