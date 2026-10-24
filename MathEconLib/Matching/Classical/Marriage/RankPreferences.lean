/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors, Bo Cowgill
-/
import MathEconLib.Matching.Classical.Marriage.Preferences
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Basic.PEquiv
import Mathlib.Basic.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Finite ordinal rank profiles for marriage markets

Strict complete rankings of the opposite population specialize the existing optional-partner
orders. Smaller ranks are preferred, and every partner is preferred to remaining unmatched.
The two population sizes are independent parameters. Incomplete acceptable lists and ties
are not represented here; the underlying `MarriageMarket` permits unacceptable partners.

The adapter, side exchange, and assignment statistics are deterministic. This module depends
on neither probability nor deferred acceptance. Applying the proposer statistics to `p.symm`
and an inverse matching gives the receiver statistics without a second implementation.
Average rank includes all agents on the evaluated side; it is not a matched-agent average
or a cardinal-welfare measure.

The rank-profile representation is adapted from `StableMarriage.Profile` in
`FormalConjecturesForMathlib/Combinatorics/StableMarriage.lean`, formal-conjectures PR #4955,
revision `db05d685417a9c711d7438ea966e42ff605f0413`:
https://github.com/google-deepmind/formal-conjectures/blob/db05d685417a9c711d7438ea966e42ff605f0413/FormalConjecturesForMathlib/Combinatorics/StableMarriage.lean
The original code is copyright 2026 The Formal Conjectures Authors and licensed under Apache 2.0.
Here its single size parameter is generalized to two; existing marriage preferences and choice
supply the economic interpretation. The preference-port scoping in #161 may identify further
shared interfaces; this module introduces no alternative preference or stability foundation.
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

/-- Exchange the two sides and their ranking families. -/
def symm (p : RankProfile m n) : RankProfile n m := ⟨p.womanRank, p.manRank⟩

@[simp] theorem symm_symm (p : RankProfile m n) : p.symm.symm = p := rfl

/-- A rank profile consists of the two unrestricted families of permutations. -/
def equivRanks (m n : ℕ) : RankProfile m n ≃
    ((Fin m → Equiv.Perm (Fin n)) × (Fin n → Equiv.Perm (Fin m))) where
  toFun p := (p.manRank, p.womanRank)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (RankProfile m n) := Fintype.ofEquiv _ (equivRanks m n).symm

/-- An agent's ranking type, indexed by the disjoint union of both populations. -/
def Ranking (m n : ℕ) : Fin m ⊕ Fin n → Type :=
  Sum.elim (fun _ ↦ Equiv.Perm (Fin n)) (fun _ ↦ Equiv.Perm (Fin m))

instance (a : Fin m ⊕ Fin n) : Fintype (Ranking m n a) := by
  cases a <;> dsimp [Ranking] <;> infer_instance

instance (a : Fin m ⊕ Fin n) : Inhabited (Ranking m n a) := by
  cases a <;> dsimp [Ranking] <;> infer_instance

/-- The same profile as one family indexed by all agents; no restrictions link coordinates. -/
def equivAgentRanks (m n : ℕ) : RankProfile m n ≃ (∀ a, Ranking m n a) :=
  (equivRanks m n).trans (Equiv.sumPiEquivProdPi (Ranking m n)).symm

@[simp] theorem equivAgentRanks_inl (p : RankProfile m n) (i : Fin m) :
    equivAgentRanks m n p (Sum.inl i) = p.manRank i := rfl

@[simp] theorem equivAgentRanks_inr (p : RankProfile m n) (j : Fin n) :
    equivAgentRanks m n p (Sum.inr j) = p.womanRank j := rfl

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
  let e := (Equiv.optionCongr r).trans finSuccEquivLast.symm
  have h : rank r = Nat.succ ∘ Fin.val ∘ e := by
    funext o
    cases o <;> simp [e, rank]
  rw [h]
  exact Nat.succ_injective.comp (Fin.val_injective.comp e.injective)

/-- The existing marriage API prefers larger values, so its order is the dual rank order. -/
def rankOrder (r : Equiv.Perm (Fin n)) : LinearOrder (Option (Fin n)) :=
  LinearOrder.lift' (fun o ↦ OrderDual.toDual (rank r o)) (rank_injective r)

/-- Interpret a rank profile as the existing marriage-market structure. -/
def toMarriageMarket (p : RankProfile m n) : MarriageMarket (Fin m) (Fin n) where
  prefM i := rankOrder (p.manRank i)
  prefW j := rankOrder (p.womanRank j)

/-- Side exchange agrees with the existing marriage-market operation. -/
@[simp] theorem symm_toMarriageMarket (p : RankProfile m n) :
    p.symm.toMarriageMarket = p.toMarriageMarket.symm := rfl

@[simp] theorem toMarriageMarket_leM (p : RankProfile m n) (i : Fin m)
    (x y : Option (Fin n)) :
    p.toMarriageMarket.leM i x y ↔ rank (p.manRank i) y ≤ rank (p.manRank i) x := Iff.rfl

@[simp] theorem toMarriageMarket_leW (p : RankProfile m n) (j : Fin n)
    (x y : Option (Fin m)) :
    p.toMarriageMarket.leW j x y ↔ rank (p.womanRank j) y ≤ rank (p.womanRank j) x := Iff.rfl

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

/-- Every partner in a complete rank profile is acceptable. -/
theorem toMarriageMarket_noUnacceptablePartners (p : RankProfile m n) :
    p.toMarriageMarket.NoUnacceptablePartners :=
  ⟨p.toMarriageMarket_acceptableM, p.toMarriageMarket_acceptableW⟩

/-- Previous name for `toMarriageMarket_noUnacceptablePartners`. -/
theorem toMarriageMarket_universallyAcceptable (p : RankProfile m n) :
    p.toMarriageMarket.UniversallyAcceptable := p.toMarriageMarket_noUnacceptablePartners

/-- Sum of one-based partner ranks for all proposers. This permits partial matchings,
with `none` assigned rank `n+1`; later matched-agent statistics must exclude unmatched agents. -/
def totalProposerRank (p : RankProfile m n) (μ : Fin m ≃. Fin n) : ℕ :=
  ∑ i, rank (p.manRank i) (μ i)

/-- Average one-based rank over all `m` proposers, including unmatched proposers at rank `n+1`.
The empty population has average zero; economic average-rank claims use a positive size.
This statistic measures ordinal position, not cardinal welfare or a matched-agent average. -/
noncomputable def averageProposerRank (p : RankProfile m n) (μ : Fin m ≃. Fin n) : ℝ :=
  𝔼 i, (rank (p.manRank i) (μ i) : ℝ)

/-- Average proposer rank divides the total by the number of proposers, also for unequal sides. -/
theorem averageProposerRank_eq_total_div (p : RankProfile m n) (μ : Fin m ≃. Fin n) :
    p.averageProposerRank μ = (p.totalProposerRank μ : ℝ) / m := by
  simp [averageProposerRank, Fintype.expect_eq_sum_div_card, totalProposerRank, Nat.cast_sum]

/-- A pointwise better assignment has weakly lower total ordinal rank. -/
theorem totalProposerRank_le (p : RankProfile m n) {μ ν : Fin m ≃. Fin n}
    (h : ∀ i, p.toMarriageMarket.leM i (ν i) (μ i)) :
    p.totalProposerRank μ ≤ p.totalProposerRank ν :=
  Finset.sum_le_sum fun i _ ↦ (p.toMarriageMarket_leM i (ν i) (μ i)).mp (h i)

/-- A pointwise better assignment has weakly lower average ordinal rank. -/
theorem averageProposerRank_le (p : RankProfile m n) {μ ν : Fin m ≃. Fin n}
    (h : ∀ i, p.toMarriageMarket.leM i (ν i) (μ i)) :
    p.averageProposerRank μ ≤ p.averageProposerRank ν := by
  rw [averageProposerRank_eq_total_div, averageProposerRank_eq_total_div]
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (p.totalProposerRank_le h))
    (Nat.cast_nonneg _)

end RankProfile
end MathEconLib.Matching.MarriageMarket
