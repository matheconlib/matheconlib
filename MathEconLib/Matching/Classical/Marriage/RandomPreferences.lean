/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors, Bo Cowgill
-/
import MathEconLib.Matching.Classical.Marriage.Preferences
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

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

end RankProfile
end MathEconLib.Matching.MarriageMarket
