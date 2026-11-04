/-
Copyright (c) 2026 Georges Khater and MathEconLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georges Khater, MathEconLib contributors
-/
module

public import MathEconLib.Matching.Classical.Marriage.StableOrder
public import Mathlib.Data.Fintype.Pi
public import Mathlib.SetTheory.Cardinal.Finite

/-! A bound on the size of the exact stable-matching count. -/

@[expose] public section

namespace MathEconLib.Matching.MarriageMarket.StableMatching

variable {M W : Type*} [Fintype M] [Fintype W] (mkt : MarriageMarket M W)

/-- Recording each man's partner is injective, including unmatched men.
In particular the binary output length of exact counting is polynomial in
the explicit preference-list input size. -/
theorem card_le_partner_assignments :
    Nat.card mkt.StableMatching ≤ (Fintype.card W + 1) ^ Fintype.card M := by
  classical
  have hinj : Function.Injective (fun μ : mkt.StableMatching =>
      fun m : M => μ.matching m) := by
    intro μ ν h
    apply ext mkt
    apply PEquiv.ext
    exact congrFun h
  have h := Nat.card_le_card_of_injective _ hinj
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_option] using h

/-- A coarse bound requiring at most one bit per possible pair, plus one
bit, to write the exact count in binary. -/
theorem card_le_two_pow_pairs :
    Nat.card mkt.StableMatching ≤ 2 ^ (Fintype.card M * Fintype.card W) := by
  calc
    Nat.card mkt.StableMatching ≤ (Fintype.card W + 1) ^ Fintype.card M :=
      card_le_partner_assignments mkt
    _ ≤ (2 ^ Fintype.card W) ^ Fintype.card M :=
      Nat.pow_le_pow_left (Nat.succ_le_of_lt (Nat.lt_two_pow_self)) _
    _ = 2 ^ (Fintype.card M * Fintype.card W) := by
      rw [← pow_mul, Nat.mul_comm]

end MathEconLib.Matching.MarriageMarket.StableMatching
