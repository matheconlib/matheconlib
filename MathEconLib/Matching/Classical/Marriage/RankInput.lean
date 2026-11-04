/-
Copyright (c) 2026 Georges Khater and MathEconLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georges Khater, MathEconLib contributors
-/
module

public import MathEconLib.Matching.Classical.Marriage.Preferences
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.Nodup

/-! Explicit rank-list inputs for the existing marriage-market model.
Higher ranks are preferred; the last entry is the outside option. -/

@[expose] public section

namespace MathEconLib.Matching.MarriageMarket

def optionIndex {n : Nat} : Option (Fin n) → Fin (n + 1)
  | none => ⟨n, by omega⟩
  | some i => i.castSucc

theorem optionIndex_injective {n : Nat} : Function.Injective (@optionIndex n) := by
  intro a b h
  have hv := congrArg Fin.val h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b =>
      change n = b.val at hv
      omega
  | some a =>
    cases b with
    | none =>
      change a.val = n at hv
      omega
    | some b =>
      congr 1
      exact Fin.ext hv

/-- Total list lookup; the validity proofs below ensure that defaults are
never used for participants and their optional partners. -/
def rankAt (rows : List (List Nat)) (i j : Nat) : Nat :=
  (rows.getD i []).getD j 0

@[instance_reducible]
def rankRowOrder {n : Nat} (row : List Nat) (hlen : row.length = n + 1)
    (hnd : row.Nodup) : LinearOrder (Option (Fin n)) :=
  LinearOrder.lift' (fun o => row.getD (optionIndex o).val 0) (by
    let index (o : Option (Fin n)) : Fin row.length := Fin.cast hlen.symm (optionIndex o)
    have hget (o : Option (Fin n)) :
        row.getD (optionIndex o).val 0 = row.get (index o) :=
      List.getD_eq_get row 0 (index o)
    intro a b h
    change row.getD (optionIndex a).val 0 = row.getD (optionIndex b).val 0 at h
    rw [hget a, hget b] at h
    have hi := hnd.get_inj_iff.mp h
    apply optionIndex_injective
    apply Fin.ext
    exact congrArg (fun i : Fin row.length => i.val) hi)

/-- Balanced explicit input lists. Each participant lists a distinct numeric
rank for every partner and for remaining unmatched. -/
structure RankInput where
  men : List (List Nat)
  women : List (List Nat)
  women_length : women.length = men.length
  men_row_length : ∀ row ∈ men, row.length = men.length + 1
  women_row_length : ∀ row ∈ women, row.length = men.length + 1
  men_row_nodup : ∀ row ∈ men, row.Nodup
  women_row_nodup : ∀ row ∈ women, row.Nodup

namespace RankInput

def market (p : RankInput) : MarriageMarket (Fin p.men.length) (Fin p.men.length) where
  prefM m := rankRowOrder (p.men.get m)
    (p.men_row_length _ (List.get_mem _ _)) (p.men_row_nodup _ (List.get_mem _ _))
  prefW w :=
    let i : Fin p.women.length := Fin.cast p.women_length.symm w
    rankRowOrder (p.women.get i)
      (p.women_row_length _ (List.get_mem _ _)) (p.women_row_nodup _ (List.get_mem _ _))

theorem leM_iff (p : RankInput) (m : Fin p.men.length)
    (a b : Option (Fin p.men.length)) :
    p.market.leM m a b ↔
      rankAt p.men m.val (optionIndex a).val ≤ rankAt p.men m.val (optionIndex b).val := by
  simp only [rankAt, List.getD_eq_get p.men [] m]
  rfl

theorem ltM_iff (p : RankInput) (m : Fin p.men.length)
    (a b : Option (Fin p.men.length)) :
    p.market.ltM m a b ↔
      rankAt p.men m.val (optionIndex a).val < rankAt p.men m.val (optionIndex b).val := by
  simp only [rankAt, List.getD_eq_get p.men [] m]
  rfl

theorem leW_iff (p : RankInput) (w : Fin p.men.length)
    (a b : Option (Fin p.men.length)) :
    p.market.leW w a b ↔
      rankAt p.women w.val (optionIndex a).val ≤ rankAt p.women w.val (optionIndex b).val := by
  let i : Fin p.women.length := Fin.cast p.women_length.symm w
  have hrow : p.women.getD w.val [] = p.women.get i := List.getD_eq_get p.women [] i
  simp only [rankAt, hrow]
  rfl

end RankInput
end MathEconLib.Matching.MarriageMarket
