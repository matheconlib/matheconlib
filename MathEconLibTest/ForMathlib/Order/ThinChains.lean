/-
Copyright (c) 2026 Georges Khater and MathEconLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georges Khater, MathEconLib contributors
-/
import MathEconLib.ForMathlib.Order.ThinChains

/-!
# Thin double chain partitions

These clients import only the general order module. The column-separation lemma is
applied to an infinite poset, and the fibre lemmas need finiteness only of the points.
-/

namespace MathEconLibTest.Order.ThinChains

open MathEconLib.Order

/-- An infinite chain as a single row, each point in its own column. -/
def natRow : ThinChains ℕ Unit ℕ where
  row _ := ()
  col := id
  label_injective := fun _ _ h => congrArg Prod.snd h
  row_comparable x y _ := le_total x y
  col_comparable x y _ := le_total x y

-- No finiteness assumption is needed to separate columns in a row.
example : natRow.col 0 ≠ natRow.col 1 := natRow.col_ne_of_row_eq rfl (by decide)

-- Fibres and prefixes need only finitely many points; labels may be infinite.
example {P R C : Type*} [PartialOrder P] [Fintype P] (t : ThinChains P R C) {x x' : P}
    (hrow : t.row x = t.row x') (hne : x ≠ x') :
    Disjoint (t.colPrefix x) (t.colPrefix x') :=
  t.colPrefix_disjoint_of_row_eq hrow hne

example {P R C : Type*} [PartialOrder P] [Fintype P] (t : ThinChains P R C) (x : P) :
    (t.colPrefix x : Set P) ⊆ Set.Iic x :=
  t.coe_colPrefix_subset_Iic x

example {P R C : Type*} [PartialOrder P] [Fintype P] (t : ThinChains P R C) {r : R}
    (hr : (t.rowFiber r).Nonempty) :
    ∃ v ∈ t.rowFiber r, Nat.card (t.RowPrefixPair r) ≤ Nat.card (Set.Iic v) :=
  t.rowPrefixPairs_card_le_downset hr

/-- A two-point chain as a single row. -/
def finRow : ThinChains (Fin 2) Unit (Fin 2) where
  row _ := ()
  col := id
  label_injective := fun _ _ h => congrArg Prod.snd h
  row_comparable x y _ := le_total x y
  col_comparable x y _ := le_total x y

example : Fintype.card (Fin 2) ≤ Fintype.card Unit * Fintype.card (Fin 2) :=
  finRow.card_le_rows_mul_cols

end MathEconLibTest.Order.ThinChains
