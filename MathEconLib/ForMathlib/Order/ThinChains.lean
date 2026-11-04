/-
Copyright (c) 2026 Georges Khater and MathEconLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georges Khater, MathEconLib contributors
-/
module

public import Mathlib.Order.Preorder.Finite
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Finset.Card
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Thin double chain partitions

A finite poset has two indexed chain partitions whose common cells contain
at most one point. The first counting lemmas are the row-column injection and
the disjointness of column prefixes within each row.
-/

@[expose] public section

namespace MathEconLib.Order

universe u v w

/-- Two partitions into chains, with at most one element in a row-column cell. -/
structure ThinChains (P : Type u) (R : Type v) (C : Type w)
    [PartialOrder P] where
  row : P → R
  col : P → C
  label_injective : Function.Injective (fun x => (row x, col x))
  row_comparable : ∀ x y, row x = row y → x ≤ y ∨ y ≤ x
  col_comparable : ∀ x y, col x = col y → x ≤ y ∨ y ≤ x

namespace ThinChains

variable {P : Type u} {R : Type v} {C : Type w}
variable [PartialOrder P] [Fintype P] [Fintype R] [Fintype C]
variable (t : ThinChains P R C)

theorem card_le_rows_mul_cols (t : ThinChains P R C) :
    Fintype.card P ≤ Fintype.card R * Fintype.card C := by
  simpa only [Fintype.card_prod] using
    Fintype.card_le_of_injective (fun x : P => (t.row x, t.col x)) t.label_injective

/-- The fibre of one row. -/
noncomputable def rowFiber (t : ThinChains P R C) (r : R) : Finset P := by
  classical
  exact Finset.univ.filter fun x => t.row x = r

/-- The inclusive prefix in `x`'s column. -/
noncomputable def colPrefix (t : ThinChains P R C) (x : P) : Finset P := by
  classical
  exact Finset.univ.filter fun y => t.col y = t.col x ∧ y ≤ x

/-- The inclusive downset of a point. -/
noncomputable def downset (t : ThinChains P R C) (x : P) : Finset P := by
  classical
  exact Finset.univ.filter fun y => y ≤ x

/-- The inclusive upset of a point. -/
noncomputable def upset (t : ThinChains P R C) (x : P) : Finset P := by
  classical
  exact Finset.univ.filter fun y => x ≤ y

@[simp] theorem mem_rowFiber {r : R} {x : P} :
    x ∈ t.rowFiber r ↔ t.row x = r := by
  simp [rowFiber]

@[simp] theorem mem_colPrefix {x y : P} :
    y ∈ t.colPrefix x ↔ t.col y = t.col x ∧ y ≤ x := by
  simp [colPrefix]

@[simp] theorem mem_downset {x y : P} :
    y ∈ t.downset x ↔ y ≤ x := by
  simp [downset]

@[simp] theorem mem_upset {x y : P} :
    y ∈ t.upset x ↔ x ≤ y := by
  simp [upset]

/-- A nonempty row has a largest element in the ambient order. -/
theorem exists_row_greatest {r : R} (hr : (t.rowFiber r).Nonempty) :
    ∃ v ∈ t.rowFiber r, ∀ x ∈ t.rowFiber r, x ≤ v := by
  obtain ⟨v, hv⟩ := (t.rowFiber r).exists_maximal hr
  refine ⟨v, hv.1, ?_⟩
  intro x hx
  have hxrow : t.row x = t.row v := by
    exact (t.mem_rowFiber.mp hx).trans (t.mem_rowFiber.mp hv.1).symm
  rcases t.row_comparable x v hxrow with hxv | hvx
  · exact hxv
  · exact hv.2 hx hvx

/-- Two distinct points of one row occupy different columns. -/
theorem col_ne_of_row_eq {x x' : P} (hrow : t.row x = t.row x')
    (hne : x ≠ x') : t.col x ≠ t.col x' := by
  intro hcol
  exact hne (t.label_injective (Prod.ext hrow hcol))

/-- Column prefixes of distinct elements of a row are disjoint. -/
theorem colPrefix_disjoint_of_row_eq {x x' : P}
    (hrow : t.row x = t.row x') (hne : x ≠ x') :
    Disjoint (t.colPrefix x) (t.colPrefix x') := by
  apply Finset.disjoint_left.mpr
  intro y hy hy'
  have hcol : t.col x = t.col x' :=
    (t.mem_colPrefix.mp hy).1.symm.trans (t.mem_colPrefix.mp hy').1
  exact t.col_ne_of_row_eq hrow hne hcol

/-- A column prefix below a row element lies below that row's greatest point. -/
theorem colPrefix_subset_downset_of_le {x v : P} (hxv : x ≤ v) :
    t.colPrefix x ⊆ t.downset v := by
  intro y hy
  exact t.mem_downset.mpr ((t.mem_colPrefix.mp hy).2.trans hxv)

/-- A point of a row together with an element of its column prefix. -/
def RowPrefixPair (r : R) :=
  {p : P × P // t.row p.1 = r ∧ t.col p.2 = t.col p.1 ∧ p.2 ≤ p.1}

/-- Prefix pairs in one row inject into the downset of its greatest point.
The second coordinate alone is injective because different row points have
different columns. -/
theorem rowPrefixPairs_card_le_downset {r : R}
    (hr : (t.rowFiber r).Nonempty) :
    ∃ v ∈ t.rowFiber r,
      Nat.card (t.RowPrefixPair r) ≤ Nat.card {y : P // y ≤ v} := by
  classical
  obtain ⟨v, hv, hgreatest⟩ := t.exists_row_greatest hr
  let f : t.RowPrefixPair r → {y : P // y ≤ v} := fun p =>
    ⟨p.1.2, (p.2.2.2).trans
      (hgreatest p.1.1 (t.mem_rowFiber.mpr p.2.1))⟩
  have hinj : Function.Injective f := by
    intro p q hpq
    have hy : p.1.2 = q.1.2 := congrArg Subtype.val hpq
    have hrow : t.row p.1.1 = t.row q.1.1 := p.2.1.trans q.2.1.symm
    have hcol : t.col p.1.1 = t.col q.1.1 := by
      calc
        t.col p.1.1 = t.col p.1.2 := p.2.2.1.symm
        _ = t.col q.1.2 := congrArg t.col hy
        _ = t.col q.1.1 := q.2.2.1
    have hx : p.1.1 = q.1.1 := t.label_injective (Prod.ext hrow hcol)
    apply Subtype.ext
    exact Prod.ext hx hy
  letI : Fintype (t.RowPrefixPair r) := by
    change Fintype
      {p : P × P // t.row p.1 = r ∧ t.col p.2 = t.col p.1 ∧ p.2 ≤ p.1}
    infer_instance
  exact ⟨v, hv, by
    simpa only [Nat.card_eq_fintype_card] using
      (Fintype.card_le_of_injective f hinj)⟩

end ThinChains
end MathEconLib.Order
