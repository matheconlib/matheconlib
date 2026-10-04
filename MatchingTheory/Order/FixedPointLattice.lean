import Mathlib.Order.FixedPoints

/-!
# Comparing fixed-point and ambient lattice operations

The complete lattice of fixed points inherits its order from the ambient
lattice. If the ambient join or meet of two fixed points is itself fixed,
it agrees with their operation in the fixed-point lattice. No closure of
fixed points under ambient joins or meets is assumed implicitly.
-/

open Function

namespace OrderHom

variable {L : Type*} [CompleteLattice L] (f : L →o L)

/-- The top of the fixed-point lattice has value `gfp`. -/
theorem fixedPoints_val_top : (⊤ : fixedPoints f).val = gfp f := by
  refine le_antisymm (f.isGreatest_gfp.2 (⊤ : fixedPoints f).property) ?_
  exact le_top (a := (⟨gfp f, f.isGreatest_gfp.1⟩ : fixedPoints f))

/-- The bottom of the fixed-point lattice has value `lfp`. -/
theorem fixedPoints_val_bot : (⊥ : fixedPoints f).val = lfp f := by
  refine le_antisymm ?_ (f.isLeast_lfp.2 (⊥ : fixedPoints f).property)
  exact bot_le (a := (⟨lfp f, f.isLeast_lfp.1⟩ : fixedPoints f))

/-- An ambient join that is fixed is also the join in the fixed-point lattice. -/
theorem fixedPoints_val_sup_of_isFixedPt {p q : fixedPoints f}
    (h : IsFixedPt f (p.val ⊔ q.val)) :
    (p ⊔ q).val = p.val ⊔ q.val := by
  let r : fixedPoints f := ⟨p.val ⊔ q.val, h⟩
  have hpr : p ≤ r := by
    change p.val ≤ p.val ⊔ q.val
    exact le_sup_left
  have hqr : q ≤ r := by
    change q.val ≤ p.val ⊔ q.val
    exact le_sup_right
  have hle : p ⊔ q ≤ r := sup_le hpr hqr
  have hge : r ≤ p ⊔ q := by
    change p.val ⊔ q.val ≤ (p ⊔ q).val
    exact sup_le (le_sup_left : p ≤ p ⊔ q) (le_sup_right : q ≤ p ⊔ q)
  exact congrArg _root_.Subtype.val (le_antisymm hle hge)

/-- An ambient meet that is fixed is also the meet in the fixed-point lattice. -/
theorem fixedPoints_val_inf_of_isFixedPt {p q : fixedPoints f}
    (h : IsFixedPt f (p.val ⊓ q.val)) :
    (p ⊓ q).val = p.val ⊓ q.val := by
  let r : fixedPoints f := ⟨p.val ⊓ q.val, h⟩
  have hrp : r ≤ p := by
    change p.val ⊓ q.val ≤ p.val
    exact inf_le_left
  have hrq : r ≤ q := by
    change p.val ⊓ q.val ≤ q.val
    exact inf_le_right
  have hge : r ≤ p ⊓ q := le_inf hrp hrq
  have hle : p ⊓ q ≤ r := by
    change (p ⊓ q).val ≤ p.val ⊓ q.val
    exact le_inf (inf_le_left : p ⊓ q ≤ p) (inf_le_right : p ⊓ q ≤ q)
  exact congrArg _root_.Subtype.val (le_antisymm hle hge)

end OrderHom
