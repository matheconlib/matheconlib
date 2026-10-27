/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Order.Antisymmetrization
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Order.WellFounded

/-!
# Linear refinement of a total preorder

Refine a total preorder to a linear order on the same carrier. Compare antisymmetrization
classes first, then compare fixed injective priorities within each class. The quotient is
internal to the construction, which is noncomputable. Larger priorities give larger elements.

## Main definitions

* `tieBreakOrder`: the linear refinement of an explicit preorder `r` with totality proof `htotal`.

## Main statements

* `tieBreakOrder_le_iff`: a refined comparison is an original comparison, with a priority
  comparison required when both original directions hold.
* `le_of_tieBreakOrder_le`: every refined comparison is an original comparison.
* `isGreatest_tieBreakOrder_iff`: a refined greatest element is an original greatest element
  whose priority is greatest among original greatest elements.
* `exists_isGreatest_tieBreakOrder_iff`: attainment is equivalent to a greatest value in the
  priority image of the original greatest-element set.
* `exists_isGreatest_tieBreakOrder_of_finite`: a finite nonempty original greatest-element set
  guarantees refined attainment, even when the ambient set is infinite.
* `exists_isGreatest_tieBreakOrder_iff_of_wellFoundedGT`: under `WellFoundedGT` on the priority
  codomain, original and refined attainment are equivalent.
* `tieBreakOrder_of_linearOrder`: refining an already linear order recovers that order.

## Attainment conditions

Totality alone does not guarantee a greatest element of an infinite set. Existing original
greatest elements may also fail to have a greatest priority. Finiteness of their nonempty set
or well-founded strict priority improvement suffices. The well-founded condition still
requires original attainment.
-/

@[expose] public section

namespace MathEconLib.Order

variable {α β : Type*} [LinearOrder β]

/-- Refine a total preorder by comparing its antisymmetrization classes first and fixed
injective priorities second. Larger priorities give larger elements within a class. -/
@[instance_reducible]
noncomputable def tieBreakOrder (r : Preorder α) (htotal : Std.Total r.le)
    (priority : α ↪ β) : LinearOrder α := by
  classical
  let := r
  let := htotal
  let : IsPreorder α (· ≤ ·) := inferInstance
  exact LinearOrder.lift'
    (fun a : α ↦ toLex (toAntisymmetrization (· ≤ ·) a, priority a))
    (fun _ _ h ↦ priority.injective (congrArg (fun p ↦ (ofLex p).2) h))

/-- The refinement preserves the original relation and compares priorities within equivalence
classes of the preorder. -/
theorem tieBreakOrder_le_iff (r : Preorder α) (htotal : Std.Total r.le)
    (priority : α ↪ β) (a b : α) :
    (tieBreakOrder r htotal priority).le a b ↔
      r.le a b ∧ (AntisymmRel r.le a b → priority a ≤ priority b) := by
  classical
  let := r
  let := htotal
  let : IsPreorder α (· ≤ ·) := inferInstance
  change (toLex (toAntisymmetrization (· ≤ ·) a, priority a) ≤
    toLex (toAntisymmetrization (· ≤ ·) b, priority b)) ↔ _
  rw [Prod.Lex.toLex_le_toLex']
  change (a ≤ b ∧ (toAntisymmetrization (· ≤ ·) a =
    toAntisymmetrization (· ≤ ·) b → priority a ≤ priority b)) ↔ _
  exact and_congr_right fun _ ↦ imp_congr_left (show _ ↔ _ from Quotient.eq)

/-- A comparison in the refined order is a comparison in the original preorder. -/
theorem le_of_tieBreakOrder_le (r : Preorder α) (htotal : Std.Total r.le)
    (priority : α ↪ β) {a b : α} (h : (tieBreakOrder r htotal priority).le a b) :
    r.le a b :=
  ((tieBreakOrder_le_iff r htotal priority a b).mp h).1

/-- Compatibility name for `le_of_tieBreakOrder_le`. -/
alias tieBreakOrder_le := le_of_tieBreakOrder_le

/-- A greatest element of the refinement is an original greatest element with highest priority
among all original greatest elements. Neither set needs to be finite. -/
theorem isGreatest_tieBreakOrder_iff (r : Preorder α) (htotal : Std.Total r.le)
    (priority : α ↪ β) {S : Set α} {a : α} :
    (letI := (tieBreakOrder r htotal priority).toPreorder; IsGreatest S a) ↔
      (letI := r; IsGreatest S a ∧ ∀ b, IsGreatest S b → priority b ≤ priority a) := by
  let := r
  refine ⟨?_, ?_⟩
  · intro ha
    have hgreatest : IsGreatest S a :=
      ⟨ha.1, fun b hb ↦ le_of_tieBreakOrder_le r htotal priority (ha.2 hb)⟩
    exact ⟨hgreatest, fun b hb ↦
      ((tieBreakOrder_le_iff r htotal priority b a).mp (ha.2 hb.1)).2
        ⟨hgreatest.2 hb.1, hb.2 hgreatest.1⟩⟩
  · exact fun ⟨ha, hpriority⟩ ↦ ⟨ha.1, fun b hb ↦
      (tieBreakOrder_le_iff r htotal priority b a).mpr
        ⟨ha.2 hb, fun hindiff ↦ hpriority b
          ⟨hb, fun c hc ↦ le_trans (ha.2 hc) hindiff.2⟩⟩⟩

/-- The refinement attains a greatest element exactly when priorities attain a greatest value
on the original greatest-element set. Membership in the image includes original attainment. -/
theorem exists_isGreatest_tieBreakOrder_iff (r : Preorder α) (htotal : Std.Total r.le)
    (priority : α ↪ β) (S : Set α) :
    (∃ a, letI := (tieBreakOrder r htotal priority).toPreorder; IsGreatest S a) ↔
      ∃ p, IsGreatest (priority '' {a | letI := r; IsGreatest S a}) p := by
  exact ⟨fun ⟨a, ha⟩ ↦
    let h := (isGreatest_tieBreakOrder_iff r htotal priority).mp ha
    ⟨priority a, ⟨a, h.1, rfl⟩, fun _ ⟨b, hb, heq⟩ ↦ heq ▸ h.2 b hb⟩,
    fun ⟨_, ⟨⟨a, ha, rfl⟩, hmax⟩⟩ ↦
      ⟨a, (isGreatest_tieBreakOrder_iff r htotal priority).mpr
        ⟨ha, fun b hb ↦ hmax ⟨b, hb, rfl⟩⟩⟩⟩

/-- A finite nonempty original greatest-element set guarantees refinement attainment.
The ambient set may be infinite. -/
theorem exists_isGreatest_tieBreakOrder_of_finite
    (r : Preorder α) (htotal : Std.Total r.le) (priority : α ↪ β) {S : Set α}
    (hfinite : {a | letI := r; IsGreatest S a}.Finite)
    (hne : ∃ a, letI := r; IsGreatest S a) :
    ∃ a, letI := (tieBreakOrder r htotal priority).toPreorder; IsGreatest S a := by
  apply (exists_isGreatest_tieBreakOrder_iff r htotal priority S).mpr
  obtain ⟨p, hp⟩ := (hfinite.image priority).exists_maximal (Set.Nonempty.image priority hne)
  exact ⟨p, hp.1, fun q hq ↦ (le_total q p).elim id (hp.2 hq)⟩

/-- Well-founded strict improvement of priorities guarantees refinement attainment whenever
the original preorder attains a greatest element. Original attainment is still required. -/
theorem exists_isGreatest_tieBreakOrder_of_wellFoundedGT [WellFoundedGT β]
    (r : Preorder α) (htotal : Std.Total r.le) (priority : α ↪ β) {S : Set α}
    (hne : ∃ a, letI := r; IsGreatest S a) :
    ∃ a, letI := (tieBreakOrder r htotal priority).toPreorder; IsGreatest S a := by
  apply (exists_isGreatest_tieBreakOrder_iff r htotal priority S).mpr
  obtain ⟨p, hp, hmax⟩ := wellFounded_gt.has_min
    (priority '' {a | letI := r; IsGreatest S a}) (Set.Nonempty.image priority hne)
  exact ⟨p, hp, fun q hq ↦ not_lt.mp (hmax q hq)⟩

/-- Under well-founded strict improvement of priorities, refinement attainment is equivalent
to original attainment. No finiteness of either set is required. -/
theorem exists_isGreatest_tieBreakOrder_iff_of_wellFoundedGT [WellFoundedGT β]
    (r : Preorder α) (htotal : Std.Total r.le) (priority : α ↪ β) (S : Set α) :
    (∃ a, letI := (tieBreakOrder r htotal priority).toPreorder; IsGreatest S a) ↔
      ∃ a, letI := r; IsGreatest S a := by
  exact ⟨fun ⟨a, ha⟩ ↦
    ⟨a, ((isGreatest_tieBreakOrder_iff r htotal priority).mp ha).1⟩,
    exists_isGreatest_tieBreakOrder_of_wellFoundedGT r htotal priority⟩

/-- Resolving ties in an already linear order leaves that order unchanged. -/
theorem tieBreakOrder_of_linearOrder (r : LinearOrder α) (priority : α ↪ β) :
    tieBreakOrder r.toPreorder ⟨r.le_total⟩ priority = r := by
  apply LinearOrder.ext
  intro a b
  rw [tieBreakOrder_le_iff]
  exact ⟨And.left, fun hab ↦ ⟨hab, fun h ↦
    le_of_eq (congrArg priority (r.le_antisymm a b h.1 h.2))⟩⟩

end MathEconLib.Order
