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

Compose Mathlib's antisymmetrization, lexicographic product, and injective order lift.
The input preorder remains on the original carrier; its quotient is only used to construct
a linear refinement. An explicit priority embedding fixes how distinct indifferent elements
are ordered. This construction is noncomputable.

`isGreatest_tieBreakOrder_iff` characterizes a refined greatest element by original greatness
and highest priority among original greatest elements. `exists_isGreatest_tieBreakOrder_iff`
expresses attainment as existence of a greatest value in their priority image.
Finite nonempty original greatest-element sets guarantee attainment even when the ambient set
is infinite. Under `WellFoundedGT` on priorities, refinement attainment is equivalent to original
attainment; well-founded priorities alone do not provide an original greatest element.
-/

@[expose] public section

namespace MathEconLib.Order

variable {α β : Type*} [LinearOrder β]

/-- Resolve indifference by a fixed injective priority. Higher priority is preferred.
The weak preference is compared first, using its Mathlib antisymmetrization. -/
@[instance_reducible]
noncomputable def tieBreakOrder (pref : Preorder α) (complete : Std.Total pref.le)
    (priority : α ↪ β) : LinearOrder α := by
  classical
  let := pref
  let := complete
  let : IsPreorder α (· ≤ ·) := inferInstance
  exact LinearOrder.lift'
    (fun a : α ↦ toLex (toAntisymmetrization (· ≤ ·) a, priority a))
    (fun _ _ h ↦ priority.injective (congrArg (fun p ↦ (ofLex p).2) h))

/-- The refinement preserves weak preference and consults priority only within a tie. -/
theorem tieBreakOrder_le_iff (pref : Preorder α) (complete : Std.Total pref.le)
    (priority : α ↪ β) (a b : α) :
    (tieBreakOrder pref complete priority).le a b ↔
      pref.le a b ∧ (AntisymmRel pref.le a b → priority a ≤ priority b) := by
  classical
  let := pref
  let := complete
  let : IsPreorder α (· ≤ ·) := inferInstance
  change (toLex (toAntisymmetrization (· ≤ ·) a, priority a) ≤
    toLex (toAntisymmetrization (· ≤ ·) b, priority b)) ↔ _
  rw [Prod.Lex.toLex_le_toLex']
  change (a ≤ b ∧ (toAntisymmetrization (· ≤ ·) a =
    toAntisymmetrization (· ≤ ·) b → priority a ≤ priority b)) ↔ _
  exact and_congr_right fun _ ↦ imp_congr_left (show _ ↔ _ from Quotient.eq)

/-- A comparison in the refined order is a weak-preference comparison. -/
theorem tieBreakOrder_le (pref : Preorder α) (complete : Std.Total pref.le)
    (priority : α ↪ β) {a b : α} (h : (tieBreakOrder pref complete priority).le a b) :
    pref.le a b :=
  ((tieBreakOrder_le_iff pref complete priority a b).mp h).1

/-- A greatest element of the refinement is an original greatest element with highest priority
among all original greatest elements. Neither set needs to be finite. -/
theorem isGreatest_tieBreakOrder_iff (pref : Preorder α) (complete : Std.Total pref.le)
    (priority : α ↪ β) {S : Set α} {a : α} :
    (letI := (tieBreakOrder pref complete priority).toPreorder; IsGreatest S a) ↔
      (letI := pref; IsGreatest S a ∧ ∀ b, IsGreatest S b → priority b ≤ priority a) := by
  let := pref
  refine ⟨?_, ?_⟩
  · intro ha
    have hgreatest : IsGreatest S a :=
      ⟨ha.1, fun b hb ↦ tieBreakOrder_le pref complete priority (ha.2 hb)⟩
    exact ⟨hgreatest, fun b hb ↦
      ((tieBreakOrder_le_iff pref complete priority b a).mp (ha.2 hb.1)).2
        ⟨hgreatest.2 hb.1, hb.2 hgreatest.1⟩⟩
  · exact fun ⟨ha, hpriority⟩ ↦ ⟨ha.1, fun b hb ↦
      (tieBreakOrder_le_iff pref complete priority b a).mpr
        ⟨ha.2 hb, fun hindiff ↦ hpriority b
          ⟨hb, fun c hc ↦ le_trans (ha.2 hc) hindiff.2⟩⟩⟩

/-- The refinement attains a greatest element exactly when priorities attain a greatest value
on the original greatest-element set. Membership in the image includes original attainment. -/
theorem exists_isGreatest_tieBreakOrder_iff (pref : Preorder α) (complete : Std.Total pref.le)
    (priority : α ↪ β) (S : Set α) :
    (∃ a, letI := (tieBreakOrder pref complete priority).toPreorder; IsGreatest S a) ↔
      ∃ p, IsGreatest (priority '' {a | letI := pref; IsGreatest S a}) p := by
  exact ⟨fun ⟨a, ha⟩ ↦
    let h := (isGreatest_tieBreakOrder_iff pref complete priority).mp ha
    ⟨priority a, ⟨a, h.1, rfl⟩, fun _ ⟨b, hb, heq⟩ ↦ heq ▸ h.2 b hb⟩,
    fun ⟨_, ⟨⟨a, ha, rfl⟩, hmax⟩⟩ ↦
      ⟨a, (isGreatest_tieBreakOrder_iff pref complete priority).mpr
        ⟨ha, fun b hb ↦ hmax ⟨b, hb, rfl⟩⟩⟩⟩

/-- A finite nonempty original greatest-element set guarantees refinement attainment.
The ambient set may be infinite. -/
theorem exists_isGreatest_tieBreakOrder_of_finite
    (pref : Preorder α) (complete : Std.Total pref.le) (priority : α ↪ β) {S : Set α}
    (hfinite : {a | letI := pref; IsGreatest S a}.Finite)
    (hne : ∃ a, letI := pref; IsGreatest S a) :
    ∃ a, letI := (tieBreakOrder pref complete priority).toPreorder; IsGreatest S a := by
  apply (exists_isGreatest_tieBreakOrder_iff pref complete priority S).mpr
  obtain ⟨p, hp⟩ := (hfinite.image priority).exists_maximal (Set.Nonempty.image priority hne)
  exact ⟨p, hp.1, fun q hq ↦ (le_total q p).elim id (hp.2 hq)⟩

/-- Well-founded strict improvement of priorities guarantees refinement attainment whenever
the original preorder attains a greatest element. Original attainment is still required. -/
theorem exists_isGreatest_tieBreakOrder_of_wellFoundedGT [WellFoundedGT β]
    (pref : Preorder α) (complete : Std.Total pref.le) (priority : α ↪ β) {S : Set α}
    (hne : ∃ a, letI := pref; IsGreatest S a) :
    ∃ a, letI := (tieBreakOrder pref complete priority).toPreorder; IsGreatest S a := by
  apply (exists_isGreatest_tieBreakOrder_iff pref complete priority S).mpr
  obtain ⟨p, hp, hmax⟩ := wellFounded_gt.has_min
    (priority '' {a | letI := pref; IsGreatest S a}) (Set.Nonempty.image priority hne)
  exact ⟨p, hp, fun q hq ↦ not_lt.mp (hmax q hq)⟩

/-- Under well-founded strict improvement of priorities, refinement attainment is equivalent
to original attainment. No finiteness of either set is required. -/
theorem exists_isGreatest_tieBreakOrder_iff_of_wellFoundedGT [WellFoundedGT β]
    (pref : Preorder α) (complete : Std.Total pref.le) (priority : α ↪ β) (S : Set α) :
    (∃ a, letI := (tieBreakOrder pref complete priority).toPreorder; IsGreatest S a) ↔
      ∃ a, letI := pref; IsGreatest S a := by
  exact ⟨fun ⟨a, ha⟩ ↦
    ⟨a, ((isGreatest_tieBreakOrder_iff pref complete priority).mp ha).1⟩,
    exists_isGreatest_tieBreakOrder_of_wellFoundedGT pref complete priority⟩

/-- Resolving ties in an already linear order leaves that order unchanged. -/
theorem tieBreakOrder_of_linearOrder (pref : LinearOrder α) (priority : α ↪ β) :
    tieBreakOrder pref.toPreorder ⟨pref.le_total⟩ priority = pref := by
  apply LinearOrder.ext
  intro a b
  rw [tieBreakOrder_le_iff]
  exact ⟨And.left, fun hab ↦ ⟨hab, fun h ↦
    le_of_eq (congrArg priority (pref.le_antisymm a b h.1 h.2))⟩⟩

end MathEconLib.Order
