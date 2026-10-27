/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Order.Antisymmetrization

/-!
# Linear refinement of a total preorder

Compose Mathlib's antisymmetrization, lexicographic product, and injective order lift.
The input preorder remains on the original carrier; its quotient is only used to construct
a linear refinement. An explicit priority embedding fixes how distinct indifferent elements
are ordered. This construction is noncomputable.
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

/-- Resolving ties in an already linear order leaves that order unchanged. -/
theorem tieBreakOrder_of_linearOrder (pref : LinearOrder α) (priority : α ↪ β) :
    tieBreakOrder pref.toPreorder ⟨pref.le_total⟩ priority = pref := by
  apply LinearOrder.ext
  intro a b
  rw [tieBreakOrder_le_iff]
  exact ⟨And.left, fun hab ↦ ⟨hab, fun h ↦
    le_of_eq (congrArg priority (pref.le_antisymm a b h.1 h.2))⟩⟩

end MathEconLib.Order
