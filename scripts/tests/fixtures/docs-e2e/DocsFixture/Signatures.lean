/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Init

/-!
# Binder signatures

These declarations exercise universe parameters and binders in the documentation pipeline fixture.
-/

universe u v

namespace DocsFixture

def sortIdentity {α : Sort u} (x : α) : α := x

def mapValue {α : Type u} {β : Type v} (f : α → β) (x : α) : β := f x

abbrev strictIdentity ⦃α : Type u⦄ (x : α) : α := x

def addValues {α : Type u} [Add α] (x y : α) : α := x + y

def lessEqual {α : Type u} [inst : LE α] (x y : α) : Prop := x ≤ y

def autoIdentity (x : α) : α := x

theorem identity_eq {α : Sort u} (x : α) : sortIdentity x = x := rfl

theorem admitted : True := by sorry

private def hiddenValue : Nat := 37

end DocsFixture
