/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Init

/-!
# Structure signatures

These declarations exercise parents, fields, and instances in the documentation pipeline fixture.
-/

universe u

namespace DocsFixture

structure Operations (α : Type u) where
  apply (x : α) : α
  choose {β : Type u} (x : β) : β

structure PointedOperations (α : Type u) extends Operations α where
  point : α

class BaseOrder (α : Type u) [LE α] where
  reflexive (x : α) : x ≤ x

class ExtendedOrder (α : Type u) [LE α] extends BaseOrder α where
  transitive {x y z : α} (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z

instance natBaseOrder : BaseOrder Nat where
  reflexive := Nat.le_refl

end DocsFixture
