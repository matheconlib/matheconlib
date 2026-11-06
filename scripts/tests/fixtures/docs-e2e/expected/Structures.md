# DocsFixture.Structures — Declaration Signatures

Auto-extracted from `api-docs.db` by `scripts/extract_signatures.py`.

## DocsFixture.Structures

```
structure DocsFixture.Operations (α : Type u) : Type (u + 1)
  where
    DocsFixture.Operations.apply (x : α) : α
    DocsFixture.Operations.choose {β : Type u} (x : β) : β
```
```
structure DocsFixture.PointedOperations (α : Type u) extends DocsFixture.Operations α : Type (u + 1)
  where
    DocsFixture.PointedOperations.point : α
```
```
class DocsFixture.BaseOrder (α : Type u) [LE α] : Prop
  where
    DocsFixture.BaseOrder.reflexive (x : α) : x ≤ x
```
```
class DocsFixture.ExtendedOrder (α : Type u) [LE α] extends DocsFixture.BaseOrder α : Prop
  where
    DocsFixture.ExtendedOrder.transitive {x y z : α} (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z
```
- `instance DocsFixture.natBaseOrder : BaseOrder Nat`

---
*5 declarations across 1 modules.*
