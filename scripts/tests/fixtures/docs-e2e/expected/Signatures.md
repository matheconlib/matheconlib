# DocsFixture.Signatures — Declaration Signatures

Auto-extracted from `api-docs.db` by `scripts/extract_signatures.py`.

## DocsFixture.Signatures

- `definition DocsFixture.sortIdentity {α : Sort u} (x : α) : α`
- `definition DocsFixture.mapValue {α : Type u} {β : Type v} (f : α → β) (x : α) : β`
- `definition DocsFixture.strictIdentity ⦃α : Type u⦄ (x : α) : α`
- `definition DocsFixture.addValues {α : Type u} [Add α] (x y : α) : α`
- `definition DocsFixture.lessEqual {α : Type u} [inst : LE α] (x y : α) : Prop`
- `definition DocsFixture.autoIdentity {α : Sort u_1} (x : α) : α`
- `theorem DocsFixture.identity_eq {α : Sort u} (x : α) : sortIdentity x = x`
- `theorem DocsFixture.admitted : True [sorry]`

---
*8 declarations across 1 modules.*
