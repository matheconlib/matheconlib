import MathEconLib.Choice.Conditions.Individual
import Mathlib.Order.Hom.Basic

/-!
# Mapping choice functions along embeddings

An embedding maps a choice function to another type of alternatives,
ignoring alternatives outside its range. Mapping composes, reflects equality
and pointwise inclusion, and preserves the optional conditions used below. No preference orders or finite populations are
needed here; the law of aggregate demand keeps its finite-menu hypothesis.
-/

namespace MathEconLib.Choice

universe u v w

namespace ChoiceFunction

variable {α : Type u} {β : Type v} {γ : Type w}

/-! ## Mapping along embeddings -/

/-- Map a choice function along an embedding. Alternatives outside the
range of the embedding are ignored. -/
def map (C : ChoiceFunction α) (e : α ↪ β) : ChoiceFunction β where
  toFun Y := e '' C (e ⁻¹' Y)
  choose_subset := by
    rintro Y _ ⟨x, hx, rfl⟩
    exact C.choose_subset (e ⁻¹' Y) hx

@[simp] theorem mem_map_iff (C : ChoiceFunction α) (e : α ↪ β)
    {Y : Set β} {y : β} :
    y ∈ C.map e Y ↔ ∃ x, x ∈ C (e ⁻¹' Y) ∧ e x = y :=
  Iff.rfl

/-- At an embedded alternative, membership is checked in the original menu. -/
@[simp] theorem mem_map (C : ChoiceFunction α) (e : α ↪ β)
    {Y : Set β} {x : α} :
    e x ∈ C.map e Y ↔ x ∈ C (e ⁻¹' Y) := by
  constructor
  · rintro ⟨y, hy, heq⟩
    exact e.injective heq ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Choice on an embedded menu is the embedded original choice. -/
@[simp] theorem map_apply_image (C : ChoiceFunction α) (e : α ↪ β)
    (Y : Set α) :
    C.map e (e '' Y) = e '' C Y := by
  change e '' C (e ⁻¹' (e '' Y)) = e '' C Y
  rw [Set.preimage_image_eq _ e.injective]

@[simp] theorem map_refl (C : ChoiceFunction α) :
    C.map (Function.Embedding.refl α) = C := by
  ext Y x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Mapping twice is mapping along the composite embedding. -/
@[simp] theorem map_map (C : ChoiceFunction α) (e : α ↪ β) (f : β ↪ γ) :
    (C.map e).map f = C.map (e.trans f) := by
  ext Y z
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨e x, ⟨x, hx, rfl⟩, rfl⟩

/-- Mapping along an embedding preserves and reflects pointwise enlargement. -/
theorem map_le_map_iff (e : α ↪ β) {C D : ChoiceFunction α} :
    C.map e ≤ D.map e ↔ C ≤ D := by
  constructor
  · intro h Y x hx
    have hmem : e x ∈ D.map e (e '' Y) := by
      apply h (e '' Y)
      rw [map_apply_image]
      exact ⟨x, hx, rfl⟩
    rw [map_apply_image] at hmem
    obtain ⟨y, hy, heq⟩ := hmem
    exact e.injective heq ▸ hy
  · rintro h Y _ ⟨x, hx, rfl⟩
    exact ⟨x, h _ hx, rfl⟩

theorem map_injective (e : α ↪ β) :
    Function.Injective (fun C : ChoiceFunction α => C.map e) := by
  intro C D h
  apply le_antisymm
  · exact (map_le_map_iff e).mp (le_of_eq h)
  · exact (map_le_map_iff e).mp (le_of_eq h.symm)

/-- Mapping along an embedding as an order embedding of choice functions.
The order is pointwise inclusion, so this bundles both preservation and
reflection of pointwise enlargement. -/
def mapOrderEmbedding (e : α ↪ β) : ChoiceFunction α ↪o ChoiceFunction β where
  toFun C := C.map e
  inj' := map_injective e
  map_rel_iff' := map_le_map_iff e

@[simp] theorem mapOrderEmbedding_apply (e : α ↪ β) (C : ChoiceFunction α) :
    mapOrderEmbedding e C = C.map e := rfl

theorem UnitDemand.map {C : ChoiceFunction α}
    (hunit : C.UnitDemand) (e : α ↪ β) :
    (C.map e).UnitDemand := by
  rintro Y _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact congrArg e (hunit _ hx hy)

theorem Consistent.map {C : ChoiceFunction α}
    (hcons : C.Consistent) (e : α ↪ β) :
    (C.map e).Consistent := by
  intro Y Z hchoice hZY
  have hchoice' : C (e ⁻¹' Y) ⊆ e ⁻¹' Z := by
    intro x hx
    exact hchoice ⟨x, hx, rfl⟩
  have hZY' : e ⁻¹' Z ⊆ e ⁻¹' Y := fun _ hx => hZY hx
  change e '' C (e ⁻¹' Z) = e '' C (e ⁻¹' Y)
  rw [hcons hchoice' hZY']

theorem Substitutable.map {C : ChoiceFunction α}
    (hsub : C.Substitutable) (e : α ↪ β) :
    (C.map e).Substitutable := by
  apply substitutable_iff_chernoff.mpr
  intro Y Z hYZ y hy
  obtain ⟨x, hx, rfl⟩ := hy.1
  refine ⟨x, ?_, rfl⟩
  exact substitutable_iff_chernoff.mp hsub
    (fun _ ha => hYZ ha) ⟨hx, hy.2⟩

/-- Cardinalities are preserved by embeddings, including for finite menus. -/
theorem SizeMonotone.map {C : ChoiceFunction α}
    (hsize : C.SizeMonotone) (e : α ↪ β) :
    (C.map e).SizeMonotone := by
  intro Y Z hZ hYZ
  change (e '' C (e ⁻¹' Y)).ncard ≤ (e '' C (e ⁻¹' Z)).ncard
  rw [Set.ncard_image_of_injective _ e.injective,
    Set.ncard_image_of_injective _ e.injective]
  exact hsize (hZ.preimage_embedding e) (fun _ hx => hYZ hx)

theorem FiniteValued.map {C : ChoiceFunction α}
    (hfinite : C.FiniteValued) (e : α ↪ β) :
    (C.map e).FiniteValued :=
  fun Y => (hfinite (e ⁻¹' Y)).image e

theorem PathIndependent.map {C : ChoiceFunction α}
    (hpath : C.PathIndependent) (e : α ↪ β) :
    (C.map e).PathIndependent :=
  (hpath.substitutable.map e).pathIndependent (hpath.consistent.map e)

end ChoiceFunction

end MathEconLib.Choice
