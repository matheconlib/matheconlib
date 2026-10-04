/-
Preference-induced choice, independent of agents and markets.
-/
import MatchingTheory.Choice.Basic
import Mathlib.Data.Finset.Max

/-!
# Choice from a linear preference order

`ofLinearOrder pref` selects the greatest available alternative above the
outside option `none`, where `pref : LinearOrder (Option α)` is data rather
than a globally installed order. Its definition needs neither finiteness nor
decidability. Unit demand and substitutability hold on arbitrary types.

Consistency requires existence of a greatest option whenever there is an
acceptable option. Here it is proved for finite menus, then for finite types.
On an infinite menu with no greatest option the choice is empty, so there is
no unconditional infinite-menu consistency assertion.

`map` transports a choice function along an embedding. In a marriage market,
the embeddings are `w ↦ (m, w)` and `m ↦ (m, w)`. This handles restriction to
an agent's own contracts without putting market data in the choice layer.
-/

universe u v

namespace ChoiceFunction

variable {α : Type u} {β : Type v}

/-- Choice of the greatest acceptable alternative. Larger options are
preferred, and `none` is the outside option. A menu without a greatest
acceptable alternative yields the empty set. -/
def ofLinearOrder (pref : LinearOrder (Option α)) : ChoiceFunction α :=
  letI := pref
  { toFun := fun Y =>
      {x | x ∈ Y ∧ none ≤ some x ∧ ∀ y ∈ Y, some y ≤ some x}
    choose_subset := fun _ _ hx => hx.1 }

@[simp] theorem mem_ofLinearOrder (pref : LinearOrder (Option α))
    {Y : Set α} {x : α} :
    x ∈ ofLinearOrder pref Y ↔
      x ∈ Y ∧ pref.le none (some x) ∧
        ∀ y ∈ Y, pref.le (some y) (some x) :=
  Iff.rfl

/-- Strict preferences imply unit demand, even for infinite menus. -/
theorem unitDemand_ofLinearOrder (pref : LinearOrder (Option α)) :
    (ofLinearOrder pref).UnitDemand := by
  letI := pref
  intro Y x hx y hy
  exact Option.some.inj
    (le_antisymm (hy.2.2 x hx.1) (hx.2.2 y hy.1))

/-- Deleting alternatives cannot displace a chosen greatest alternative. -/
theorem substitutable_ofLinearOrder (pref : LinearOrder (Option α)) :
    (ofLinearOrder pref).Substitutable := by
  apply substitutable_iff_chernoff.mpr
  intro Y Z hYZ x hx
  exact ⟨hx.2, hx.1.2.1, fun y hy => hx.1.2.2 y (hYZ hy)⟩

/-- A finite menu with an acceptable alternative has a chosen alternative. -/
theorem nonempty_ofLinearOrder_of_finite
    (pref : LinearOrder (Option α)) {Y : Set α} (hY : Y.Finite)
    {x : α} (hx : x ∈ Y) (haccept : pref.le none (some x)) :
    (ofLinearOrder pref Y).Nonempty := by
  classical
  letI := pref
  let s : Finset α := hY.toFinset
  let menu : Finset (Option α) := insert none (s.image some)
  have hmenu : menu.Nonempty := ⟨none, Finset.mem_insert_self _ _⟩
  have hsome_mem (y : α) (hy : y ∈ Y) : some y ∈ menu := by
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image_of_mem some (hY.mem_toFinset.mpr hy)
  have hxmax : some x ≤ menu.max' hmenu :=
    Finset.le_max' menu (some x) (hsome_mem x hx)
  have hmax_mem := Finset.max'_mem menu hmenu
  cases hmax : menu.max' hmenu with
  | none =>
      have hsome_none : some x = none :=
        le_antisymm (hmax ▸ hxmax) haccept
      cases hsome_none
  | some y =>
      have hy : y ∈ Y := by
        rw [hmax] at hmax_mem
        have hy_image : some y ∈ s.image some := by
          simpa [menu] using hmax_mem
        obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hy_image
        have hzy' : z = y := Option.some.inj hzy
        exact hzy' ▸ hY.mem_toFinset.mp hz
      refine ⟨y, hy, ?_, ?_⟩
      · have hnone : (none : Option α) ≤ menu.max' hmenu :=
          Finset.le_max' menu none (Finset.mem_insert_self _ _)
        exact hmax ▸ hnone
      · intro z hz
        have hzmax : some z ≤ menu.max' hmenu :=
          Finset.le_max' menu (some z) (hsome_mem z hz)
        exact hmax ▸ hzmax

/-- IRC at a finite menu. The ambient alternative type may be infinite. -/
theorem ofLinearOrder_eq_of_choice_subset
    (pref : LinearOrder (Option α)) {Y Z : Set α} (hY : Y.Finite)
    (hchoice : ofLinearOrder pref Y ⊆ Z) (hZY : Z ⊆ Y) :
    ofLinearOrder pref Z = ofLinearOrder pref Y := by
  letI := pref
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := nonempty_ofLinearOrder_of_finite pref hY
      (hZY hx.1) hx.2.1
    refine ⟨hZY hx.1, hx.2.1, ?_⟩
    intro z hz
    exact le_trans (hy.2.2 z hz) (hx.2.2 y (hchoice hy))
  · intro hx
    exact ⟨hchoice hx, hx.2.1, fun y hy => hx.2.2 y (hZY hy)⟩

theorem consistent_ofLinearOrder [Finite α]
    (pref : LinearOrder (Option α)) :
    (ofLinearOrder pref).Consistent := by
  intro Y Z hchoice hZY
  exact ofLinearOrder_eq_of_choice_subset pref (Set.toFinite Y) hchoice hZY

/-- Aggregate demand is monotone on finite menus, even when the ambient
alternative type is infinite. -/
theorem sizeMonotone_ofLinearOrder
    (pref : LinearOrder (Option α)) :
    (ofLinearOrder pref).SizeMonotone := by
  intro Y Z hZ hYZ
  rcases Set.eq_empty_or_nonempty (ofLinearOrder pref Y) with hY | ⟨x, hx⟩
  · simp [hY]
  · obtain ⟨z, hz⟩ := nonempty_ofLinearOrder_of_finite pref hZ
      (hYZ hx.1) hx.2.1
    rw [((unitDemand_ofLinearOrder pref) Y).eq_singleton_of_mem hx,
      ((unitDemand_ofLinearOrder pref) Z).eq_singleton_of_mem hz]
    simp

theorem pathIndependent_ofLinearOrder [Finite α]
    (pref : LinearOrder (Option α)) :
    (ofLinearOrder pref).PathIndependent :=
  (substitutable_ofLinearOrder pref).pathIndependent (consistent_ofLinearOrder pref)

/-- Finite preference-induced choice is decidable when menu membership is
provided as data. This does not make arbitrary `Set` inputs computable. -/
instance decidableMem_ofLinearOrder [Fintype α]
    (pref : LinearOrder (Option α)) (Y : Set α) [DecidablePred (· ∈ Y)] :
    DecidablePred (· ∈ ofLinearOrder pref Y) := by
  intro x
  letI := pref
  change Decidable (x ∈ Y ∧ none ≤ some x ∧ ∀ y ∈ Y, some y ≤ some x)
  infer_instance

/-- Transport a choice function along an embedding. Alternatives outside the
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

end ChoiceFunction
