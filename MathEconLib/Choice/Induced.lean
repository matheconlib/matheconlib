/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
/-
Preference-induced choice, independent of agents and markets.
-/
import MathEconLib.Choice.Map
import MathEconLib.Choice.FiniteOption
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Set.Finite.Powerset
import Mathlib.Data.Set.Subsingleton
import Mathlib.Order.Basic

/-!
# Choice from linear preferences over bundles

A bundle is a set of alternatives.

`ofBundleOrder pref bundle` maximizes a linear preference order over a
represented family of bundles. The embedding `bundle : β ↪ Set α`
specifies the admissible bundles; a represented bundle is feasible at
menu `Y` precisely when it is a subset of `Y`.

`ofSetLinearOrder pref` admits every bundle and chooses the greatest
subset of the menu under `pref : LinearOrder (Set α)`, when one exists.

`ofOptionLinearOrder pref` is the singleton-or-empty specialization. It retains
the existing `LinearOrder (Option α)` API, interpreting `none` as `∅`
and `some x` as `{x}`.

`singletonPreference pref` restricts a preference order on all sets to
the singleton-or-empty bundles. Consequently,
`ofSingletonSetLinearOrder pref` derives singleton choice directly from
set preferences.

All definitions work on arbitrary types. If no greatest feasible bundle
exists, the choice is empty. Consistency is proved for finite menus,
then for finite alternative types.

Arbitrary bundle preferences need not induce substitutable or
size-monotone choice. Those properties are proved for the singleton
specialization.

Preference comparisons use `pref.le`, with larger elements weakly preferred.
They are distinct from set inclusion.
-/

namespace MathEconLib.Choice

universe u v

namespace ChoiceFunction

variable {α : Type u} {β : Type v}

/-! ## Choice over a represented family of bundles -/

/-- Choose the greatest feasible represented bundle.

`bundle` specifies the admissible bundles. Feasibility means containment
in the current menu. A menu without a greatest feasible bundle yields
the empty set, which need not itself be a represented bundle.

The existential definition needs no additional decidability instances.
Antisymmetry ensures that all maximizing witnesses represent the same
bundle. -/
def ofBundleOrder
    (pref : LinearOrder β) (bundle : β ↪ Set α) :
    ChoiceFunction α where
  toFun Y :=
    {x | ∃ b,
      bundle b ⊆ Y ∧
      x ∈ bundle b ∧
      ∀ c, bundle c ⊆ Y → pref.le c b}
  choose_subset := by
    rintro Y x ⟨b, hb, hx, _⟩
    exact hb hx

@[simp] theorem mem_ofBundleOrder
    (pref : LinearOrder β) (bundle : β ↪ Set α)
    {Y : Set α} {x : α} :
    x ∈ ofBundleOrder pref bundle Y ↔
      ∃ b,
        bundle b ⊆ Y ∧
        x ∈ bundle b ∧
        ∀ c, bundle c ⊆ Y → pref.le c b :=
  Iff.rfl

/-- Greatest feasible indices encode both feasibility and preference maximality.
The locally installed order is the supplied preference order, not set inclusion. -/
theorem isGreatest_feasibleBundle_iff
    (pref : LinearOrder β) (bundle : β ↪ Set α)
    {Y : Set α} {b : β} :
    letI := pref
    IsGreatest {c : β | bundle c ⊆ Y} b ↔
      bundle b ⊆ Y ∧ ∀ c, bundle c ⊆ Y → pref.le c b :=
  Iff.rfl

/-- Membership in preference-induced choice is witnessed by a greatest feasible
index. If no such index exists, the choice is empty. -/
theorem mem_ofBundleOrder_iff_exists_isGreatest
    (pref : LinearOrder β) (bundle : β ↪ Set α)
    {Y : Set α} {x : α} :
    letI := pref
    x ∈ ofBundleOrder pref bundle Y ↔
      ∃ b, IsGreatest {c : β | bundle c ⊆ Y} b ∧ x ∈ bundle b := by
  let := pref
  constructor
  · rintro ⟨b, hb, hx, hmax⟩
    exact ⟨b, ⟨hb, hmax⟩, hx⟩
  · rintro ⟨b, ⟨hb, hmax⟩, hx⟩
    exact ⟨b, hb, hx, hmax⟩

/-- If a greatest feasible bundle exists, it is exactly the chosen set. -/
theorem ofBundleOrder_eq_of_max
    (pref : LinearOrder β) (bundle : β ↪ Set α)
    {Y : Set α} {b : β}
    (hb : bundle b ⊆ Y)
    (hmax : ∀ c, bundle c ⊆ Y → pref.le c b) :
    ofBundleOrder pref bundle Y = bundle b := by
  let := pref
  ext x
  constructor
  · rintro ⟨c, hc, hx, hcmax⟩
    have hcb : c = b :=
      le_antisymm (hmax c hc) (hcmax b hb)
    simpa only [hcb] using hx
  · intro hx
    exact ⟨b, hb, hx, hmax⟩

/-- A standard greatest-element certificate identifies the chosen bundle. -/
theorem ofBundleOrder_eq_of_isGreatest
    (pref : LinearOrder β) (bundle : β ↪ Set α)
    {Y : Set α} {b : β}
    (hb : letI := pref; IsGreatest {c : β | bundle c ⊆ Y} b) :
    ofBundleOrder pref bundle Y = bundle b :=
  ofBundleOrder_eq_of_max pref bundle hb.1 hb.2

/-- A finite menu has only finitely many represented feasible bundles.
If at least one is feasible, a greatest one exists. -/
theorem exists_greatest_bundle_of_finite
    (pref : LinearOrder β) (bundle : β ↪ Set α)
    {Y : Set α} (hY : Y.Finite)
    (hne : ∃ b, bundle b ⊆ Y) :
    ∃ b, bundle b ⊆ Y ∧
      ∀ c, bundle c ⊆ Y → pref.le c b := by
  let := pref
  have hfinite : {b : β | bundle b ⊆ Y}.Finite :=
    hY.finite_subsets.preimage_embedding bundle
  exact Set.exists_max_image
    {b : β | bundle b ⊆ Y} id hfinite hne

/-- A nonempty family of feasible represented bundles on a finite menu has a
greatest index under the supplied preference order. -/
theorem exists_isGreatest_bundle_of_finite
    (pref : LinearOrder β) (bundle : β ↪ Set α)
    {Y : Set α} (hY : Y.Finite)
    (hne : ∃ b, bundle b ⊆ Y) :
    letI := pref
    ∃ b, IsGreatest {c : β | bundle c ⊆ Y} b :=
  exists_greatest_bundle_of_finite pref bundle hY hne

/-- IRC at a finite menu, for an arbitrary represented family of bundles.

The family need not contain the empty set: if no represented bundle is
feasible, the choice is empty. -/
theorem ofBundleOrder_eq_of_choice_subset
    (pref : LinearOrder β) (bundle : β ↪ Set α)
    {Y Z : Set α} (hY : Y.Finite)
    (hchoice : ofBundleOrder pref bundle Y ⊆ Z)
    (hZY : Z ⊆ Y) :
    ofBundleOrder pref bundle Z =
      ofBundleOrder pref bundle Y := by
  let := pref
  ext x
  constructor
  · rintro ⟨b, hbZ, hxb, hmaxb⟩
    have hbY : bundle b ⊆ Y :=
      fun z hz => hZY (hbZ hz)
    obtain ⟨c, hcY, hmaxc⟩ :=
      exists_greatest_bundle_of_finite pref bundle hY ⟨b, hbY⟩
    have hcZ : bundle c ⊆ Z := by
      intro z hz
      exact hchoice ⟨c, hcY, hz, hmaxc⟩
    refine ⟨b, hbY, hxb, ?_⟩
    intro d hdY
    exact le_trans (hmaxc d hdY) (hmaxb c hcZ)
  · rintro ⟨b, hbY, hxb, hmaxb⟩
    have hbZ : bundle b ⊆ Z := by
      intro z hz
      exact hchoice ⟨b, hbY, hz, hmaxb⟩
    refine ⟨b, hbZ, hxb, ?_⟩
    intro c hcZ
    exact hmaxb c (fun z hz => hZY (hcZ hz))

theorem consistent_ofBundleOrder [Finite α]
    (pref : LinearOrder β) (bundle : β ↪ Set α) :
    (ofBundleOrder pref bundle).Consistent := by
  intro Y Z hchoice hZY
  exact ofBundleOrder_eq_of_choice_subset
    pref bundle (Set.toFinite Y) hchoice hZY

/-! ## Linear preferences over all subsets -/

/-- Choice induced by a linear preference order over all sets.

At menu `Y`, every subset of `Y` is feasible, including `∅`. -/
def ofSetLinearOrder (pref : LinearOrder (Set α)) :
    ChoiceFunction α :=
  ofBundleOrder pref (Function.Embedding.refl (Set α))

@[simp] theorem mem_ofSetLinearOrder
    (pref : LinearOrder (Set α)) {Y : Set α} {x : α} :
    x ∈ ofSetLinearOrder pref Y ↔
      ∃ A : Set α,
        A ⊆ Y ∧
        x ∈ A ∧
        ∀ B : Set α, B ⊆ Y → pref.le B A :=
  Iff.rfl

theorem ofSetLinearOrder_eq_of_max
    (pref : LinearOrder (Set α)) {Y A : Set α}
    (hA : A ⊆ Y)
    (hmax : ∀ B : Set α, B ⊆ Y → pref.le B A) :
    ofSetLinearOrder pref Y = A :=
  ofBundleOrder_eq_of_max
    pref (Function.Embedding.refl (Set α)) hA hmax

/-- On a finite menu, the chosen set is weakly preferred to every
feasible bundle. -/
theorem le_ofSetLinearOrder_of_subset
    (pref : LinearOrder (Set α))
    {Y A : Set α} (hY : Y.Finite) (hA : A ⊆ Y) :
    pref.le A (ofSetLinearOrder pref Y) := by
  obtain ⟨B, hB, hmax⟩ :=
    exists_greatest_bundle_of_finite
      pref (Function.Embedding.refl (Set α))
      hY ⟨∅, Set.empty_subset Y⟩
  have heq : ofSetLinearOrder pref Y = B :=
    ofSetLinearOrder_eq_of_max pref hB hmax
  rw [heq]
  exact hmax A hA

theorem ofSetLinearOrder_eq_of_choice_subset
    (pref : LinearOrder (Set α))
    {Y Z : Set α} (hY : Y.Finite)
    (hchoice : ofSetLinearOrder pref Y ⊆ Z)
    (hZY : Z ⊆ Y) :
    ofSetLinearOrder pref Z = ofSetLinearOrder pref Y :=
  ofBundleOrder_eq_of_choice_subset
    pref (Function.Embedding.refl (Set α)) hY hchoice hZY

theorem consistent_ofSetLinearOrder [Finite α]
    (pref : LinearOrder (Set α)) :
    (ofSetLinearOrder pref).Consistent :=
  consistent_ofBundleOrder
    pref (Function.Embedding.refl (Set α))

/-! ## Singleton-or-empty bundles -/

/-- Represent the outside option by `∅` and an alternative by its singleton. -/
def optionBundle : Option α ↪ Set α where
  toFun := fun
    | none => ∅
    | some x => {x}
  inj' := by
    intro a b h
    cases a <;> cases b
    · rfl
    · simp at h
    · simp at h
    · simpa using h

@[simp] theorem optionBundle_none :
    optionBundle (none : Option α) = ∅ :=
  rfl

@[simp] theorem optionBundle_some (x : α) :
    optionBundle (some x) = {x} :=
  rfl

/-- The represented bundles are exactly the empty set and singletons. -/
theorem mem_range_optionBundle {A : Set α} :
    A ∈ Set.range (optionBundle : Option α ↪ Set α) ↔
      A.Subsingleton := by
  constructor
  · rintro ⟨o, rfl⟩
    cases o <;> simp
  · intro hA
    rcases hA.eq_empty_or_singleton with rfl | ⟨x, rfl⟩
    · exact ⟨none, rfl⟩
    · exact ⟨some x, rfl⟩

/-- Singleton-or-empty choice.

This preserves the original API, but is now a specialization of the
general bundle construction rather than a separate construction. -/
def ofOptionLinearOrder (pref : LinearOrder (Option α)) :
    ChoiceFunction α :=
  ofBundleOrder pref optionBundle

@[simp] theorem mem_ofOptionLinearOrder
    (pref : LinearOrder (Option α)) {Y : Set α} {x : α} :
    x ∈ ofOptionLinearOrder pref Y ↔
      x ∈ Y ∧ pref.le none (some x) ∧
        ∀ y ∈ Y, pref.le (some y) (some x) := by
  change
    (∃ o : Option α,
      optionBundle o ⊆ Y ∧
      x ∈ optionBundle o ∧
      ∀ p, optionBundle p ⊆ Y → pref.le p o) ↔ _
  constructor
  · rintro ⟨o, ho, hx, hmax⟩
    cases o with
    | none =>
        exact hx.elim
    | some y =>
        have hxy : x = y :=
          Set.mem_singleton_iff.mp hx
        subst y
        refine ⟨ho (by simp), hmax none (by simp), ?_⟩
        intro z hz
        exact hmax (some z) (by simpa using hz)
  · rintro ⟨hx, hnone, hmax⟩
    refine ⟨some x, ?_, ?_, ?_⟩
    · simpa using hx
    · simp
    · intro o ho
      cases o with
      | none =>
          exact hnone
      | some y =>
          exact hmax y (ho (by simp))

/-- The executable finite selector realizes singleton-or-empty set choice. -/
theorem bestOption_eq_some_iff_mem_ofOptionLinearOrder [DecidableEq α]
    (pref : LinearOrder (Option α)) (A : Finset α) {x : α} :
    bestOption pref A = some x ↔ x ∈ ofOptionLinearOrder pref (A : Set α) :=
  (bestOption_eq_some_iff pref A).trans (mem_ofOptionLinearOrder pref).symm

/-- Singleton bundle choice has unit demand, even on infinite menus. -/
theorem unitDemand_ofOptionLinearOrder
    (pref : LinearOrder (Option α)) :
    (ofOptionLinearOrder pref).UnitDemand := by
  let := pref
  intro Y x hx y hy
  have hx' := (mem_ofOptionLinearOrder pref).mp hx
  have hy' := (mem_ofOptionLinearOrder pref).mp hy
  exact Option.some.inj
    (le_antisymm
      (hy'.2.2 x hx'.1)
      (hx'.2.2 y hy'.1))

/-- Deleting alternatives cannot displace a chosen singleton. -/
theorem substitutable_ofOptionLinearOrder
    (pref : LinearOrder (Option α)) :
    (ofOptionLinearOrder pref).Substitutable := by
  apply substitutable_iff_chernoff.mpr
  intro Y Z hYZ x hx
  have hx' := (mem_ofOptionLinearOrder pref).mp hx.1
  apply (mem_ofOptionLinearOrder pref).mpr
  exact ⟨hx.2, hx'.2.1, fun y hy => hx'.2.2 y (hYZ hy)⟩

/-- A finite menu with an acceptable alternative has nonempty choice. -/
theorem nonempty_ofOptionLinearOrder_of_finite
    (pref : LinearOrder (Option α))
    {Y : Set α} (hY : Y.Finite)
    {x : α} (hx : x ∈ Y)
    (haccept : pref.le none (some x)) :
    (ofOptionLinearOrder pref Y).Nonempty := by
  let := pref
  have hxY : optionBundle (some x) ⊆ Y := by
    simpa using hx
  obtain ⟨o, ho, hmax⟩ :=
    exists_greatest_bundle_of_finite
      pref optionBundle hY ⟨some x, hxY⟩
  cases o with
  | none =>
      have hsome_none : some x = (none : Option α) :=
        le_antisymm (hmax (some x) hxY) haccept
      cases hsome_none
  | some y =>
      refine ⟨y, (mem_ofOptionLinearOrder pref).mpr ?_⟩
      refine ⟨ho (by simp), hmax none (by simp), ?_⟩
      intro z hz
      exact hmax (some z) (by simpa using hz)

/-- Singleton IRC is inherited from general bundle IRC. -/
theorem ofOptionLinearOrder_eq_of_choice_subset
    (pref : LinearOrder (Option α))
    {Y Z : Set α} (hY : Y.Finite)
    (hchoice : ofOptionLinearOrder pref Y ⊆ Z)
    (hZY : Z ⊆ Y) :
    ofOptionLinearOrder pref Z = ofOptionLinearOrder pref Y :=
  ofBundleOrder_eq_of_choice_subset
    pref optionBundle hY hchoice hZY

theorem consistent_ofOptionLinearOrder [Finite α]
    (pref : LinearOrder (Option α)) :
    (ofOptionLinearOrder pref).Consistent :=
  consistent_ofBundleOrder pref optionBundle

/-- The law of aggregate demand holds on finite menus. -/
theorem sizeMonotone_ofOptionLinearOrder
    (pref : LinearOrder (Option α)) :
    (ofOptionLinearOrder pref).SizeMonotone := by
  intro Y Z hZ hYZ
  rcases Set.eq_empty_or_nonempty (ofOptionLinearOrder pref Y) with
    hY | ⟨x, hx⟩
  · simp [hY]
  · have hx' := (mem_ofOptionLinearOrder pref).mp hx
    obtain ⟨z, hz⟩ :=
      nonempty_ofOptionLinearOrder_of_finite
        pref hZ (hYZ hx'.1) hx'.2.1
    rw [((unitDemand_ofOptionLinearOrder pref) Y).eq_singleton_of_mem hx,
      ((unitDemand_ofOptionLinearOrder pref) Z).eq_singleton_of_mem hz]
    simp

theorem pathIndependent_ofOptionLinearOrder [Finite α]
    (pref : LinearOrder (Option α)) :
    (ofOptionLinearOrder pref).PathIndependent :=
  (substitutable_ofOptionLinearOrder pref).pathIndependent
    (consistent_ofOptionLinearOrder pref)

/-- Finite singleton choice is decidable when menu membership is supplied
as data. Arbitrary `Set` inputs are not thereby made computable. -/
instance decidableMem_ofOptionLinearOrder [Fintype α]
    (pref : LinearOrder (Option α))
    (Y : Set α) [DecidablePred (· ∈ Y)] :
    DecidablePred (· ∈ ofOptionLinearOrder pref Y) := by
  intro x
  letI := pref
  exact decidable_of_iff
    (x ∈ Y ∧ none ≤ some x ∧ ∀ y ∈ Y, some y ≤ some x)
    (mem_ofOptionLinearOrder pref).symm

/-! ## Restricting set preferences to singleton-or-empty bundles -/

/-- Restrict a linear preference order over sets to `∅` and singletons.

No preference comparisons involving larger bundles affect this order. -/
def singletonPreference (pref : LinearOrder (Set α)) :
    LinearOrder (Option α) := by
  letI := pref
  exact LinearOrder.lift'
    (optionBundle : Option α ↪ Set α)
    optionBundle.injective

@[simp] theorem singletonPreference_le
    (pref : LinearOrder (Set α)) (a b : Option α) :
    (singletonPreference pref).le a b ↔
      pref.le (optionBundle a) (optionBundle b) :=
  Iff.rfl

/-- Singleton choice derived from a preference order over sets.

Only the empty set and singleton subsets of the menu are admissible.
This is generally different from unrestricted `ofSetLinearOrder pref`. -/
def ofSingletonSetLinearOrder (pref : LinearOrder (Set α)) :
    ChoiceFunction α :=
  ofOptionLinearOrder (singletonPreference pref)

@[simp] theorem mem_ofSingletonSetLinearOrder
    (pref : LinearOrder (Set α)) {Y : Set α} {x : α} :
    x ∈ ofSingletonSetLinearOrder pref Y ↔
      x ∈ Y ∧ pref.le ∅ {x} ∧
        ∀ y ∈ Y, pref.le {y} {x} :=
  mem_ofOptionLinearOrder (singletonPreference pref)

/-- An explicit set-based characterization of the singleton restriction. -/
theorem mem_ofSingletonSetLinearOrder_iff
    (pref : LinearOrder (Set α)) {Y : Set α} {x : α} :
    x ∈ ofSingletonSetLinearOrder pref Y ↔
      ∃ A : Set α,
        A.Subsingleton ∧
        A ⊆ Y ∧
        x ∈ A ∧
        ∀ B : Set α,
          B.Subsingleton → B ⊆ Y → pref.le B A := by
  rw [mem_ofSingletonSetLinearOrder]
  constructor
  · rintro ⟨hx, hnone, hmax⟩
    refine ⟨{x}, Set.subsingleton_singleton, ?_, by simp, ?_⟩
    · simpa using hx
    · intro B hB hBY
      rcases hB.eq_empty_or_singleton with rfl | ⟨y, rfl⟩
      · exact hnone
      · exact hmax y (hBY (by simp))
  · rintro ⟨A, hA, hAY, hx, hmax⟩
    have hEq : A = {x} :=
      hA.eq_singleton_of_mem hx
    subst A
    refine ⟨hAY (by simp), hmax ∅ (by simp) (by simp), ?_⟩
    intro y hy
    exact hmax {y} (by simp) (by simpa using hy)

theorem unitDemand_ofSingletonSetLinearOrder
    (pref : LinearOrder (Set α)) :
    (ofSingletonSetLinearOrder pref).UnitDemand :=
  unitDemand_ofOptionLinearOrder (singletonPreference pref)

theorem substitutable_ofSingletonSetLinearOrder
    (pref : LinearOrder (Set α)) :
    (ofSingletonSetLinearOrder pref).Substitutable :=
  substitutable_ofOptionLinearOrder (singletonPreference pref)

theorem ofSingletonSetLinearOrder_eq_of_choice_subset
    (pref : LinearOrder (Set α))
    {Y Z : Set α} (hY : Y.Finite)
    (hchoice : ofSingletonSetLinearOrder pref Y ⊆ Z)
    (hZY : Z ⊆ Y) :
    ofSingletonSetLinearOrder pref Z =
      ofSingletonSetLinearOrder pref Y :=
  ofOptionLinearOrder_eq_of_choice_subset
    (singletonPreference pref) hY hchoice hZY

theorem consistent_ofSingletonSetLinearOrder [Finite α]
    (pref : LinearOrder (Set α)) :
    (ofSingletonSetLinearOrder pref).Consistent :=
  consistent_ofOptionLinearOrder (singletonPreference pref)

theorem sizeMonotone_ofSingletonSetLinearOrder
    (pref : LinearOrder (Set α)) :
    (ofSingletonSetLinearOrder pref).SizeMonotone :=
  sizeMonotone_ofOptionLinearOrder (singletonPreference pref)

theorem pathIndependent_ofSingletonSetLinearOrder [Finite α]
    (pref : LinearOrder (Set α)) :
    (ofSingletonSetLinearOrder pref).PathIndependent :=
  pathIndependent_ofOptionLinearOrder (singletonPreference pref)

instance decidableMem_ofSingletonSetLinearOrder [Fintype α]
    (pref : LinearOrder (Set α))
    (Y : Set α) [DecidablePred (· ∈ Y)] :
    DecidablePred (· ∈ ofSingletonSetLinearOrder pref Y) :=
  decidableMem_ofOptionLinearOrder (singletonPreference pref) Y

end ChoiceFunction

end MathEconLib.Choice
