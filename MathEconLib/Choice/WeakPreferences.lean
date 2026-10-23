/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLib.Choice.Induced
import MathEconLib.ForMathlib.Order.Refinement
import Mathlib.Order.Preorder.Finite

/-!
# Choice under weak preferences

Preferences are explicit Mathlib preorders, with larger elements weakly preferred.
Strict preference is the preorder's `lt`; indifference is `AntisymmRel pref.le`.
Completeness is supplied separately when finite existence or linear refinement needs it.

`maximizers` retains all greatest feasible alternatives, and `optimalBundles` retains their
represented bundles as a family of sets. It does not combine tied bundles into their union.
The definitions allow infinite menus; existence results require finite feasible sets.
An empty correspondence means no greatest feasible alternative exists, not that the empty
bundle is optimal. It may reflect infeasibility or failure of attainment.

`ChoiceFunction.ofWeakBundleOrder` uses a fixed priority to refine preferences and then calls
the existing `ofBundleOrder`. On finite menus with a feasible represented bundle, its output
belongs to `optimalBundles`. It inherits the old constructor's empty-set totalization if
the refined order has no greatest feasible bundle. This selector is noncomputable; it is
distinct from the correspondence. Strict preferences recover the existing constructor.

-/

namespace MathEconLib.Choice

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-- All greatest feasible alternatives under the supplied preorder. -/
def maximizers (pref : Preorder α) (S : Set α) : Set α :=
  {a | letI := pref; IsGreatest S a}

@[simp] theorem mem_maximizers (pref : Preorder α) {S : Set α} {a : α} :
    a ∈ maximizers pref S ↔ a ∈ S ∧ ∀ b ∈ S, pref.le b a := Iff.rfl

theorem maximizers_subset (pref : Preorder α) (S : Set α) : maximizers pref S ⊆ S :=
  fun _ h ↦ h.1

@[simp] theorem maximizers_empty (pref : Preorder α) : maximizers pref ∅ = ∅ := by
  ext a
  simp

/-- Any two maximizers are indifferent, although they need not be equal. -/
theorem indifferent_of_mem_maximizers (pref : Preorder α) {S : Set α} {a b : α}
    (ha : a ∈ maximizers pref S) (hb : b ∈ maximizers pref S) :
    AntisymmRel pref.le a b :=
  ⟨hb.2 ha.1, ha.2 hb.1⟩

/-- A nonempty finite feasible set attains a greatest element under complete preferences. -/
theorem maximizers_nonempty_of_finite (pref : Preorder α) (complete : Std.Total pref.le)
    {S : Set α} (hS : S.Finite) (hne : S.Nonempty) : (maximizers pref S).Nonempty := by
  letI := pref
  letI := complete
  obtain ⟨a, ha⟩ := hS.exists_maximal hne
  exact ⟨a, (Std.Total.directedOn S).maximal_iff_isGreatest.mp ha⟩

/-- The family of best represented bundles, retaining each tied bundle separately. -/
def optimalBundles (pref : Preorder β) (bundle : β ↪ Set α) (Y : Set α) : Set (Set α) :=
  bundle '' maximizers pref {b | bundle b ⊆ Y}

/-- Every bundle in the correspondence is feasible at the given menu. -/
theorem subset_of_mem_optimalBundles (pref : Preorder β) (bundle : β ↪ Set α)
    {Y A : Set α} (hA : A ∈ optimalBundles pref bundle Y) : A ⊆ Y := by
  obtain ⟨b, hb, rfl⟩ := hA
  exact hb.1

/-- Finite menus have a best bundle if some represented bundle is feasible. -/
theorem optimalBundles_nonempty_of_finite (pref : Preorder β) (complete : Std.Total pref.le)
    (bundle : β ↪ Set α) {Y : Set α} (hY : Y.Finite) (hne : ∃ b, bundle b ⊆ Y) :
    (optimalBundles pref bundle Y).Nonempty :=
  (maximizers_nonempty_of_finite pref complete
    (hY.finite_subsets.preimage_embedding bundle) hne).image bundle

namespace ChoiceFunction

/-- Select a bundle with a fixed priority among ties, using the existing strict constructor.
Priority is independent of the menu, with larger priority preferred. -/
noncomputable def ofWeakBundleOrder [LinearOrder γ] (pref : Preorder β)
    (complete : Std.Total pref.le) (priority : β ↪ γ) (bundle : β ↪ Set α) :
    ChoiceFunction α :=
  ofBundleOrder (Order.tieBreakOrder pref complete priority) bundle

/-- A feasible weak maximizer is selected when it has highest priority among feasible ties. -/
theorem ofWeakBundleOrder_eq_of_max [LinearOrder γ] (pref : Preorder β)
    (complete : Std.Total pref.le) (priority : β ↪ γ) (bundle : β ↪ Set α)
    {Y : Set α} {b : β} (hb : bundle b ⊆ Y)
    (hmax : ∀ c, bundle c ⊆ Y → pref.le c b)
    (hpriority : ∀ c, bundle c ⊆ Y → AntisymmRel pref.le c b → priority c ≤ priority b) :
    ofWeakBundleOrder pref complete priority bundle Y = bundle b :=
  ofBundleOrder_eq_of_max _ bundle hb fun c hc ↦
    (Order.tieBreakOrder_le_iff pref complete priority c b).mpr ⟨hmax c hc, hpriority c hc⟩

/-- Fixed tie-breaking selects one of the weakly best bundles on a finite feasible menu. -/
theorem ofWeakBundleOrder_mem_optimalBundles_of_finite [LinearOrder γ]
    (pref : Preorder β) (complete : Std.Total pref.le) (priority : β ↪ γ)
    (bundle : β ↪ Set α) {Y : Set α} (hY : Y.Finite) (hne : ∃ b, bundle b ⊆ Y) :
    ofWeakBundleOrder pref complete priority bundle Y ∈ optimalBundles pref bundle Y := by
  obtain ⟨b, hb, hmax⟩ := exists_greatest_bundle_of_finite
    (Order.tieBreakOrder pref complete priority) bundle hY hne
  rw [ofWeakBundleOrder, ofBundleOrder_eq_of_max _ bundle hb hmax]
  exact ⟨b, ⟨hb, fun c hc ↦ Order.tieBreakOrder_le pref complete priority
    (hmax c hc)⟩, rfl⟩

/-- For a strict order, fixed tie-breaking recovers the existing choice function. -/
@[simp] theorem ofWeakBundleOrder_linearOrder [LinearOrder γ] (pref : LinearOrder β)
    (priority : β ↪ γ) (bundle : β ↪ Set α) :
    ofWeakBundleOrder pref.toPreorder ⟨pref.le_total⟩ priority bundle =
      ofBundleOrder pref bundle := by
  simp only [ofWeakBundleOrder, Order.tieBreakOrder_of_linearOrder]

/-- The existing finite outside-option selector chooses a weak maximizer under the refinement. -/
theorem bestOption_mem_maximizers [DecidableEq α] [LinearOrder γ]
    (pref : Preorder (Option α)) (complete : Std.Total pref.le)
    (priority : Option α ↪ γ) (A : Finset α) :
    bestOption (Order.tieBreakOrder pref complete priority) A ∈
      maximizers pref (optionMenu A : Set (Option α)) :=
  ⟨bestOption_mem _ A,
    fun _ ho ↦ Order.tieBreakOrder_le pref complete priority (le_bestOption _ A ho)⟩

end ChoiceFunction

end MathEconLib.Choice
