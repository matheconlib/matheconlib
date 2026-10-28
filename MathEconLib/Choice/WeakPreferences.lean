/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Choice.Induced
public import MathEconLib.Choice.Maximizers
public import MathEconLib.Preferences.Refinement

/-!
# Choice under weak preferences

Represent weakly optimal bundles as a correspondence, and select a bundle using a fixed
injective priority among ties. The public entry point is `MathEconLib.Choice`. Preferences are
explicit `Preference` values; fixed tie-breaking uses `CompletePreference` to supply totality.
Larger elements are weakly preferred, `Preference.lt` is strict preference, and
`AntisymmRel pref.le` is indifference.

## Main definitions

* `optimalBundles`: the represented bundles of greatest feasible indices. Feasibility means
  `bundle b ⊆ Y`. Tied bundles remain separate members of this family of sets.
* `ChoiceFunction.ofWeakBundleOrder`: the noncomputable selector induced by
  `CompletePreference.tieBreak` and `ChoiceFunction.ofBundleOrder`.

## Main statements

* `mem_optimalBundles_iff`: representation, feasibility, and weak optimality characterize
  membership in the correspondence.
* `mem_optimalBundles_tieBreak_iff`: refined optima have highest priority among weak maximizers.
* `optimalBundles_tieBreak_nonempty_iff`: the refined correspondence attains exactly when
  priority attains a greatest value on the weakly optimal feasible indices.
* `optimalBundles_subset_ofBundleOrder`: each strict optimum equals the strict selector's output.
* `ChoiceFunction.ofBundleOrder_mem_optimalBundles_of_maximizers_nonempty`: any
  comparison-preserving linear refinement selects a weak optimum when the refined order attains.
* `ChoiceFunction.ofWeakBundleOrder_mem_optimalBundles_of_finite_maximizers` and
  `ChoiceFunction.ofWeakBundleOrder_mem_optimalBundles_of_wellFoundedGT`: finite nonempty weak
  optimum sets or well-founded strict priority improvement with weak attainment suffice.
* `ChoiceFunction.ofWeakBundleOrder_of_linearOrder`: linear preferences recover strict choice.
* `ChoiceFunction.bestOption_mem_maximizers`: executable finite option choice is weakly optimal.

## Attainment and participation

All definitions allow infinite menus. A finite menu has finitely many feasible represented
indices because `bundle` is injective; existence still requires one feasible index. More
generally, only the weak-maximizer set needs to be finite and nonempty. Under `WellFoundedGT`
on priorities, weak attainment suffices even when that set is infinite.

An empty correspondence is different from a correspondence containing the empty bundle.
The former can indicate infeasibility or nonattainment. When no refined greatest feasible index
exists, the selector returns `∅`; this set need not be represented or weakly optimal. For
`ChoiceFunction.optionBundle`, it also represents the outside option. Contracts of utility one,
an outside option of utility zero, and unbounded increasing priorities yield weak optima but
no refined optimum, so the selector returns `∅` despite the outside option being suboptimal.
Outside-option participation certificates therefore use the refined order. The infinite-menu
and outside-tie regressions are in `MathEconLibTest.Choice.WeakPreferences`.

A comparison-preserving linear refinement already implies completeness of the original
preference: one direction of every pair is comparable in the linear order and is preserved.
The general refinement theorem does not construct missing comparisons for incomplete inputs.
Option-induced choice inherits unit demand from `ChoiceFunction.unitDemand_ofOptionLinearOrder`.

-/

@[expose] public section

namespace MathEconLib.Choice

open Preferences

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-- The family of best represented bundles, retaining each tied bundle separately. -/
def optimalBundles (pref : Preference β) (bundle : β ↪ Set α) (Y : Set α) : Set (Set α) :=
  bundle '' maximizers pref {b | bundle b ⊆ Y}

/-- Membership means being represented by a feasible index weakly above all feasible indices. -/
theorem mem_optimalBundles_iff (pref : Preference β) (bundle : β ↪ Set α) {Y A : Set α} :
    A ∈ optimalBundles pref bundle Y ↔
      ∃ b, bundle b = A ∧ bundle b ⊆ Y ∧ ∀ c, bundle c ⊆ Y → pref.le c b :=
  ⟨fun ⟨b, hb, h⟩ ↦ ⟨b, h, hb.1, hb.2⟩,
    fun ⟨b, h, hb, hmax⟩ ↦ ⟨b, ⟨hb, hmax⟩, h⟩⟩

/-- Bundle correspondence attainment is exactly attainment of its feasible indices. -/
theorem optimalBundles_nonempty_iff (pref : Preference β) (bundle : β ↪ Set α) (Y : Set α) :
    (optimalBundles pref bundle Y).Nonempty ↔ (maximizers pref {b | bundle b ⊆ Y}).Nonempty :=
  Set.image_nonempty

/-- Refined optimal bundles are represented by weakly optimal indices with highest priority. -/
theorem mem_optimalBundles_tieBreak_iff [LinearOrder γ] (pref : CompletePreference β)
    (priority : β ↪ γ) (bundle : β ↪ Set α) {Y A : Set α} :
    A ∈ optimalBundles (Preference.ofPreorder (pref.tieBreak priority).toPreorder) bundle Y ↔
      ∃ b, b ∈ maximizers pref.toPreference {c | bundle c ⊆ Y} ∧ bundle b = A ∧
        ∀ c ∈ maximizers pref.toPreference {d | bundle d ⊆ Y}, priority c ≤ priority b := by
  exact ⟨fun ⟨b, hb, heq⟩ ↦
    let h := (mem_maximizers_tieBreak_iff pref priority).mp hb
    ⟨b, h.1, heq, h.2⟩,
    fun ⟨b, hb, heq, hpriority⟩ ↦
      ⟨b, (mem_maximizers_tieBreak_iff pref priority).mpr ⟨hb, hpriority⟩, heq⟩⟩

/-- The refined correspondence is nonempty exactly when priority attains on weak optima. -/
theorem optimalBundles_tieBreak_nonempty_iff [LinearOrder γ] (pref : CompletePreference β)
    (priority : β ↪ γ) (bundle : β ↪ Set α) (Y : Set α) :
    (optimalBundles (Preference.ofPreorder (pref.tieBreak priority).toPreorder) bundle Y).Nonempty ↔
      ∃ p, IsGreatest (priority '' maximizers pref.toPreference {b | bundle b ⊆ Y}) p :=
  (optimalBundles_nonempty_iff _ bundle Y).trans
    (maximizers_tieBreak_nonempty_iff pref priority _)

/-- Every strict optimum is the strict constructor's output, including on infinite menus.
If attainment fails, the correspondence is empty and the inclusion remains valid. -/
theorem optimalBundles_subset_ofBundleOrder (pref : LinearOrder β) (bundle : β ↪ Set α)
    (Y : Set α) :
    optimalBundles (Preference.ofPreorder pref.toPreorder) bundle Y ⊆
      {ChoiceFunction.ofBundleOrder pref bundle Y} :=
  fun _ ⟨_, hb, heq⟩ ↦ Set.mem_singleton_iff.mpr
    (heq.symm.trans (ChoiceFunction.ofBundleOrder_eq_of_isGreatest pref bundle hb).symm)

/-- Every bundle in the correspondence is feasible at the given menu. -/
theorem subset_of_mem_optimalBundles (pref : Preference β) (bundle : β ↪ Set α)
    {Y A : Set α} (hA : A ∈ optimalBundles pref bundle Y) : A ⊆ Y := by
  obtain ⟨b, hb, rfl⟩ := hA
  exact hb.1

/-- A finite nonempty feasible bundle family has a weak optimum, even on an infinite menu. -/
theorem optimalBundles_nonempty_of_finite_feasible
    (pref : CompletePreference β) (bundle : β ↪ Set α)
    {Y : Set α} (hF : {b | bundle b ⊆ Y}.Finite) (hne : ∃ b, bundle b ⊆ Y) :
    (optimalBundles pref bundle Y).Nonempty :=
  (maximizers_nonempty_of_finite pref hF hne).image bundle

/-- Finite menus have a best bundle if some represented bundle is feasible. -/
theorem optimalBundles_nonempty_of_finite (pref : CompletePreference β)
    (bundle : β ↪ Set α) {Y : Set α} (hY : Y.Finite) (hne : ∃ b, bundle b ⊆ Y) :
    (optimalBundles pref bundle Y).Nonempty :=
  optimalBundles_nonempty_of_finite_feasible pref bundle
    (hY.finite_subsets.preimage_embedding bundle) hne

namespace ChoiceFunction

/-- Any comparison-preserving linear refinement selects a weak optimum when it attains.
The hypothesis concerns the refined order; weak attainment alone does not suffice. -/
theorem ofBundleOrder_mem_optimalBundles_of_maximizers_nonempty
    (pref : Preference β) (refined : LinearOrder β)
    (hrefine : ∀ a b, refined.le a b → pref.le a b) (bundle : β ↪ Set α) {Y : Set α}
    (hne : (maximizers (Preference.ofPreorder refined.toPreorder) {b | bundle b ⊆ Y}).Nonempty) :
    ofBundleOrder refined bundle Y ∈ optimalBundles pref bundle Y := by
  obtain ⟨b, hb⟩ := hne
  rw [ofBundleOrder_eq_of_isGreatest refined bundle hb]
  exact (mem_optimalBundles_iff pref bundle).mpr
    ⟨b, rfl, hb.1, fun c hc ↦ hrefine c b (hb.2 hc)⟩

/-- Any linear refinement selects a weak optimum from a finite nonempty feasible bundle family.
The menu itself need not be finite. The comparison-preservation hypothesis already implies
completeness of `pref`; this is not a construction completing an incomplete preference. -/
theorem ofBundleOrder_mem_optimalBundles_of_finite_feasible
    (pref : Preference β) (refined : LinearOrder β)
    (hrefine : ∀ a b, refined.le a b → pref.le a b)
    (bundle : β ↪ Set α) {Y : Set α}
    (hF : {b | bundle b ⊆ Y}.Finite) (hne : ∃ b, bundle b ⊆ Y) :
    ofBundleOrder refined bundle Y ∈ optimalBundles pref bundle Y :=
  ofBundleOrder_mem_optimalBundles_of_maximizers_nonempty pref refined hrefine bundle
    (maximizers_nonempty_of_finite (CompletePreference.ofLinearOrder refined) hF hne)

/-- Failure of refined attainment makes the strict constructor return its empty-set totalization. -/
theorem ofBundleOrder_eq_empty_of_maximizers_eq_empty (pref : LinearOrder β)
    (bundle : β ↪ Set α) {Y : Set α}
    (h : maximizers (Preference.ofPreorder pref.toPreorder) {b | bundle b ⊆ Y} = ∅) :
    ofBundleOrder pref bundle Y = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  exact fun _ ⟨b, hb, _, hmax⟩ ↦ Set.notMem_empty b
    (h ▸ (show b ∈ maximizers (Preference.ofPreorder pref.toPreorder) {c | bundle c ⊆ Y}
      from ⟨hb, hmax⟩))

/-- Select a bundle with a fixed priority among ties, using the existing strict constructor.
Priority is independent of the menu, with larger priority preferred. -/
noncomputable def ofWeakBundleOrder [LinearOrder γ] (pref : CompletePreference β)
    (priority : β ↪ γ) (bundle : β ↪ Set α) :
    ChoiceFunction α :=
  ofBundleOrder (pref.tieBreak priority) bundle

/-- A refined maximizer identifies the selected bundle on any menu. -/
theorem ofWeakBundleOrder_eq_of_mem_maximizers [LinearOrder γ] (pref : CompletePreference β)
    (priority : β ↪ γ) (bundle : β ↪ Set α) {Y : Set α} {b : β}
    (hb : b ∈ maximizers (Preference.ofPreorder (pref.tieBreak priority).toPreorder)
      {c | bundle c ⊆ Y}) :
    ofWeakBundleOrder pref priority bundle Y = bundle b :=
  ofBundleOrder_eq_of_isGreatest (pref.tieBreak priority) bundle hb

/-- Fixed tie-breaking selects a weak optimum when the refined feasible order attains. -/
theorem ofWeakBundleOrder_mem_optimalBundles_of_maximizers_nonempty [LinearOrder γ]
    (pref : CompletePreference β) (priority : β ↪ γ) (bundle : β ↪ Set α) {Y : Set α}
    (hne : (maximizers (Preference.ofPreorder (pref.tieBreak priority).toPreorder)
      {b | bundle b ⊆ Y}).Nonempty) :
    ofWeakBundleOrder pref priority bundle Y ∈ optimalBundles pref.toPreference bundle Y :=
  ofBundleOrder_mem_optimalBundles_of_maximizers_nonempty pref.toPreference
    (pref.tieBreak priority) (fun _ _ h ↦ pref.le_of_tieBreak_le priority h) bundle hne

/-- Finitely many weakly optimal indices suffice, even when the feasible family is infinite. -/
theorem ofWeakBundleOrder_mem_optimalBundles_of_finite_maximizers [LinearOrder γ]
    (pref : CompletePreference β) (priority : β ↪ γ) (bundle : β ↪ Set α) {Y : Set α}
    (hfinite : (maximizers pref.toPreference {b | bundle b ⊆ Y}).Finite)
    (hne : (optimalBundles pref.toPreference bundle Y).Nonempty) :
    ofWeakBundleOrder pref priority bundle Y ∈ optimalBundles pref.toPreference bundle Y :=
  ofWeakBundleOrder_mem_optimalBundles_of_maximizers_nonempty pref priority bundle
    (maximizers_tieBreak_nonempty_of_finite pref priority hfinite
      ((optimalBundles_nonempty_iff pref.toPreference bundle Y).mp hne))

/-- Well-founded strict priority improvement makes weak attainment sufficient for optimal
selection. -/
theorem ofWeakBundleOrder_mem_optimalBundles_of_wellFoundedGT [LinearOrder γ] [WellFoundedGT γ]
    (pref : CompletePreference β) (priority : β ↪ γ) (bundle : β ↪ Set α) {Y : Set α}
    (hne : (optimalBundles pref.toPreference bundle Y).Nonempty) :
    ofWeakBundleOrder pref priority bundle Y ∈ optimalBundles pref.toPreference bundle Y :=
  ofWeakBundleOrder_mem_optimalBundles_of_maximizers_nonempty pref priority bundle
    (maximizers_tieBreak_nonempty_of_wellFoundedGT pref priority
      ((optimalBundles_nonempty_iff pref.toPreference bundle Y).mp hne))

/-- A feasible weak maximizer is selected when it has highest priority among feasible ties. -/
theorem ofWeakBundleOrder_eq_of_max [LinearOrder γ] (pref : CompletePreference β)
    (priority : β ↪ γ) (bundle : β ↪ Set α)
    {Y : Set α} {b : β} (hb : bundle b ⊆ Y)
    (hmax : ∀ c, bundle c ⊆ Y → pref.le c b)
    (hpriority : ∀ c, bundle c ⊆ Y → AntisymmRel pref.le c b → priority c ≤ priority b) :
    ofWeakBundleOrder pref priority bundle Y = bundle b :=
  ofWeakBundleOrder_eq_of_mem_maximizers pref priority bundle
    ⟨hb, fun c hc ↦
      (pref.tieBreak_le_iff priority c b).mpr ⟨hmax c hc, hpriority c hc⟩⟩

/-- Fixed tie-breaking selects one of the weakly best bundles on a finite feasible menu. -/
theorem ofWeakBundleOrder_mem_optimalBundles_of_finite [LinearOrder γ]
    (pref : CompletePreference β) (priority : β ↪ γ)
    (bundle : β ↪ Set α) {Y : Set α} (hY : Y.Finite) (hne : ∃ b, bundle b ⊆ Y) :
    ofWeakBundleOrder pref priority bundle Y ∈ optimalBundles pref bundle Y :=
  ofBundleOrder_mem_optimalBundles_of_finite_feasible pref
    (pref.tieBreak priority)
    (fun _ _ h ↦ pref.le_of_tieBreak_le priority h) bundle
    (hY.finite_subsets.preimage_embedding bundle) hne

/-- For a strict order, fixed tie-breaking recovers the existing choice function. -/
@[simp] theorem ofWeakBundleOrder_of_linearOrder [LinearOrder γ] (pref : LinearOrder β)
    (priority : β ↪ γ) (bundle : β ↪ Set α) :
    ofWeakBundleOrder (CompletePreference.ofLinearOrder pref) priority bundle =
      ofBundleOrder pref bundle := by
  simp only [ofWeakBundleOrder, CompletePreference.tieBreak_ofLinearOrder]

/-- Compatibility name for `ofWeakBundleOrder_of_linearOrder`. -/
alias ofWeakBundleOrder_linearOrder := ofWeakBundleOrder_of_linearOrder

/-- The existing finite outside-option selector chooses a weak maximizer under the refinement. -/
theorem bestOption_mem_maximizers [DecidableEq α] [LinearOrder γ]
    (pref : CompletePreference (Option α))
    (priority : Option α ↪ γ) (A : Finset α) :
    bestOption (pref.tieBreak priority) A ∈
      maximizers pref (optionMenu A : Set (Option α)) :=
  ⟨bestOption_mem _ A,
    fun _ ho ↦ pref.le_of_tieBreak_le priority (le_bestOption _ A ho)⟩

end ChoiceFunction

end MathEconLib.Choice

end
