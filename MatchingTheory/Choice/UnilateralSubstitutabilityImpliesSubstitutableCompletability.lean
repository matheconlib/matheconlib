/-
On finite domains, unilateral substitutability implies substitutable completability.
-/
import MatchingTheory.Choice.WeakSubstitutes
import MatchingTheory.Choice.Induced
import Mathlib.Data.Set.Finite.Basic

/-!
# Unilateral substitutability and consistent substitutable completions

For finite contract types, a consistent, many-to-one-feasible,
unilaterally substitutable choice function has a completion satisfying
both substitutability and consistency.

This is a result of Kadam (2016), but we give a new, more structural proof
using a substitute hull.

Our development does not implement Kadam's iterative preference-editing algorithm
or construct an explicit completed linear preference order.

Only the contract type must be finite; the counterparty type need not be.
-/

namespace ChoiceFunction

variable {A : Type*} {X : Type*}

namespace UnilateralSubstitutabilityImpliesSubstitutableCompletability

/-! ## The substitute hull -/

/-- Keep contracts that the original choice selects from some larger menu. -/
def hull (C : ChoiceFunction X) : ChoiceFunction X where
  toFun Y :=
    {x | x ∈ Y ∧ ∃ Z, Y ⊆ Z ∧ x ∈ C Z}
  choose_subset := by
    intro Y x hx
    exact hx.1

@[simp] theorem mem_hull
    (C : ChoiceFunction X) {Y : Set X} {x : X} :
    x ∈ hull C Y ↔
      x ∈ Y ∧ ∃ Z, Y ⊆ Z ∧ x ∈ C Z :=
  Iff.rfl

/-- The hull enlarges the original choice pointwise. -/
theorem subset_hull
    (C : ChoiceFunction X) (Y : Set X) :
    C Y ⊆ hull C Y := by
  intro x hx
  exact ⟨C.choose_subset Y hx, Y, fun _ hy => hy, hx⟩

/-- The hull is substitutable, without finiteness or IRC assumptions. -/
theorem hull_substitutable
    (C : ChoiceFunction X) :
    (hull C).Substitutable := by
  apply substitutable_iff_chernoff.mpr
  intro Y Z hYZ x hx
  rcases hx with ⟨⟨_hxZ, W, hZW, hxW⟩, hxY⟩
  exact ⟨hxY, W, fun y hy => hZW (hYZ hy), hxW⟩

/-- IRC is preserved by the substitute hull.

For a witness menu `W`, compare `W` with `W ∪ Y`. Every contract chosen
from the union that belongs to `Y` belongs to the hull at `Y`, and hence
to the retained menu `Z`. Thus the original choice from the union lies
inside `W`, allowing IRC to be applied. -/
theorem hull_consistent
    {C : ChoiceFunction X}
    (hIRC : C.Consistent) :
    (hull C).Consistent := by
  intro Y Z hchoice hZY
  ext x
  constructor
  · rintro ⟨hxZ, W, hZW, hxW⟩
    have hCW : C (W ∪ Y) ⊆ W := by
      intro y hy
      rcases C.choose_subset (W ∪ Y) hy with hyW | hyY
      · exact hyW
      · exact hZW
          (hchoice
            ⟨hyY, W ∪ Y, Set.subset_union_right, hy⟩)
    have heq : C W = C (W ∪ Y) := by
      apply hIRC
      · exact hCW
      · exact Set.subset_union_left
    refine ⟨hZY hxZ, W ∪ Y, Set.subset_union_right, ?_⟩
    rw [← heq]
    exact hxW
  · intro hx
    exact
      (substitutable_iff_chernoff.mp (hull_substitutable C))
        hZY ⟨hx, hchoice hx⟩

/-! ## Iterating unilateral substitutability over a finite set -/

/-- Rejection persists after finitely many additions when the rejected
contract's counterparty is absent from the base menus. -/
private theorem reject_union_of_finite
    {counterparty : X → A} {C : ChoiceFunction X}
    (hUS : C.UnilaterallySubstitutable counterparty)
    {x : X} {Y E : Set X}
    (hE : E.Finite)
    (hx : x ∉ C (insert x Y)) :
    Fresh counterparty x (Y ∪ E) →
      x ∉ C (insert x (Y ∪ E)) := by
  induction E, hE using Set.Finite.induction_on with
  | empty =>
      intro _
      simpa only [Set.union_empty] using hx
  | @insert z E _hz _hE ih =>
      intro hf
      have hf' : Fresh counterparty x (Y ∪ E) := by
        intro w hw
        apply hf w
        rcases hw with hw | hw
        · exact Or.inl hw
        · exact Or.inr (Set.mem_insert_of_mem z hw)
      have hnot :=
        hUS (z := z) hf' (ih hf')
      simpa only [Set.union_insert] using hnot

/-- The corresponding contraction statement on fresh finite menus. -/
private theorem mem_insert_of_subset_fresh
    {counterparty : X → A} {C : ChoiceFunction X}
    (hUS : C.UnilaterallySubstitutable counterparty)
    {x : X} {Y Z : Set X}
    (hZ : Z.Finite)
    (hYZ : Y ⊆ Z)
    (hfresh : Fresh counterparty x Z)
    (hxZ : x ∈ C (insert x Z)) :
    x ∈ C (insert x Y) := by
  classical
  by_contra hxY
  have hf : Fresh counterparty x (Y ∪ Z) := by
    intro w hw
    apply hfresh w
    rcases hw with hw | hw
    · exact hYZ hw
    · exact hw
  have hnot :=
    reject_union_of_finite hUS hZ hxY hf
  have hUnion : Y ∪ Z = Z :=
    Set.union_eq_right.mpr hYZ
  rw [hUnion] at hnot
  exact hnot hxZ

/-! ## Recalled contracts have represented counterparties -/

/-- If `x` is available at `Y` and chosen from a finite larger menu `Z`,
then its counterparty is represented in `C Y`.

Feasibility is required only for the choice from `Z`.

This conclusion does not assert that `x` itself belongs to `C Y`. -/
theorem exists_chosen_counterparty
    {counterparty : X → A} {C : ChoiceFunction X}
    (hUS : C.UnilaterallySubstitutable counterparty)
    (hIRC : C.Consistent)
    {Y Z : Set X} {x : X}
    (hZ : Z.Finite)
    (hfeasible : Set.InjOn counterparty (C Z))
    (hYZ : Y ⊆ Z)
    (hxY : x ∈ Y)
    (hxZ : x ∈ C Z) :
    ∃ y ∈ C Y, counterparty y = counterparty x := by
  classical

  -- Remove all contracts with x's counterparty, then reinsert x.
  let Y0 : Set X :=
    {y | y ∈ Y ∧ counterparty y ≠ counterparty x}
  let Z0 : Set X :=
    {y | y ∈ Z ∧ counterparty y ≠ counterparty x}

  have hY0Z0 : Y0 ⊆ Z0 := by
    intro y hy
    exact ⟨hYZ hy.1, hy.2⟩

  have hZ0 : Z0.Finite :=
    hZ.subset (fun _ hy => hy.1)

  have hfresh : Fresh counterparty x Z0 := by
    intro y hy
    exact hy.2

  -- Since x is chosen and the chosen set is feasible, all other
  -- contracts with its counterparty are rejected at Z.
  have hCZ : C Z ⊆ insert x Z0 := by
    intro y hy
    by_cases heq : counterparty y = counterparty x
    · exact Or.inl (hfeasible hy hxZ heq)
    · exact Or.inr ⟨C.choose_subset Z hy, heq⟩

  have hCZ0 : C (insert x Z0) = C Z := by
    apply hIRC
    · exact hCZ
    · exact Set.insert_subset
        (C.choose_subset Z hxZ)
        (fun _ hy => hy.1)

  have hxZ0 : x ∈ C (insert x Z0) := by
    rw [hCZ0]
    exact hxZ

  have hxY0 : x ∈ C (insert x Y0) :=
    mem_insert_of_subset_fresh
      hUS hZ0 hY0Z0 hfresh hxZ0

  -- If C Y contains no contract with x's counterparty, IRC also
  -- permits the corresponding deletion at Y, a contradiction.
  by_contra hnone

  have hCY : C Y ⊆ insert x Y0 := by
    intro y hy
    refine Or.inr ⟨C.choose_subset Y hy, ?_⟩
    intro heq
    exact hnone ⟨y, hy, heq⟩

  have hCY0 : C (insert x Y0) = C Y := by
    apply hIRC
    · exact hCY
    · exact Set.insert_subset hxY (fun _ hy => hy.1)

  apply hnone
  refine ⟨x, ?_, rfl⟩
  rw [← hCY0]
  exact hxY0

/-! ## The hull is a completion -/

/-- Under finite unilateral substitutability, IRC, and many-to-one
feasibility, the substitute hull is a completion.

If a newly chosen contract `x` was not in `C Y`, the preceding lemma
supplies a distinct contract in `C Y` with the same counterparty.
Both belong to the hull. -/
theorem hull_isCompletionOf [Finite X]
    {counterparty : X → A} {C : ChoiceFunction X}
    (hUS : C.UnilaterallySubstitutable counterparty)
    (hIRC : C.Consistent)
    (hfeasible : ∀ Y, Set.InjOn counterparty (C Y)) :
    C.IsCompletionOf counterparty (hull C) := by
  classical
  intro Y
  by_cases hsub : hull C Y ⊆ C Y
  · exact Or.inl
      (Set.Subset.antisymm hsub (subset_hull C Y))
  · right
    have hex : ∃ x ∈ hull C Y, x ∉ C Y := by
      by_contra hnone
      apply hsub
      intro x hx
      by_contra hxnot
      exact hnone ⟨x, hx, hxnot⟩

    obtain ⟨x, hxH, hxnot⟩ := hex
    rcases hxH with ⟨hxY, Z, hYZ, hxZ⟩

    obtain ⟨y, hy, hsame⟩ :=
      exists_chosen_counterparty
        hUS hIRC (Set.toFinite Z) (hfeasible Z)
        hYZ hxY hxZ

    refine
      ⟨x, ⟨hxY, Z, hYZ, hxZ⟩,
        y, subset_hull C Y hy, ?_, hsame.symm⟩
    intro hxy
    apply hxnot
    rw [hxy]
    exact hy

end UnilateralSubstitutabilityImpliesSubstitutableCompletability

/-! ## Public existence theorems -/

/-- Finite unilateral substitutability, IRC, and many-to-one feasibility
imply existence of a completion satisfying both substitutability and IRC. -/
theorem UnilaterallySubstitutable.hasConsistentSubstitutableCompletion
    [Finite X]
    {counterparty : X → A} {C : ChoiceFunction X}
    (hUS : C.UnilaterallySubstitutable counterparty)
    (hIRC : C.Consistent)
    (hfeasible : ∀ Y, Set.InjOn counterparty (C Y)) :
    C.HasConsistentSubstitutableCompletion counterparty := by
  exact
    ⟨UnilateralSubstitutabilityImpliesSubstitutableCompletability.hull C,
      UnilateralSubstitutabilityImpliesSubstitutableCompletability.hull_isCompletionOf hUS hIRC hfeasible,
      UnilateralSubstitutabilityImpliesSubstitutableCompletability.hull_substitutable C,
      UnilateralSubstitutabilityImpliesSubstitutableCompletability.hull_consistent hIRC⟩

/-- Forgetting IRC gives the weaker completability predicate. -/
theorem UnilaterallySubstitutable.substitutablyCompletable
    [Finite X]
    {counterparty : X → A} {C : ChoiceFunction X}
    (hUS : C.UnilaterallySubstitutable counterparty)
    (hIRC : C.Consistent)
    (hfeasible : ∀ Y, Set.InjOn counterparty (C Y)) :
    C.SubstitutablyCompletable counterparty :=
  (hUS.hasConsistentSubstitutableCompletion
    hIRC hfeasible).substitutablyCompletable

/-! ## Preference-induced choice -/

/-- Kadam's implication for preference-induced choice over represented
many-to-one-feasible bundles.

IRC follows from preference maximization on a finite contract type.
Feasibility follows from feasibility of every represented bundle. -/
theorem hasConsistentSubstitutableCompletion_ofBundleOrder
    [Finite X] {β : Type*}
    (counterparty : X → A)
    (pref : LinearOrder β)
    (bundle : β ↪ Set X)
    (hbundle : ∀ b, Set.InjOn counterparty (bundle b))
    (hUS :
      (ofBundleOrder pref bundle).UnilaterallySubstitutable
        counterparty) :
    (ofBundleOrder pref bundle).HasConsistentSubstitutableCompletion
      counterparty := by
  apply hUS.hasConsistentSubstitutableCompletion
  · exact consistent_ofBundleOrder pref bundle
  · intro Y x hx y hy hxy
    obtain ⟨b, hb, hxb, hmax⟩ :=
      (mem_ofBundleOrder pref bundle).mp hx
    have heq : ofBundleOrder pref bundle Y = bundle b :=
      ofBundleOrder_eq_of_max pref bundle hb hmax
    have hyb : y ∈ bundle b := by
      rw [← heq]
      exact hy
    exact hbundle b hxb hyb hxy

/-! ## Preference-induced completions

These corollaries use the finite unilateral-substitutability completion
theorem proved above.

The original choice is induced by preferences. The completion witness
is the substitute hull; no completed linear preference order is
constructed.
-/

/-- For preferences over counterparty-feasible bundles, neither
feasibility nor IRC needs to be supplied separately. -/
theorem hasConsistentSubstitutableCompletion_ofFeasibleBundleOrder
    [Finite X]
    (counterparty : X → A)
    (pref : LinearOrder (FeasibleBundle counterparty))
    (hUS :
      UnilaterallySubstitutable counterparty
        (ofFeasibleBundleOrder counterparty pref)) :
    HasConsistentSubstitutableCompletion counterparty
      (ofFeasibleBundleOrder counterparty pref) := by
  exact UnilaterallySubstitutable.hasConsistentSubstitutableCompletion
    hUS
    (consistent_ofFeasibleBundleOrder counterparty pref)
    (injOn_ofFeasibleBundleOrder counterparty pref)

/-- For unrestricted set preferences, counterparty feasibility of the
actual choices must be supplied separately.

IRC follows from preference maximization on a finite contract type. -/
theorem hasConsistentSubstitutableCompletion_ofSetLinearOrder
    [Finite X]
    (counterparty : X → A)
    (pref : LinearOrder (Set X))
    (hfeasible :
      ∀ Y, Set.InjOn counterparty (ofSetLinearOrder pref Y))
    (hUS :
      (ofSetLinearOrder pref).UnilaterallySubstitutable counterparty) :
    (ofSetLinearOrder pref).HasConsistentSubstitutableCompletion
      counterparty := by
  exact hUS.hasConsistentSubstitutableCompletion
    (consistent_ofSetLinearOrder pref)
    hfeasible

end ChoiceFunction
