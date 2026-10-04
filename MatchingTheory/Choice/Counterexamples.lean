/-
Matching with contracts: counterexamples for the choice layer.
-/
import MatchingTheory.Choice.Basic

/-!
# Choice-layer counterexamples

`infiniteOrEmpty` — take the whole menu when it is infinite, nothing
otherwise — separates the single-new-alternative form of substitutability
(survey Definition 2.1 as printed) from the superset-form definition on
infinite types, **even in the presence of consistency/IRC**. This justifies
these design choices:

* the superset quantification in `ChoiceFunction.Substitutable` (the printed
  single-contract form is too weak to drive the finiteness-free fixed-point
  development), and
* retaining the literature's single-contract shape for the §6 weakened
  conditions (`MatchingTheory.Choice.WeakSubstitutes`), while exposing the
  hypotheses needed to extend their consequences beyond finite markets.

The completion theorem now permits arbitrary contract types when choice is
finite-valued. This example chooses an infinite set from an infinite menu,
so it does not satisfy that hypothesis.

No finite counterexample exists — that is the content of
`ChoiceFunction.substitutable_iff_forall_insert_insert` — so this is
inherently an infinite-domain phenomenon.
-/

namespace ChoiceFunction

namespace Counterexamples

/-- The choice function that takes the whole menu when it is infinite and
nothing otherwise. -/
noncomputable def infiniteOrEmpty (α : Type*) : ChoiceFunction α := by
  classical
  refine
    { toFun := fun Y => if Y.Infinite then Y else ∅
      choose_subset := ?_ }
  intro Y
  by_cases hY : Y.Infinite
  · rw [if_pos hY]
  · rw [if_neg hY]
    exact Set.empty_subset Y

/-- On an infinite menu, `infiniteOrEmpty` chooses the entire menu. -/
@[simp]
theorem infiniteOrEmpty_of_infinite
    {α : Type*} {Y : Set α} (hY : Y.Infinite) :
    infiniteOrEmpty α Y = Y := by
  classical
  change (if Y.Infinite then Y else ∅) = Y
  exact if_pos hY

/-- On a finite menu, `infiniteOrEmpty` chooses nothing. -/
@[simp]
theorem infiniteOrEmpty_of_finite
    {α : Type*} {Y : Set α} (hY : Y.Finite) :
    infiniteOrEmpty α Y = ∅ := by
  classical
  change (if Y.Infinite then Y else ∅) = ∅
  exact if_neg hY.not_infinite

/-- `infiniteOrEmpty` satisfies the single-new-alternative form.

If `insert x Y` is infinite, everything on the menu is chosen, so the
hypothesis `x ∉ C (insert x Y)` is false and the claim is vacuous. If
`insert x Y` is finite, then so is `insert x (insert z Y)`, and nothing is
chosen from it. -/
theorem forall_insert_insert_infiniteOrEmpty (α : Type*) :
    ∀ ⦃x z : α⦄ ⦃Y : Set α⦄,
      x ∉ infiniteOrEmpty α (insert x Y) →
        x ∉ infiniteOrEmpty α (insert x (insert z Y)) := by
  classical
  intro x z Y hx
  rcases Set.finite_or_infinite (insert x Y) with hfin | hinf
  · have hbig : (insert x (insert z Y)).Finite := by
      rw [Set.insert_comm x z]
      exact hfin.insert z
    rw [infiniteOrEmpty_of_finite hbig]
    simp
  · rw [infiniteOrEmpty_of_infinite hinf] at hx
    exact (hx (Set.mem_insert x Y)).elim

/-- `infiniteOrEmpty` is consistent.

For `C Y ⊆ Z ⊆ Y`: if `Y` is infinite then `C Y = Y`, so the sandwich
forces `Z = Y`; if `Y` is finite then `Z` is finite too and both choices
are empty. -/
theorem consistent_infiniteOrEmpty (α : Type*) :
    (infiniteOrEmpty α).Consistent := by
  classical
  intro Y Z hCY hZY
  rcases Set.finite_or_infinite Y with hYfin | hYinf
  · have hZfin : Z.Finite :=
      hYfin.subset hZY
    rw [infiniteOrEmpty_of_finite hZfin,
        infiniteOrEmpty_of_finite hYfin]
  · have hYZ : Y ⊆ Z := by
      rw [infiniteOrEmpty_of_infinite hYinf] at hCY
      exact hCY
    have hZYeq : Z = Y :=
      le_antisymm hZY hYZ
    subst Z
    rfl

/-- Over `ℕ`, `infiniteOrEmpty` is **not** substitutable.

Take `x = 0`, `Y = ∅`, and `Z = {n | n ≠ 0}`. Then `0` is rejected from
`insert 0 ∅ = {0}` because that menu is finite, but it is chosen from
`insert 0 Z = Set.univ` because that menu is infinite. -/
theorem not_substitutable_infiniteOrEmpty :
    ¬ (infiniteOrEmpty ℕ).Substitutable := by
  classical
  intro hsub

  let Z : Set ℕ := {n | n ≠ 0}

  have hsmallFin : (insert 0 (∅ : Set ℕ)).Finite :=
    Set.finite_empty.insert 0

  have h0small :
      0 ∉ infiniteOrEmpty ℕ (insert 0 (∅ : Set ℕ)) := by
    rw [infiniteOrEmpty_of_finite hsmallFin]
    simp

  have hZuniv : insert 0 Z = Set.univ := by
    ext n
    by_cases hn : n = 0 <;> simp [Z, hn]

  have hunivInf : (Set.univ : Set ℕ).Infinite :=
    Set.infinite_univ

  have h0large :
      0 ∈ infiniteOrEmpty ℕ (insert 0 Z) := by
    rw [hZuniv]
    rw [infiniteOrEmpty_of_infinite hunivInf]
    simp

  have h0rejected :
      0 ∉ infiniteOrEmpty ℕ (insert 0 Z) :=
    hsub
      (x := 0)
      (Y := (∅ : Set ℕ))
      (Z := Z)
      (Set.empty_subset Z)
      h0small

  exact h0rejected h0large

/-- Packaging the separation: the single-new-alternative form together with
consistency does **not** imply substitutability in general. -/
theorem exists_forall_insert_insert_consistent_not_substitutable :
    ∃ C : ChoiceFunction ℕ,
      (∀ ⦃x z : ℕ⦄ ⦃Y : Set ℕ⦄,
        x ∉ C (insert x Y) → x ∉ C (insert x (insert z Y))) ∧
      C.Consistent ∧ ¬ C.Substitutable :=
  ⟨infiniteOrEmpty ℕ,
    forall_insert_insert_infiniteOrEmpty ℕ,
    consistent_infiniteOrEmpty ℕ,
    not_substitutable_infiniteOrEmpty⟩

/-! ### Why aggregate demand is restricted to finite menus -/

/-- The choice function accepting every available alternative. -/
def acceptAll (α : Type*) : ChoiceFunction α where
  toFun Y := Y
  choose_subset _ := fun _ hx => hx

/-- Accepting all alternatives satisfies aggregate demand on finite menus,
even when the universe of alternatives is infinite. -/
theorem sizeMonotone_acceptAll (α : Type*) :
    (acceptAll α).SizeMonotone := by
  intro Y Z hZ hYZ
  exact Set.ncard_le_ncard hYZ hZ

/-- Applying natural cardinality to arbitrary menus gives the wrong
infinite-universe condition: even accepting everything would fail it.
The singleton menu has cardinality `1`; `Set.univ : Set ℕ` has `ncard = 0`.
This is a regression witness for the finite-menu definition of
`ChoiceFunction.SizeMonotone`. -/
theorem not_monotone_ncard_acceptAll :
    ¬ Monotone (fun Y : Set ℕ => (acceptAll ℕ Y).ncard) := by
  intro h
  have hle := h (show ({0} : Set ℕ) ⊆ Set.univ from Set.subset_univ _)
  change ({0} : Set ℕ).ncard ≤ (Set.univ : Set ℕ).ncard at hle
  have hinfinite : (Set.univ : Set ℕ).Infinite := Set.infinite_univ
  simp [hinfinite.ncard] at hle

end Counterexamples

end ChoiceFunction
