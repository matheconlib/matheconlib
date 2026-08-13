/-
Matching with contracts: counterexamples for the choice layer.

DRAFT — design signatures; not compiled. See SPEC.md. In a mathlib
upstreaming these results would move to the `Counterexamples/` library.
-/
import MatchingTheory.Choice.Basic

/-!
# Choice-layer counterexamples

`infiniteOrEmpty` — take the whole menu when it is infinite, nothing
otherwise — separates the single-new-alternative form of substitutability
(survey Definition 2.1 as printed) from the superset-form definition on
infinite types, **even in the presence of consistency**. This settles the
strictness half of SPEC Q9 and justifies both design choices it protects:

* the superset quantification in `ChoiceFunction.Substitutable` (the printed
  single-contract form is too weak to drive the finiteness-free fixed-point
  development), and
* stating the §6 weakened conditions (`Matching.Contracts.WeakSubstitutes`)
  as finite-market notions in the literature's single-contract shape.

No finite counterexample exists — that is the content of
`ChoiceFunction.substitutable_iff_forall_insert_insert` — so this is
inherently an infinite-universe phenomenon.
-/

namespace ChoiceFunction

namespace Counterexamples

open scoped Classical in
/-- The choice function that takes the whole menu when it is infinite and
nothing otherwise. -/
noncomputable def infiniteOrEmpty (α : Type*) : ChoiceFunction α where
  toFun Y := if Y.Infinite then Y else ∅
  choose_subset' Y := by
    sorry

/-- `infiniteOrEmpty` satisfies the single-new-alternative form.

Paper proof. If `insert x Y` is infinite, everything on the menu is chosen,
so the hypothesis `x ∉ C (insert x Y)` is false and the claim is vacuous. If
`insert x Y` is finite, then so is `insert x (insert z Y)`, and nothing is
chosen from it. -/
theorem forall_insert_insert_infiniteOrEmpty (α : Type*) :
    ∀ ⦃x z : α⦄ ⦃Y : Set α⦄,
      x ∉ infiniteOrEmpty α (insert x Y) →
        x ∉ infiniteOrEmpty α (insert x (insert z Y)) := by
  sorry

/-- `infiniteOrEmpty` is consistent.

Paper proof. For `C Y ⊆ Z ⊆ Y`: if `Y` is infinite then `C Y = Y`, so the
sandwich forces `Z = Y`; if `Y` is finite then `Z` is finite too and both
choices are empty. -/
theorem consistent_infiniteOrEmpty (α : Type*) :
    (infiniteOrEmpty α).Consistent := by
  sorry

/-- Over `ℕ`, `infiniteOrEmpty` is **not** substitutable.

Paper proof. Take `x = 0`, `Y = ∅`, `Z = {n | n ≠ 0}`: then `0` is rejected
from `insert 0 ∅ = {0}` (finite ⇒ nothing chosen) but chosen from
`insert 0 Z = Set.univ` (infinite ⇒ everything chosen), violating the
superset form at `∅ ⊆ Z`. -/
theorem not_substitutable_infiniteOrEmpty :
    ¬ (infiniteOrEmpty ℕ).Substitutable := by
  sorry

/-- Packaging the separation: the single-new-alternative form together with
consistency does **not** imply substitutability in general. -/
theorem exists_forall_insert_insert_consistent_not_substitutable :
    ∃ C : ChoiceFunction ℕ,
      (∀ ⦃x z : ℕ⦄ ⦃Y : Set ℕ⦄,
        x ∉ C (insert x Y) → x ∉ C (insert x (insert z Y))) ∧
      C.Consistent ∧ ¬ C.Substitutable :=
  ⟨infiniteOrEmpty ℕ, forall_insert_insert_infiniteOrEmpty ℕ,
    consistent_infiniteOrEmpty ℕ, not_substitutable_infiniteOrEmpty⟩

end Counterexamples

end ChoiceFunction
