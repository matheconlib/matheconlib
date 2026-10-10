/-
Matching with contracts: completion need not enlarge choices.
-/
import MathEconLib.Choice.WeakSubstitutes
import MathEconLib.Choice.SubstituteHull
import MathEconLibTest.Choice.Counterexamples
import Mathlib.Tactic.Tauto

/-!
# A completion outside the pointwise-enlargement characterization

This file formalizes the buyer's three-contract choice rule from
Hatfield–Kominers, *The theory of matching with contracts* (2025),
Example 6.1, p. 469, and its completion on pp. 471–472
(DOI 10.1016/bs.hesmat.2025.10.005). Here `a`, `b`, `c` correspond to
the survey's `x′`, `x`, `y`. The survey's full market also includes another
buyer and the contract `ŷ`. The choice rule separates ordinary substitutable
completability from the stronger requirement that the completion contain
every original choice.

The original choice ranks the acceptable bundles
`{a, c} > {b} > {c} > {a} > ∅`. The completion prepends `{a, b}`.
Contracts `a` and `b` have the same counterparty; `c` has another.
Both rules satisfy IRC, and the completion is substitutable. Nevertheless,
the original rule is not unilaterally substitutable, and the completion
drops `c` from the full menu. Thus the pointwise-enlargement hypothesis in
the characterization cannot be omitted, even on a finite contract type.

The explicit membership formulas keep the example independent of a
numerical ranking representation or a general preference constructor.
-/

namespace MathEconLib.Choice

namespace ChoiceFunction.Counterexamples.Completion

/-- The contracts in the finite example. -/
inductive Contract where
  | a
  | b
  | c
  deriving DecidableEq

open Contract

instance : Fintype Contract where
  elems := {a, b, c}
  complete x := by cases x <;> simp

/-- `a` and `b` have the same counterparty; `c` has another. -/
def counterparty : Contract → Bool
  | a => false
  | b => false
  | c => true

/-- Choice from the acceptable-bundle ranking
`{a, c} > {b} > {c} > {a} > ∅`. -/
def original : ChoiceFunction Contract where
  toFun Y := {x | match x with
    | a => a ∈ Y ∧ (c ∈ Y ∨ b ∉ Y)
    | b => b ∈ Y ∧ ¬ (a ∈ Y ∧ c ∈ Y)
    | c => c ∈ Y ∧ (a ∈ Y ∨ b ∉ Y)}
  choose_subset Y x hx := by cases x <;> exact hx.1

/-- Choice after prepending `{a, b}` to the acceptable-bundle ranking. -/
def completed : ChoiceFunction Contract where
  toFun Y := {x | match x with
    | a => a ∈ Y
    | b => b ∈ Y
    | c => c ∈ Y ∧ b ∉ Y}
  choose_subset Y x hx := by
    cases x with
    | a => exact hx
    | b => exact hx
    | c => exact hx.1

@[simp] theorem mem_original_a {Y : Set Contract} :
    a ∈ original Y ↔ a ∈ Y ∧ (c ∈ Y ∨ b ∉ Y) := Iff.rfl

@[simp] theorem mem_original_b {Y : Set Contract} :
    b ∈ original Y ↔ b ∈ Y ∧ ¬ (a ∈ Y ∧ c ∈ Y) := Iff.rfl

@[simp] theorem mem_original_c {Y : Set Contract} :
    c ∈ original Y ↔ c ∈ Y ∧ (a ∈ Y ∨ b ∉ Y) := Iff.rfl

@[simp] theorem mem_completed_a {Y : Set Contract} :
    a ∈ completed Y ↔ a ∈ Y := Iff.rfl

@[simp] theorem mem_completed_b {Y : Set Contract} :
    b ∈ completed Y ↔ b ∈ Y := Iff.rfl

@[simp] theorem mem_completed_c {Y : Set Contract} :
    c ∈ completed Y ↔ c ∈ Y ∧ b ∉ Y := Iff.rfl

/-- The original choice has at most one contract per counterparty. -/
theorem original_feasible (Y : Set Contract) :
    Set.InjOn counterparty (original Y) := by
  intro x hx y hy hxy
  cases x <;> cases y <;> simp_all [counterparty]

/-- The original choice satisfies IRC. -/
theorem original_consistent : original.Consistent := by
  intro Y Z hCY hZY
  have ha := @hCY a
  have hb := @hCY b
  have hc := @hCY c
  have hza := @hZY a
  have hzb := @hZY b
  have hzc := @hZY c
  simp only [mem_original_a, mem_original_b, mem_original_c] at ha hb hc
  clear hCY hZY
  ext x
  cases x <;> simp only [mem_original_a, mem_original_b, mem_original_c] <;> tauto

/-- The completed choice satisfies IRC. -/
theorem completed_consistent : completed.Consistent := by
  intro Y Z hCY hZY
  have ha := @hCY a
  have hb := @hCY b
  have hc := @hCY c
  have hza := @hZY a
  have hzb := @hZY b
  have hzc := @hZY c
  simp only [mem_completed_a, mem_completed_b, mem_completed_c] at ha hb hc
  clear hCY hZY
  ext x
  cases x <;> simp only [mem_completed_a, mem_completed_b, mem_completed_c] <;> tauto

/-- The second choice rule is a completion in the ordinary sense. -/
theorem isCompletionOf : original.IsCompletionOf counterparty completed := by
  intro Y
  by_cases ha : a ∈ Y
  · by_cases hb : b ∈ Y
    · right
      exact ⟨a, by simpa using ha, b, by simpa using hb, by decide, rfl⟩
    · left
      ext x
      cases x <;> simp [ha, hb]
  · left
    ext x
    cases x <;> simp [ha]

/-- The completed rule is substitutable. -/
theorem completed_substitutable : completed.Substitutable := by
  apply substitutable_iff_chernoff.mpr
  intro Y Z hYZ x hx
  rcases hx with ⟨hxZ, hxY⟩
  cases x with
  | a => simpa using hxY
  | b => simpa using hxY
  | c =>
      simp only [mem_completed_c] at hxZ ⊢
      exact ⟨hxY, fun hbY => hxZ.2 (hYZ hbY)⟩

/-- The original rule has a substitutable completion satisfying IRC. -/
theorem original_hasConsistentSubstitutableCompletion :
    original.HasConsistentSubstitutableCompletion counterparty :=
  ⟨completed, isCompletionOf, completed_substitutable, completed_consistent⟩

/-- Adding `a` rescues the rejected contract `c`, although `c` is the
only contract with its counterparty on the smaller menu `{b, c}`. -/
theorem original_not_unilaterallySubstitutable :
    ¬ original.UnilaterallySubstitutable counterparty := by
  intro hUS
  have hfresh : Fresh counterparty c ({b} : Set Contract) := by
    intro y hy
    have hyb : y = b := Set.mem_singleton_iff.mp hy
    subst y
    decide
  have hreject : c ∉ original (insert c ({b} : Set Contract)) := by simp
  have hchosen : c ∈ original (insert c (insert a ({b} : Set Contract))) := by simp
  exact hUS (z := a) hfresh hreject hchosen

/-- This ordinary completion is not a pointwise enlargement. -/
theorem completed_not_enlargement :
    ¬ original ≤ completed := by
  intro h
  have hc := h Set.univ (show c ∈ original Set.univ by simp)
  simp at hc

/-- The substitute hull is not a completion of this rule: it rescues `c`
on the feasible menu `{b, c}`, where the original choice rejects `c`. -/
theorem substituteHull_not_isCompletionOf :
    ¬ original.IsCompletionOf counterparty original.substituteHull := by
  intro hcomp
  have hmenu : Set.InjOn counterparty ({b, c} : Set Contract) := by
    intro x hx y hy hxy
    cases x <;> cases y <;> simp_all [counterparty]
  have hc : c ∈ original.substituteHull ({b, c} : Set Contract) := by
    exact ⟨by simp, Set.univ, Set.subset_univ _, by simp⟩
  rw [hcomp.eq_of_injOn_menu hmenu] at hc
  simp at hc

end ChoiceFunction.Counterexamples.Completion

namespace ChoiceFunction.Counterexamples

/-! ## The role of finite-valuedness on infinite contract types -/

/-- With distinct counterparties for all contracts, the infinite-or-empty
rule is feasible on every menu. -/
theorem infiniteOrEmpty_feasible (Y : Set ℕ) :
    Set.InjOn id (infiniteOrEmpty ℕ Y) := by
  intro x _ y _ hxy
  exact hxy

/-- The single-addition definition of unilateral substitutability also
holds for the infinite-or-empty rule. -/
theorem infiniteOrEmpty_unilaterallySubstitutable :
    (infiniteOrEmpty ℕ).UnilaterallySubstitutable id := by
  intro x z Y _hx hx
  exact forall_insert_insert_infiniteOrEmpty ℕ hx

/-- The infinite menu witnesses failure of finite-valuedness. -/
theorem infiniteOrEmpty_not_finiteValued :
    ¬ (infiniteOrEmpty ℕ).FiniteValued := by
  intro hfinite
  have h := hfinite Set.univ
  rw [infiniteOrEmpty_of_infinite Set.infinite_univ] at h
  exact Set.infinite_univ h

/-- On the injective counterparty map `id`, every completion must be the
original rule. Thus this feasible, IRC, unilaterally substitutable rule
has no substitutable completion. Finite-valuedness cannot simply be
removed from the stronger completion theorem. -/
theorem infiniteOrEmpty_not_substitutablyCompletable :
    ¬ (infiniteOrEmpty ℕ).SubstitutablyCompletable id := by
  rintro ⟨D, hcomp, hsub⟩
  have hD : D = infiniteOrEmpty ℕ := by
    apply ChoiceFunction.ext
    intro Y
    apply hcomp.eq_of_injOn
    intro x _ y _ hxy
    exact hxy
  rw [hD] at hsub
  exact not_substitutable_infiniteOrEmpty hsub

end ChoiceFunction.Counterexamples

end MathEconLib.Choice
