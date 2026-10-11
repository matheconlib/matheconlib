import MathEconLib.Choice.Matching.Completion
import MathEconLib.Choice.Matching.WeakSubstitutability
import MathEconLib.Choice.SubstituteHull

/-!
# Relationships between matching choice conditions

The definitions of weak substitutability are in
`MathEconLib.Choice.Matching.WeakSubstitutability`; completion and
substitutable completability are in
`MathEconLib.Choice.Matching.Completion`.
This module relates those conditions to the general substitute hull. The
partner map is arbitrary; no matching market is required.

A feasible, finite-valued IRC choice function is unilaterally substitutable
if and only if its substitute hull is a completion. Equivalently, the hull
preserves the set of represented partners, or there exists a substitutable
completion which enlarges the original choices pointwise. The hull is then
the least such completion and is path independent.

The alternative and partner types may both be infinite: only the chosen
sets must be finite. The converse from an enlarging substitutable
completion requires no finiteness assumption. The finite-alternative
existence theorems are retained as corollaries.

Zhang (2016), Proposition 2, p. 233, proves the finite-domain implication
to bare substitutable completability for feasible IRC choice. The
contraction lemma below extends his one-addition Lemma 2 on the same page.
The final paragraphs of §§5 and 6, p. 233, leave IRC of the completion
unestablished. Here the generic substitute-hull results supply IRC as well.
Kadam (2017) proves the preference-based implication by constructing a
preference completion; no completed linear preference order is constructed
here. Corollaries for preference-induced choices are in
`MathEconLib.Choice.Matching.Preferences`.

The general hull construction and its minimality and IRC properties live
in `MathEconLib.Choice.SubstituteHull`. Completion alone is not pointwise
enlargement, so the characterization states that extra condition explicitly.

## References

* Jun Zhang (2016), *On sufficient conditions for the existence of stable
  matchings with contracts*, Economics Letters 145, 230–234,
  https://doi.org/10.1016/j.econlet.2016.06.029.
* Sangram Vilasrao Kadam (2017), *Unilateral substitutability implies
  substitutable completability in many-to-one matching with contracts*,
  Games and Economic Behavior 102, 56–68,
  https://doi.org/10.1016/j.geb.2016.10.002.
-/

namespace MathEconLib.Choice

namespace ChoiceFunction

variable {A : Type*} {X : Type*}

/-! ## Enlarging completions imply unilateral substitutability -/

/-- For feasible IRC choice, a substitutable completion which enlarges
choices implies unilateral substitutability. No finiteness assumption is
needed in this direction; arbitrary completions need not satisfy the
pointwise inclusion hypothesis. -/
theorem IsCompletionOf.unilaterallySubstitutable_of_le
    {counterparty : X → A} {C D : ChoiceFunction X}
    (hcomp : C.IsCompletionOf counterparty D)
    (hD : D.Substitutable) (hCD : C ≤ D) (hIRC : C.Consistent)
    (hfeasible : ∀ Y, Set.InjOn counterparty (C Y)) :
    C.UnilaterallySubstitutable counterparty := by
  intro x z Y hfresh hxnot hxlarge
  have hsmall : insert x Y ⊆ insert x (insert z Y) := by
    intro y hy
    rcases hy with hxy | hyY
    · exact Or.inl hxy
    · exact Or.inr (Or.inr hyY)
  obtain ⟨y, hy, hsame⟩ :=
    hcomp.exists_chosen_counterparty_of_le hD hCD hIRC
      (hfeasible (insert x Y)) hsmall (Set.mem_insert x Y) hxlarge
  rcases C.choose_subset (insert x Y) hy with hxy | hyY
  · rw [hxy] at hy
    exact hxnot hy
  · exact hfresh y hyY hsame

/-! ## Iterating unilateral substitutability over finitely many additions -/

/-- Rejection persists after finitely many additions when the rejected
contract's counterparty is absent from the base menus. The initial menu
need not be finite. -/
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
      have hnot := hUS (z := z) hf' (ih hf')
      simpa only [Set.union_insert] using hnot

/-! ## Recalled alternatives have represented partners -/

/-- If `x` is available at `Y` and chosen from a larger menu `Z`, then its
counterparty is represented in `C Y`, provided **the choice `C Z`** is
finite and feasible. Neither menu needs to be finite.

This extends Zhang (2016), Lemma 2, p. 233, from a one-addition comparison to
arbitrary nested menus. It does not assert that `x` itself is chosen at `Y`.
-/
theorem UnilaterallySubstitutable.exists_chosen_counterparty_of_finite_choice
    {counterparty : X → A} {C : ChoiceFunction X}
    (hUS : C.UnilaterallySubstitutable counterparty)
    (hIRC : C.Consistent)
    {Y Z : Set X} {x : X}
    (hCZ : (C Z).Finite)
    (hfeasible : Set.InjOn counterparty (C Z))
    (hYZ : Y ⊆ Z) (hxY : x ∈ Y) (hxZ : x ∈ C Z) :
    ∃ y ∈ C Y, counterparty y = counterparty x := by
  classical
  by_contra hnone
  -- Remove x's counterparty from Y; IRC preserves choice on insert x Y0.
  let Y0 : Set X := {y | y ∈ Y ∧ counterparty y ≠ counterparty x}
  let E : Set X := {y | y ∈ C Z ∧ y ≠ x}
  have hE : E.Finite := hCZ.subset (fun _ hy => hy.1)
  have hbase : C (insert x Y0) = C Y := by
    apply hIRC
    · intro y hy
      refine Or.inr ⟨C.choose_subset Y hy, ?_⟩
      intro heq
      exact hnone ⟨y, hy, heq⟩
    · exact Set.insert_subset hxY (fun _ hy => hy.1)
  have hxbase : x ∉ C (insert x Y0) := by
    rw [hbase]
    intro hx
    exact hnone ⟨x, hx, rfl⟩
  have hfresh : Fresh counterparty x (Y0 ∪ E) := by
    intro y hy
    rcases hy with hy | hy
    · exact hy.2
    · intro heq
      exact hy.2 (hfeasible hy.1 hxZ heq)
  -- This reduced menu contains C Z, so IRC recovers the larger menu's choice.
  have hupper : C (insert x (Y0 ∪ E)) = C Z := by
    apply hIRC
    · intro y hy
      by_cases hyx : y = x
      · exact Or.inl hyx
      · exact Or.inr (Or.inr ⟨hy, hyx⟩)
    · apply Set.insert_subset (C.choose_subset Z hxZ)
      intro y hy
      rcases hy with hy | hy
      · exact hYZ hy.1
      · exact C.choose_subset Z hy.1
  have hnot := reject_union_of_finite hUS hE hxbase hfresh
  rw [hupper] at hnot
  exact hnot hxZ

/-- The substitute hull preserves precisely the represented counterparties.
Finite-valuedness replaces finiteness of the entire contract type. -/
theorem UnilaterallySubstitutable.image_substituteHull_eq
    {counterparty : X → A} {C : ChoiceFunction X}
    (hUS : C.UnilaterallySubstitutable counterparty)
    (hIRC : C.Consistent)
    (hfeasible : ∀ Y, Set.InjOn counterparty (C Y))
    (hfinite : C.FiniteValued) (Y : Set X) :
    counterparty '' C.substituteHull Y = counterparty '' C Y := by
  ext a
  constructor
  · rintro ⟨x, hxH, rfl⟩
    rcases hxH with ⟨hxY, Z, hYZ, hxZ⟩
    obtain ⟨y, hy, hsame⟩ :=
      hUS.exists_chosen_counterparty_of_finite_choice hIRC
        (hfinite Z) (hfeasible Z) hYZ hxY hxZ
    exact ⟨y, hy, hsame⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, le_substituteHull C Y hx, rfl⟩

/-- For feasible, finite-valued IRC choice, unilateral substitutability
makes the substitute hull a completion. The hull is already substitutable,
and its IRC follows separately from that of the original choice. -/
theorem UnilaterallySubstitutable.substituteHull_isCompletionOf
    {counterparty : X → A} {C : ChoiceFunction X}
    (hUS : C.UnilaterallySubstitutable counterparty)
    (hIRC : C.Consistent)
    (hfeasible : ∀ Y, Set.InjOn counterparty (C Y))
    (hfinite : C.FiniteValued) :
    C.IsCompletionOf counterparty C.substituteHull := by
  apply isCompletionOf_of_le_of_image_subset (le_substituteHull C)
  intro Y
  exact (hUS.image_substituteHull_eq hIRC hfeasible hfinite Y).subset

/-! ## Characterization by enlarging completions -/

/-- If the hull introduces no new counterparties, the original choice is
unilaterally substitutable. This direction requires neither finiteness,
feasibility, nor IRC. -/
theorem unilaterallySubstitutable_of_image_substituteHull_subset
    {counterparty : X → A} {C : ChoiceFunction X}
    (himage : ∀ Y, counterparty '' C.substituteHull Y ⊆ counterparty '' C Y) :
    C.UnilaterallySubstitutable counterparty := by
  intro x z Y hfresh hxnot hxlarge
  have hsmall : insert x Y ⊆ insert x (insert z Y) := by
    intro y hy
    rcases hy with hxy | hyY
    · exact Or.inl hxy
    · exact Or.inr (Or.inr hyY)
  have hxH : x ∈ C.substituteHull (insert x Y) :=
    ⟨Set.mem_insert x Y, insert x (insert z Y), hsmall, hxlarge⟩
  obtain ⟨y, hy, hsame⟩ := himage (insert x Y) ⟨x, hxH, rfl⟩
  rcases C.choose_subset (insert x Y) hy with hxy | hyY
  · rw [hxy] at hy
    exact hxnot hy
  · exact hfresh y hyY hsame

/-- For feasible finite-valued IRC choice, unilateral substitutability is
exactly preservation of counterparty images by the substitute hull. -/
theorem unilaterallySubstitutable_iff_image_substituteHull_eq
    {counterparty : X → A} {C : ChoiceFunction X}
    (hIRC : C.Consistent)
    (hfeasible : ∀ Y, Set.InjOn counterparty (C Y))
    (hfinite : C.FiniteValued) :
    C.UnilaterallySubstitutable counterparty ↔
      ∀ Y, counterparty '' C.substituteHull Y = counterparty '' C Y := by
  constructor
  · intro hUS
    exact hUS.image_substituteHull_eq hIRC hfeasible hfinite
  · intro himage
    exact unilaterallySubstitutable_of_image_substituteHull_subset
      (fun Y => (himage Y).subset)

/-- For feasible finite-valued IRC choice, unilateral substitutability is
exactly the assertion that the canonical hull is a completion. -/
theorem unilaterallySubstitutable_iff_substituteHull_isCompletionOf
    {counterparty : X → A} {C : ChoiceFunction X}
    (hIRC : C.Consistent)
    (hfeasible : ∀ Y, Set.InjOn counterparty (C Y))
    (hfinite : C.FiniteValued) :
    C.UnilaterallySubstitutable counterparty ↔
      C.IsCompletionOf counterparty C.substituteHull := by
  constructor
  · intro hUS
    exact hUS.substituteHull_isCompletionOf hIRC hfeasible hfinite
  · intro hcomp
    exact hcomp.unilaterallySubstitutable_of_le
      (substituteHull_substitutable C) (le_substituteHull C) hIRC hfeasible

/-- For feasible finite-valued IRC choice, unilateral substitutability is
exactly the existence of a substitutable completion which enlarges choices
pointwise. The pointwise inclusion is essential. -/
theorem unilaterallySubstitutable_iff_exists_substitutable_enlarging_completion
    {counterparty : X → A} {C : ChoiceFunction X}
    (hIRC : C.Consistent)
    (hfeasible : ∀ Y, Set.InjOn counterparty (C Y))
    (hfinite : C.FiniteValued) :
    C.UnilaterallySubstitutable counterparty ↔
      ∃ D : ChoiceFunction X,
        C.IsCompletionOf counterparty D ∧ D.Substitutable ∧ C ≤ D := by
  constructor
  · intro hUS
    exact ⟨C.substituteHull,
      hUS.substituteHull_isCompletionOf hIRC hfeasible hfinite,
      substituteHull_substitutable C, le_substituteHull C⟩
  · rintro ⟨D, hcomp, hD, hCD⟩
    exact hcomp.unilaterallySubstitutable_of_le hD hCD hIRC hfeasible

/-- The hull is the least substitutable completion among pointwise
extensions of a feasible, finite-valued, unilaterally substitutable IRC
choice function. This does not assert leastness among arbitrary completions. -/
theorem UnilaterallySubstitutable.isLeast_substitutable_enlarging_completion
    {counterparty : X → A} {C : ChoiceFunction X}
    (hUS : C.UnilaterallySubstitutable counterparty)
    (hIRC : C.Consistent)
    (hfeasible : ∀ Y, Set.InjOn counterparty (C Y))
    (hfinite : C.FiniteValued) :
    IsLeast {D : ChoiceFunction X |
      C.IsCompletionOf counterparty D ∧ D.Substitutable ∧ C ≤ D}
      C.substituteHull := by
  refine ⟨⟨hUS.substituteHull_isCompletionOf hIRC hfeasible hfinite,
    substituteHull_substitutable C, le_substituteHull C⟩, ?_⟩
  intro D hD
  exact substituteHull_le hD.2.1 hD.2.2

/-! ## Existence, with finite chosen sets -/

/-- Finite-valued unilateral substitutability, IRC, and feasibility imply
existence of a completion satisfying both substitutability and IRC. The
contract type and counterparty type need not be finite. -/
theorem UnilaterallySubstitutable.hasConsistentSubstitutableCompletion_of_finiteValued
    {counterparty : X → A} {C : ChoiceFunction X}
    (hUS : C.UnilaterallySubstitutable counterparty)
    (hIRC : C.Consistent)
    (hfeasible : ∀ Y, Set.InjOn counterparty (C Y))
    (hfinite : C.FiniteValued) :
    C.HasConsistentSubstitutableCompletion counterparty :=
  ⟨C.substituteHull,
    hUS.substituteHull_isCompletionOf hIRC hfeasible hfinite,
    substituteHull_substitutable C, substituteHull_consistent hIRC⟩

/-- Forgetting IRC gives the weaker completability predicate. -/
theorem UnilaterallySubstitutable.substitutablyCompletable_of_finiteValued
    {counterparty : X → A} {C : ChoiceFunction X}
    (hUS : C.UnilaterallySubstitutable counterparty)
    (hIRC : C.Consistent)
    (hfeasible : ∀ Y, Set.InjOn counterparty (C Y))
    (hfinite : C.FiniteValued) :
    C.SubstitutablyCompletable counterparty :=
  (hUS.hasConsistentSubstitutableCompletion_of_finiteValued
    hIRC hfeasible hfinite).substitutablyCompletable

/-- The finite-contract corollary of the finite-valued completion theorem.
Zhang (2016), Proposition 2, p. 233, gives bare substitutable completability;
the hull IRC theorem proved here additionally supplies a consistent completion. -/
theorem UnilaterallySubstitutable.hasConsistentSubstitutableCompletion
    [Finite X]
    {counterparty : X → A} {C : ChoiceFunction X}
    (hUS : C.UnilaterallySubstitutable counterparty)
    (hIRC : C.Consistent)
    (hfeasible : ∀ Y, Set.InjOn counterparty (C Y)) :
    C.HasConsistentSubstitutableCompletion counterparty :=
  hUS.hasConsistentSubstitutableCompletion_of_finiteValued
    hIRC hfeasible (finiteValued_of_finite C)

/-- Forgetting IRC gives the weaker completability predicate. -/
theorem UnilaterallySubstitutable.substitutablyCompletable
    [Finite X]
    {counterparty : X → A} {C : ChoiceFunction X}
    (hUS : C.UnilaterallySubstitutable counterparty)
    (hIRC : C.Consistent)
    (hfeasible : ∀ Y, Set.InjOn counterparty (C Y)) :
    C.SubstitutablyCompletable counterparty :=
  hUS.substitutablyCompletable_of_finiteValued
    hIRC hfeasible (finiteValued_of_finite C)

/-! ## Compatibility names

The hull is now a general choice-theoretic construction. These names keep
existing uses of the original completion namespace valid.
-/

namespace UnilateralSubstitutabilityImpliesSubstitutableCompletability

/-- Compatibility abbreviation for the general substitute hull. -/
abbrev hull (C : ChoiceFunction X) : ChoiceFunction X := C.substituteHull

@[simp] theorem mem_hull (C : ChoiceFunction X) {Y : Set X} {x : X} :
    x ∈ hull C Y ↔ x ∈ Y ∧ ∃ Z, Y ⊆ Z ∧ x ∈ C Z :=
  Iff.rfl

/-- Compatibility name for pointwise enlargement by the hull. -/
theorem subset_hull (C : ChoiceFunction X) (Y : Set X) :
    C Y ⊆ hull C Y :=
  le_substituteHull C Y

/-- Compatibility name for substitutability of the hull. -/
theorem hull_substitutable (C : ChoiceFunction X) :
    (hull C).Substitutable :=
  substituteHull_substitutable C

/-- Compatibility name for IRC preservation by the hull. -/
theorem hull_consistent {C : ChoiceFunction X} (hIRC : C.Consistent) :
    (hull C).Consistent :=
  substituteHull_consistent hIRC

/-- The original finite-menu contraction statement, derived from the
stronger theorem requiring only a finite choice from the upper menu. -/
theorem exists_chosen_counterparty
    {counterparty : X → A} {C : ChoiceFunction X}
    (hUS : C.UnilaterallySubstitutable counterparty)
    (hIRC : C.Consistent)
    {Y Z : Set X} {x : X}
    (hZ : Z.Finite)
    (hfeasible : Set.InjOn counterparty (C Z))
    (hYZ : Y ⊆ Z) (hxY : x ∈ Y) (hxZ : x ∈ C Z) :
    ∃ y ∈ C Y, counterparty y = counterparty x :=
  hUS.exists_chosen_counterparty_of_finite_choice hIRC
    (hZ.subset (C.choose_subset Z)) hfeasible hYZ hxY hxZ

/-- Compatibility name for the finite-contract hull completion theorem. -/
theorem hull_isCompletionOf [Finite X]
    {counterparty : X → A} {C : ChoiceFunction X}
    (hUS : C.UnilaterallySubstitutable counterparty)
    (hIRC : C.Consistent)
    (hfeasible : ∀ Y, Set.InjOn counterparty (C Y)) :
    C.IsCompletionOf counterparty (hull C) :=
  hUS.substituteHull_isCompletionOf hIRC hfeasible (finiteValued_of_finite C)

end UnilateralSubstitutabilityImpliesSubstitutableCompletability

end ChoiceFunction

end MathEconLib.Choice
