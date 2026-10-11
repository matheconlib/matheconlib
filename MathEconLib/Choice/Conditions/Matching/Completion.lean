import MathEconLib.Choice.Conditions.Matching.IrrelevanceOfRejectedContracts
import MathEconLib.Choice.Conditions.Matching.Substitutability

/-!
# Completion and substitutable completability

These conditions use a map assigning each alternative to a matching partner,
without requiring a market or specified market sides. The binder `counterparty`
denotes this map. This module contains the definitions of completion and both
bare and consistent substitutable completability, together with their
elementary properties.

`IsCompletionOf` uses the completion formula in Hatfield–Kominers,
*The theory of matching with contracts* (2025), §6.1, the unnumbered
definition immediately before Definition 6.1, p. 471; Definition 6.1
on that page defines substitutable completability
(DOI 10.1016/bs.hesmat.2025.10.005). The formula is exposed here on
arbitrary choice functions; the survey applies it to many-to-one original
choice and assumes IRC throughout (p. 413).
For compatibility, `C.IsCompletionOf counterparty D` means that **D** is
a completion of **C**. Completion and substitutable completability do not
include IRC as Lean predicates. `HasConsistentSubstitutableCompletion`
states the stronger existence hypothesis explicitly, accounting for the
survey's standing IRC convention.

A completion need not enlarge the original choices pointwise. The result
`IsCompletionOf.unilaterallySubstitutable_of_le` and the hull
characterization in
`MathEconLib.Choice.Conditions.Matching.Relationships`
therefore state the extra pointwise inclusion separately. Consequences for
preference-induced choice are in
`MathEconLib.Choice.Conditions.Matching.Preferences`.
-/

namespace MathEconLib.Choice

namespace ChoiceFunction

variable {A : Type*} {X : Type*}

section Defs

variable (counterparty : X → A) (C : ChoiceFunction X)

/-- `C'` is a **completion** of `C`: on every menu it either agrees with `C`
or chooses at least two contracts with a common counterparty
(Hatfield–Kominers 2025, §6.1, unnumbered definition before Definition 6.1,
p. 471). This formula does not include the survey's standing IRC assumption. -/
def IsCompletionOf (C' : ChoiceFunction X) : Prop :=
  ∀ Y, C' Y = C Y ∨
    ∃ x ∈ C' Y, ∃ x' ∈ C' Y, x ≠ x' ∧ counterparty x = counterparty x'

/-- **Substitutable completability**: some completion is substitutable
(Hatfield–Kominers 2025, Definition 6.1, p. 471).
This Lean predicate does not assert IRC of that completion; the survey
assumes IRC throughout (p. 413). Existence reductions use
`HasConsistentSubstitutableCompletion` below. -/
def SubstitutablyCompletable : Prop :=
  ∃ C' : ChoiceFunction X, C.IsCompletionOf counterparty C' ∧ C'.Substitutable

/-- A completion satisfying both substitutability and IRC.
The existential witnesses must be the same choice function: separate
existence of a substitutable completion and a consistent completion is
not the hypothesis needed for stable-outcome existence. -/
def HasConsistentSubstitutableCompletion : Prop :=
  ∃ C' : ChoiceFunction X,
    C.IsCompletionOf counterparty C' ∧ C'.Substitutable ∧ C'.Consistent

end Defs

/-- Every choice function is a completion of itself. -/
theorem isCompletionOf_refl (counterparty : X → A) (C : ChoiceFunction X) :
    C.IsCompletionOf counterparty C :=
  fun _ => Or.inl rfl

/-- Completing a completion gives a completion of the original choice function. -/
theorem IsCompletionOf.trans {counterparty : X → A}
    {C D E : ChoiceFunction X}
    (hCD : C.IsCompletionOf counterparty D)
    (hDE : D.IsCompletionOf counterparty E) :
    C.IsCompletionOf counterparty E := by
  intro Y
  rcases hDE Y with hED | hE
  · rw [hED]
    exact hCD Y
  · exact Or.inr hE

/-- A completion must agree with the original choice function whenever its
chosen set has at most one contract per counterparty. -/
theorem IsCompletionOf.eq_of_injOn {counterparty : X → A}
    {C D : ChoiceFunction X} (hCD : C.IsCompletionOf counterparty D)
    {Y : Set X} (hY : Set.InjOn counterparty (D Y)) :
    D Y = C Y := by
  rcases hCD Y with h | ⟨x, hx, x', hx', hne, heq⟩
  · exact h
  · exact (hne (hY hx hx' heq)).elim

/-- In particular, a completion agrees with the original choice function on every
many-to-one-feasible menu. -/
theorem IsCompletionOf.eq_of_injOn_menu {counterparty : X → A}
    {C D : ChoiceFunction X} (hCD : C.IsCompletionOf counterparty D)
    {Y : Set X} (hY : Set.InjOn counterparty Y) :
    D Y = C Y := by
  apply hCD.eq_of_injOn
  intro x hx x' hx' heq
  exact hY (D.choose_subset Y hx) (D.choose_subset Y hx') heq

/-- A completion agrees on singleton menus, independently of the
counterparty map. -/
theorem IsCompletionOf.apply_singleton {counterparty : X → A}
    {C D : ChoiceFunction X} (hCD : C.IsCompletionOf counterparty D) (x : X) :
    D {x} = C {x} := by
  apply hCD.eq_of_injOn_menu
  intro y hy z hz _
  exact (Set.mem_singleton_iff.mp hy).trans (Set.mem_singleton_iff.mp hz).symm

/-- An enlargement which introduces no new represented counterparties is
a completion. Neither feasibility nor IRC is needed for this implication. -/
theorem isCompletionOf_of_le_of_image_subset {counterparty : X → A}
    {C D : ChoiceFunction X} (hCD : C ≤ D)
    (himage : ∀ Y, counterparty '' D Y ⊆ counterparty '' C Y) :
    C.IsCompletionOf counterparty D := by
  classical
  intro Y
  by_cases hDC : D Y ⊆ C Y
  · exact Or.inl (Set.Subset.antisymm hDC (hCD Y))
  · right
    have hex : ∃ x ∈ D Y, x ∉ C Y := by
      by_contra hnone
      apply hDC
      intro x hx
      by_contra hxnot
      exact hnone ⟨x, hx, hxnot⟩
    obtain ⟨x, hxD, hxC⟩ := hex
    obtain ⟨y, hyC, hsame⟩ := himage Y ⟨x, hxD, rfl⟩
    refine ⟨x, hxD, y, hCD Y hyC, ?_, hsame.symm⟩
    intro hxy
    apply hxC
    rw [hxy]
    exact hyC

/-- A substitutable completion which enlarges choices preserves the
counterparty of every retained, previously chosen contract under contraction.

Only the choice from the smaller menu needs to be feasible. The contract
type and the chosen sets may be infinite. -/
theorem IsCompletionOf.exists_chosen_counterparty_of_le
    {counterparty : X → A} {C D : ChoiceFunction X}
    (hcomp : C.IsCompletionOf counterparty D)
    (hD : D.Substitutable) (hCD : C ≤ D) (hIRC : C.Consistent)
    {Y Z : Set X} {x : X}
    (hfeasible : Set.InjOn counterparty (C Y))
    (hYZ : Y ⊆ Z) (hxY : x ∈ Y) (hxZ : x ∈ C Z) :
    ∃ y ∈ C Y, counterparty y = counterparty x := by
  classical
  by_contra hnone
  have hVY : insert x (C Y) ⊆ Y :=
    Set.insert_subset hxY (C.choose_subset Y)
  have hV : Set.InjOn counterparty (insert x (C Y)) := by
    intro y hy z hz heq
    rcases hy with rfl | hy
    · rcases hz with rfl | hz
      · rfl
      · exact (hnone ⟨z, hz, heq.symm⟩).elim
    · rcases hz with rfl | hz
      · exact (hnone ⟨y, hy, heq⟩).elim
      · exact hfeasible hy hz heq
  have hCV : C (insert x (C Y)) = C Y :=
    hIRC (fun _ hy => Set.mem_insert_of_mem x hy) hVY
  have hxDV : x ∈ D (insert x (C Y)) :=
    (substitutable_iff_chernoff.mp hD)
      (fun _ hy => hYZ (hVY hy))
      ⟨hCD Z hxZ, Set.mem_insert x (C Y)⟩
  rw [hcomp.eq_of_injOn_menu hV, hCV] at hxDV
  exact hnone ⟨x, hxDV, rfl⟩

/-- Substitutable completions preserve support. A contract chosen by the
completion is chosen from its singleton menu by substitutability, and on
that menu the completion agrees with the original choice.

This is the support lemma needed to assemble individual completions into
a `Market`; it does not assume that completions already satisfy support. -/
theorem IsCompletionOf.preserves_support {counterparty : X → A}
    {C D : ChoiceFunction X} (hCD : C.IsCompletionOf counterparty D)
    (hD : D.Substitutable) {P : Set X} (hC : ∀ Y, C Y ⊆ P) :
    ∀ Y, D Y ⊆ P := by
  intro Y x hx
  have hsmall : ({x} : Set X) ⊆ Y := by
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact D.choose_subset Y hx
  have hxsmall : x ∈ D ({x} : Set X) :=
    (substitutable_iff_chernoff.mp hD) hsmall ⟨hx, Set.mem_singleton x⟩
  rw [hCD.apply_singleton x] at hxsmall
  exact hC {x} hxsmall

/-- The identity completion witnesses completability of a substitutable
choice function. -/
theorem Substitutable.substitutablyCompletable {C : ChoiceFunction X}
    (hC : C.Substitutable) (counterparty : X → A) :
    C.SubstitutablyCompletable counterparty :=
  ⟨C, isCompletionOf_refl counterparty C, hC⟩

/-- Substitutability and IRC provide a completion with both properties. -/
theorem Substitutable.hasConsistentSubstitutableCompletion {C : ChoiceFunction X}
    (hC : C.Substitutable) (hIRC : C.Consistent) (counterparty : X → A) :
    C.HasConsistentSubstitutableCompletion counterparty :=
  ⟨C, isCompletionOf_refl counterparty C, hC, hIRC⟩

/-- We can forget IRC of the completion. -/
theorem HasConsistentSubstitutableCompletion.substitutablyCompletable
    {counterparty : X → A} {C : ChoiceFunction X}
    (hC : C.HasConsistentSubstitutableCompletion counterparty) :
    C.SubstitutablyCompletable counterparty := by
  obtain ⟨D, hcomp, hsub, _hIRC⟩ := hC
  exact ⟨D, hcomp, hsub⟩

end ChoiceFunction

end MathEconLib.Choice
