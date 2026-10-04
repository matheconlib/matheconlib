/-
Matching with contracts: counterparty-relative choice conditions.
-/
import MatchingTheory.Choice.Basic
import MatchingTheory.Choice.Induced

/-!
# Weak substitutability and completions

These choice conditions depend on a counterparty map, but not on a market.
`Contracts/WeakSubstitutes.lean` supplies the buyer/seller instantiation.

`UnilaterallySubstitutable` and `BilaterallySubstitutable` use the
single-new-contract formulations of Hatfield–Kojima, *Substitutes and
Stability for Matching with Contracts* (2010). The unilateral restriction
is on the rejected contract; the bilateral restriction is on both contracts.
No assumption that their counterparties are distinct is added.

The predicates make sense on arbitrary types. Their finite-market
interpretation in the cited literature is not an assertion that the
single-contract formulation implies arbitrary-superset monotonicity on
infinite types.

`IsCompletionOf` is the choice-function definition in Hatfield–Kominers,
*Hidden Substitutes*, §3 (author manuscript, May 16, 2016, pp. 8–11).
For compatibility, `C.IsCompletionOf counterparty D` means that **D** is
a completion of **C**. Completion and substitutable completability do not
include IRC. `HasConsistentSubstitutableCompletion` states the stronger
existence hypothesis explicitly.

A completion need not enlarge the original choices pointwise. The results
`IsCompletionOf.unilaterallySubstitutable_of_le` and the hull
characterization in
`Choice/UnilateralSubstitutabilityImpliesSubstitutableCompletability.lean`
therefore state the extra pointwise inclusion separately.
-/

namespace ChoiceFunction

variable {A : Type*} {X : Type*}

section Defs

variable (counterparty : X → A) (C : ChoiceFunction X)

/-- No contract in `Y` shares its counterparty with `x` — the literature's
`d(x) ∉ d(Y)` (Hatfield–Kojima 2010, `d` the doctor map; sellers, in the
survey's dictionary). -/
def Fresh (x : X) (Y : Set X) : Prop :=
  ∀ y ∈ Y, counterparty y ≠ counterparty x

/-- **Unilateral substitutability** (Hatfield–Kojima 2010): the
substitutability implication is required only when the *rejected* contract's
counterparty has no other contract on the menu. -/
def UnilaterallySubstitutable : Prop :=
  ∀ ⦃x z : X⦄ ⦃Y : Set X⦄, Fresh counterparty x Y →
    x ∉ C (insert x Y) → x ∉ C (insert x (insert z Y))

/-- **Bilateral substitutability** (Hatfield–Kojima 2010): the implication is
required only when *both* the rejected contract's and the newly available
contract's counterparties have no contract on the menu. -/
def BilaterallySubstitutable : Prop :=
  ∀ ⦃x z : X⦄ ⦃Y : Set X⦄,
    Fresh counterparty x Y → Fresh counterparty z Y →
      x ∉ C (insert x Y) → x ∉ C (insert x (insert z Y))

/-- `C'` is a **completion** of `C`: on every menu it either agrees with `C`
or chooses at least two contracts with a common counterparty
(Hatfield–Kominers, *Hidden Substitutes*, §3). -/
def IsCompletionOf (C' : ChoiceFunction X) : Prop :=
  ∀ Y, C' Y = C Y ∨
    ∃ x ∈ C' Y, ∃ x' ∈ C' Y, x ≠ x' ∧ counterparty x = counterparty x'

/-- **Substitutable completability**: some completion is substitutable.
This condition alone does not assert IRC of that completion; existence
reductions use `HasConsistentSubstitutableCompletion` below. -/
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

/-- Freshness is absence from the image of the counterparty map. -/
theorem fresh_iff_not_mem_image {counterparty : X → A} {x : X} {Y : Set X} :
    Fresh counterparty x Y ↔ counterparty x ∉ counterparty '' Y := by
  constructor
  · intro h ⟨y, hy, heq⟩
    exact h y hy heq
  · intro h y hy heq
    exact h ⟨y, hy, heq⟩

/-- Freshness is preserved by restricting the menu. -/
theorem Fresh.mono {counterparty : X → A} {x : X} {Y Z : Set X}
    (hfresh : Fresh counterparty x Z) (hYZ : Y ⊆ Z) :
    Fresh counterparty x Y :=
  fun y hy => hfresh y (hYZ hy)

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

/-- Substitutability implies unilateral substitutability, for any
counterparty map: discard the side condition and apply the
single-new-contract form. -/
theorem Substitutable.unilaterallySubstitutable {C : ChoiceFunction X}
    (hC : C.Substitutable) (counterparty : X → A) :
    C.UnilaterallySubstitutable counterparty :=
  fun _x _z _Y _hfresh hx => hC.not_mem_insert_insert hx

/-- Unilateral substitutability implies bilateral substitutability:
strengthen the hypotheses. -/
theorem UnilaterallySubstitutable.bilaterallySubstitutable
    {counterparty : X → A} {C : ChoiceFunction X}
    (hC : C.UnilaterallySubstitutable counterparty) :
    C.BilaterallySubstitutable counterparty :=
  fun _x _z _Y hfx _hfz hx => hC hfx hx

/-! ## Identity completions for singleton preferences -/

/-- Singleton-or-empty preferences admit the identity completion,
for every counterparty map. -/
theorem hasConsistentSubstitutableCompletion_ofLinearOrder
    [Finite X]
    (counterparty : X → A)
    (pref : LinearOrder (Option X)) :
    ChoiceFunction.HasConsistentSubstitutableCompletion
      counterparty (ofLinearOrder pref) := by
  refine ⟨ofLinearOrder pref, ?_, ?_, ?_⟩
  · exact isCompletionOf_refl counterparty (ofLinearOrder pref)
  · exact substitutable_ofLinearOrder pref
  · exact consistent_ofLinearOrder pref

/-- The singleton restriction of set preferences admits the identity
completion, for every counterparty map. -/
theorem hasConsistentSubstitutableCompletion_ofSingletonSetLinearOrder
    [Finite X]
    (counterparty : X → A)
    (pref : LinearOrder (Set X)) :
    ChoiceFunction.HasConsistentSubstitutableCompletion
      counterparty (ofSingletonSetLinearOrder pref) := by
  refine ⟨ofSingletonSetLinearOrder pref, ?_, ?_, ?_⟩
  · exact isCompletionOf_refl counterparty
      (ofSingletonSetLinearOrder pref)
  · exact substitutable_ofSingletonSetLinearOrder pref
  · exact consistent_ofSingletonSetLinearOrder pref

end ChoiceFunction
