/-
Copyright (c) 2026 Ritik Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ritik Jain
-/
module

public import MathEconLib.SocialChoice.Basic
public import Mathlib.Tactic.FinCases

/-!
# Majority rule

Properties of simple majority, `majority`: `x ≿ y` when at least as many agents strictly prefer
`x` to `y` as strictly prefer `y` to `x`.

## Main statements

* `isComplete_majority`: the majority relation is complete at every profile, whatever the agents'
  relations.
* `isAnonymousOn_majority`, `isNeutralOn_majority`, `isIIAOn_majority`,
  `isPositivelyResponsiveOn_majority`: majority rule is anonymous, neutral, independent of
  irrelevant alternatives and positively responsive on every domain.
* `isParetoOn_majority`: it satisfies the Pareto property on every domain when there is at least
  one agent.
* `exists_mem_linearProfiles_majority_cycle`: **the Condorcet paradox**. For any three distinct
  alternatives `a`, `b`, `c` there is a linear profile of three agents whose majority relation has
  `a ≻ b`, `b ≻ c` and `c ≻ a`.
* `exists_mem_linearProfiles_not_isTransitive_majority`: hence the majority relation need not be
  transitive once there are three alternatives.

## Implementation notes

The Condorcet profile is built for any three distinct alternatives of an arbitrary type;
Osborne and Rubinstein's example (Sections 1.2 and 20.1) has `X = {a, b, c}`.

## References

Martin J. Osborne and Ariel Rubinstein (2023), *Models in Microeconomic Theory*, expanded second
edition, Open Book Publishers, Section 1.2 (majority rule, the Condorcet paradox) and Section 20.1.
[DOI: 10.11647/OBP.0361](https://doi.org/10.11647/OBP.0361).

Kenneth O. May (1952), *A set of independent necessary and sufficient conditions for simple
majority decision*, Econometrica **20**(4), 680–684.
[DOI: 10.2307/1907651](https://doi.org/10.2307/1907651).

## Tags

majority rule, Condorcet paradox, social welfare function
-/

@[expose] public section

namespace MathEconLib.SocialChoice

open MathEconLib.Preference

universe u v

variable {N : Type u} {X : Type v} [Fintype N] {D : Set (Profile N X)} {P Q : Profile N X}
  {x y : X}

/-- The strict part of the majority relation: strictly more agents prefer `x` to `y` than `y` to
`x`. -/
@[simp] theorem strictPart_majority_iff :
    StrictPart (majority P) x y ↔ (supporters P y x).card < (supporters P x y).card := by
  rw [MathEconLib.Preference.strictPart_iff, majority_apply, majority_apply, not_le]
  exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

@[simp]
theorem majority_self (P : Profile N X) (x : X) : majority P x x :=
  le_rfl

/-- The majority relation is complete, whatever the agents' relations. -/
theorem isComplete_majority (P : Profile N X) : IsComplete (majority P) :=
  isComplete_iff.2 fun _ _ => le_total _ _

/-- Majority rule is anonymous on every domain. -/
theorem isAnonymousOn_majority (D : Set (Profile N X)) : IsAnonymousOn (majority (X := X)) D :=
  fun σ P _ _ => funext₂ fun x y => propext <| by
    rw [majority_apply, majority_apply, card_supporters_permuteAgents,
      card_supporters_permuteAgents]

/-- Majority rule is neutral on every domain. -/
theorem isNeutralOn_majority (D : Set (Profile N X)) : IsNeutralOn (majority (X := X)) D :=
  fun τ P _ _ x y => by
    rw [majority_apply, majority_apply, supporters_relabel, supporters_relabel]

/-- Majority rule is independent of irrelevant alternatives on every domain. -/
theorem isIIAOn_majority (D : Set (Profile N X)) : IsIIAOn (majority (X := X)) D := by
  intro P _ Q _ x y h
  have hxy : supporters P x y = supporters Q x y := by
    ext i; simp only [mem_supporters, MathEconLib.Preference.strictPart_iff, (h i).1, (h i).2]
  have hyx : supporters P y x = supporters Q y x := by
    ext i; simp only [mem_supporters, MathEconLib.Preference.strictPart_iff, (h i).1, (h i).2]
  rw [majority_apply, majority_apply, hxy, hyx]

/-- Majority rule satisfies the Pareto property on every domain when there is at least one
agent. -/
theorem isParetoOn_majority [Nonempty N] (D : Set (Profile N X)) :
    IsParetoOn (majority (X := X)) D := by
  intro P _ x y h
  have h₁ : supporters P x y = Finset.univ :=
    Finset.eq_univ_of_forall fun i => mem_supporters.2 (h i)
  have h₂ : supporters P y x = ∅ :=
    Finset.eq_empty_of_forall_notMem fun i hi => (h i).asymm (mem_supporters.1 hi)
  rw [strictPart_majority_iff, h₁, h₂, Finset.card_empty, Finset.card_univ]
  exact Fintype.card_pos

/-- Majority rule is positively responsive on every domain. -/
theorem isPositivelyResponsiveOn_majority (D : Set (Profile N X)) :
    IsPositivelyResponsiveOn (majority (X := X)) D := by
  intro P _ Q _ x y ⟨h₁, h₂, i, hi⟩ hP
  rw [majority_apply] at hP
  rw [strictPart_majority_iff]
  have s₁ : supporters P x y ⊆ supporters Q x y := fun k hk =>
    mem_supporters.2 (h₁ k (mem_supporters.1 hk))
  have s₂ : supporters Q y x ⊆ supporters P y x := fun k hk =>
    mem_supporters.2 (h₂ k (mem_supporters.1 hk))
  rcases hi with ⟨hQ, hP'⟩ | ⟨hP', hQ⟩
  · have : (supporters P x y).card < (supporters Q x y).card :=
      Finset.card_lt_card ⟨s₁, fun hs => hP' (mem_supporters.1 (hs (mem_supporters.2 hQ)))⟩
    exact (Finset.card_le_card s₂).trans_lt (hP.trans_lt this)
  · have : (supporters Q y x).card < (supporters P y x).card :=
      Finset.card_lt_card ⟨s₂, fun hs => hQ (mem_supporters.1 (hs (mem_supporters.2 hP')))⟩
    exact this.trans_le (hP.trans (Finset.card_le_card s₁))

/-! ### The Condorcet paradox -/

/-- **The Condorcet paradox**: for any three distinct alternatives `a`, `b`, `c` there is a linear
profile of three agents (`a ≻₀ b ≻₀ c`, `b ≻₁ c ≻₁ a`, `c ≻₂ a ≻₂ b`) at which majority rule has
`a ≻ b`, `b ≻ c` and `c ≻ a`. -/
theorem exists_mem_linearProfiles_majority_cycle {a b c : X} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : ∃ P ∈ linearProfiles (Fin 3) X, StrictPart (majority P) a b ∧
      StrictPart (majority P) b c ∧ StrictPart (majority P) c a := by
  classical
  let r : Fin 3 → X → ℕ := fun i z =>
    if z = a then ![2, 0, 1] i else if z = b then ![1, 2, 0] i else if z = c then ![0, 1, 2] i
    else 0
  obtain ⟨P, hP, hr⟩ := exists_mem_linearProfiles_strictPart_of_lt r
  have key : ∀ {x y : X} (S : Finset (Fin 3)), x ≠ y → S.card = 2 →
      (∀ i ∈ S, r i y < r i x) → (∀ i ∉ S, r i x < r i y) → StrictPart (majority P) x y := by
    intro x y S hxy hS h₁ h₂
    have hs : supporters P x y = S :=
      supporters_eq_of_forall (fun i hi => hr i x y (h₁ i hi)) (fun i hi => hr i y x (h₂ i hi))
    have hsum := card_supporters_add_card_supporters hP hxy
    rw [hs, hS, Fintype.card_fin] at hsum
    rw [strictPart_majority_iff, hs, hS]
    omega
  have ha : ∀ i, r i a = ![2, 0, 1] i := fun i => by simp [r]
  have hb : ∀ i, r i b = ![1, 2, 0] i := fun i => by simp [r, hab.symm]
  have hc : ∀ i, r i c = ![0, 1, 2] i := fun i => by simp [r, hac.symm, hbc.symm]
  refine ⟨P, hP, key {0, 2} hab rfl ?_ ?_, key {0, 1} hbc rfl ?_ ?_, key {1, 2} hac.symm rfl ?_ ?_⟩
  all_goals
    simp only [ha, hb, hc]
    decide

/-- For any three distinct alternatives, the majority relation of some linear profile of three
agents is not transitive (so it is not a preference relation). -/
theorem exists_mem_linearProfiles_not_isTransitive_majority {a b c : X} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ P ∈ linearProfiles (Fin 3) X, ¬ IsTransitive (majority P) := by
  obtain ⟨P, hP, h₁, h₂, h₃⟩ := exists_mem_linearProfiles_majority_cycle hab hac hbc
  exact ⟨P, hP, fun ht => h₃.2 (ht.trans h₁.1 h₂.1)⟩

end MathEconLib.SocialChoice

/-! ### Worked examples -/

section Examples

open MathEconLib.Preference MathEconLib.SocialChoice

/-- The Condorcet paradox on `Fin 3`. -/
example : ∃ P ∈ linearProfiles (Fin 3) (Fin 3), ¬ IsTransitive (majority P) :=
  exists_mem_linearProfiles_not_isTransitive_majority (a := 0) (b := 1) (c := 2)
    (by decide) (by decide) (by decide)

/-- With no agents, every alternative ties with every other: majority rule is then not Pareto,
which is why `isParetoOn_majority` assumes an agent. -/
example (P : Profile Empty Bool) : majority P true false ∧ majority P false true := by
  have h : ∀ s : Finset Empty, s.card = 0 := fun s => by simp [Finset.eq_empty_of_isEmpty s]
  simp [majority_apply, h]

end Examples
