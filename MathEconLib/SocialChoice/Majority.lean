/-
Copyright (c) 2026 Ritik Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ritik Jain
-/
module

public import MathEconLib.SocialChoice.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# Majority rule

Properties of simple majority rule, the relation `majority P` on the alternatives, and the
Condorcet paradox: majority rule need not be transitive, so it is not a social welfare function.

## Main statements

* `majority_reindexAgents`, `majority_comap`, `majority_congr`: majority rule is anonymous, neutral
  and independent of irrelevant alternatives.
* `not_majority_of_forall_lt`, `not_majority_of_risesAgainst`: majority rule is Pareto and
  positively responsive.
* `exists_mem_linearProfiles_majority_cycle`: **the Condorcet paradox**.
* `exists_mem_linearProfiles_not_isTrans_majority`: majority rule need not be transitive.

## References

* M. J. Osborne, A. Rubinstein, *Models in Microeconomic Theory* (2023), Sections 1.2 and 20.1
* K. O. May, *A set of independent necessary and sufficient conditions for simple majority
  decision*, Econometrica **20** (1952), 680–684
-/

@[expose] public section

namespace MathEconLib.SocialChoice

open MathEconLib.Preferences

universe u v w

variable {N : Type u} {X : Type v} [Fintype N] {P Q : Profile N fun _ => X} {x y : X}

/-- A majority strictly prefers `x` to `y`: more agents strictly prefer `x` to `y` than `y` to
`x`. -/
@[simp] theorem not_majority_iff :
    ¬ majority P x y ↔ (supporters P y x).card < (supporters P x y).card := by
  rw [majority_apply, not_le]

@[simp]
theorem majority_self (P : Profile N fun _ => X) (x : X) : majority P x x :=
  le_rfl

theorem majority_total (P : Profile N fun _ => X) (x y : X) : majority P x y ∨ majority P y x :=
  le_total _ _

/-- Majority rule is anonymous: permuting the agents does not change it. -/
theorem majority_reindexAgents (σ : N ≃ N) (P : Profile N fun _ => X) (x y : X) :
    majority (P.reindexAgents σ) x y ↔ majority P x y := by
  rw [majority_apply, majority_apply, card_supporters_reindexAgents,
    card_supporters_reindexAgents]

/-- Majority rule is neutral: relabelling the alternatives relabels it. -/
theorem majority_comap {Y : Type w} (f : Y → X) (P : Profile N fun _ => X) (x y : Y) :
    majority (P.comap fun _ => f) x y ↔ majority P (f x) (f y) := by
  rw [majority_apply, majority_apply, supporters_comap, supporters_comap]

/-- Majority rule is independent of irrelevant alternatives. -/
theorem majority_congr
    (h : ∀ i, (y ≼[P i] x ↔ y ≼[Q i] x) ∧ (x ≼[P i] y ↔ x ≼[Q i] y)) :
    majority P y x ↔ majority Q y x := by
  have hxy : supporters P x y = supporters Q x y := by
    ext i
    simp only [mem_supporters]
    exact and_congr (h i).1 (not_congr (h i).2)
  have hyx : supporters P y x = supporters Q y x := by
    ext i
    simp only [mem_supporters]
    exact and_congr (h i).2 (not_congr (h i).1)
  rw [majority_apply, majority_apply, hxy, hyx]

/-- Majority rule is Pareto when there is at least one agent. -/
theorem not_majority_of_forall_lt [Nonempty N] (h : ∀ i, y ≺[P i] x) : ¬ majority P x y := by
  have h₁ : supporters P x y = Finset.univ :=
    Finset.eq_univ_of_forall fun i => mem_supporters.2 (h i)
  have h₂ : supporters P y x = ∅ :=
    Finset.eq_empty_of_forall_notMem fun i hi => (P i).lt_asymm (h i) (mem_supporters.1 hi)
  rw [not_majority_iff, h₁, h₂, Finset.card_empty, Finset.card_univ]
  exact Fintype.card_pos

/-- Majority rule is positively responsive. -/
theorem not_majority_of_risesAgainst (h : RisesAgainst P Q x y) (hP : majority P y x) :
    ¬ majority Q x y := by
  obtain ⟨h₁, h₂, i, hi⟩ := h
  rw [majority_apply] at hP
  rw [not_majority_iff]
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

/-- **The Condorcet paradox**: some linear profile of three agents has a majority cycle, in which
a majority strictly prefers `a` to `b`, `b` to `c`, and `c` to `a`. -/
theorem exists_mem_linearProfiles_majority_cycle {a b c : X} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : ∃ P ∈ linearProfiles (Fin 3) X,
      ¬ majority P a b ∧ ¬ majority P b c ∧ ¬ majority P c a := by
  classical
  let r : Fin 3 → X → ℕ := fun i z =>
    if z = a then ![2, 0, 1] i else if z = b then ![1, 2, 0] i else if z = c then ![0, 1, 2] i
    else 0
  obtain ⟨P, hP, hr⟩ := exists_mem_linearProfiles_lt_of_lt r
  have key : ∀ {x y : X} (S : Finset (Fin 3)), x ≠ y → S.card = 2 →
      (∀ i ∈ S, r i y < r i x) → (∀ i ∉ S, r i x < r i y) → ¬ majority P x y := by
    intro x y S hxy hS h₁ h₂
    have hs : supporters P x y = S :=
      supporters_eq_of_forall (fun i hi => hr i x y (h₁ i hi)) (fun i hi => hr i y x (h₂ i hi))
    have hsum := card_supporters_add_card_supporters hP hxy
    rw [hs, hS, Fintype.card_fin] at hsum
    rw [not_majority_iff, hs, hS]
    omega
  have ha : ∀ i, r i a = ![2, 0, 1] i := fun i => by simp [r]
  have hb : ∀ i, r i b = ![1, 2, 0] i := fun i => by simp [r, hab.symm]
  have hc : ∀ i, r i c = ![0, 1, 2] i := fun i => by simp [r, hac.symm, hbc.symm]
  refine ⟨P, hP, key {0, 2} hab rfl ?_ ?_, key {0, 1} hbc rfl ?_ ?_, key {1, 2} hac.symm rfl ?_ ?_⟩
  all_goals
    simp only [ha, hb, hc]
    decide

/-- With three alternatives, majority rule need not be transitive. -/
theorem exists_mem_linearProfiles_not_isTrans_majority {a b c : X} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ P ∈ linearProfiles (Fin 3) X, ¬ IsTrans X (majority P) := by
  obtain ⟨P, hP, h₁, h₂, h₃⟩ := exists_mem_linearProfiles_majority_cycle hab hac hbc
  exact ⟨P, hP, fun ht => h₁ (IsTrans.trans (self := ht) a c b
    ((majority_total P c a).resolve_left h₃) ((majority_total P b c).resolve_left h₂))⟩

end MathEconLib.SocialChoice

section Examples

open MathEconLib.Preferences MathEconLib.SocialChoice

example : ∃ P ∈ linearProfiles (Fin 3) (Fin 3), ¬ IsTrans (Fin 3) (majority P) :=
  exists_mem_linearProfiles_not_isTrans_majority (a := 0) (b := 1) (c := 2)
    (by decide) (by decide) (by decide)

/-- With no agents every pair ties, so `not_majority_of_forall_lt` needs an agent. -/
example (P : Profile Empty fun _ => Bool) : majority P true false ∧ majority P false true := by
  have h : ∀ s : Finset Empty, s.card = 0 := fun s => by simp [Finset.eq_empty_of_isEmpty s]
  simp [majority_apply, h]

end Examples
