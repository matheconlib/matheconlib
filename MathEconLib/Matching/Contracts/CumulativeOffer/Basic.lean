/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
module

public import MathEconLib.Matching.Contracts.Basic
public import MathEconLib.Choice.Maximizers

/-!
# Cumulative offer processes

Unit-demand sellers propose to buyers choosing from their accumulated own-contract menus.
The process retains rejected contracts and does not assume substitutability, IRC, or
feasibility of holdings. Preferences are fixed complete weak preferences over own contracts
and the outside option. Only strictly acceptable contracts may be proposed.

Admissibility is relational: every weakly best remaining acceptable contract is allowed.
A productive batch contains at most one proposal per seller, all evaluated before the round.
Policies, including fixed tie-breaking, specialize these runs in the policy module.

Histories are lists of batches in reverse chronological order. Their accumulated offers and
holdings are derived data. The raw terminal output is a set, without a feasibility claim.

## References

John William Hatfield and Fuhito Kojima (2010), *Substitutes and Stability for Matching
with Contracts*, Journal of Economic Theory 145(5), 1704–1723, §2.3.
https://doi.org/10.1016/j.jet.2010.01.007.
This module generalizes the sequential process to weak preferences and batches. Source
correspondence, stability, and incentive theorems are separate work under #139.
-/

@[expose] public section

namespace MathEconLib.Matching.CumulativeOffer

open MathEconLib.Choice MathEconLib.Preferences

/-- The data of a unit-demand cumulative offer process. Receiving choices need only contract.
Own-menu evaluation supplies buyer support without a separate support field. -/
structure Process (B S X : Type*) where
  /-- Receiving endpoint. -/
  buyer : X → B
  /-- Proposing endpoint. -/
  seller : X → S
  /-- Receiving-side choice, with no economic regularity assumptions. -/
  choiceB : B → ChoiceFunction X
  /-- Fixed weak preferences over own contracts and nonparticipation. -/
  pref : ∀ s, CompletePreference (Option {x : X // seller x = s})

variable {B S X : Type*}

/-- Use an existing market's incidence and buyer choices. The supplied preferences determine
proposals; the market's seller choice functions are not used by this raw process. -/
def ofMarket (M : Market B S X)
    (pref : ∀ s, CompletePreference (Option {x : X // M.seller x = s})) :
    Process B S X :=
  ⟨M.buyer, M.seller, M.choiceB, pref⟩

namespace Process

variable (P : Process B S X)

/-- An agent's own contracts. -/
abbrev Own (s : S) := {x : X // P.seller x = s}

/-- The weak preference restricted to contracts. -/
def contractPreference (s : S) : CompletePreference (P.Own s) :=
  (P.pref s).comap some

/-- Buyer holdings, computed from accumulated offers on that buyer's own menu. -/
def holdings (A : Set X) : Set X :=
  {x | ∃ b, x ∈ P.choiceB b {y ∈ A | P.buyer y = b}}

/-- Holdings always belong to the accumulated offers. -/
theorem holdings_subset (A : Set X) : P.holdings A ⊆ A := by
  rintro x ⟨b, hx⟩
  exact ((P.choiceB b).choose_subset _ hx).1

/-- Under market locality, own-menu and global-menu holdings agree. -/
theorem holdings_ofMarket (M : Market B S X)
    (pref : ∀ s, CompletePreference (Option {x : X // M.seller x = s}))
    (hlocal : M.Local) (A : Set X) :
    (ofMarket M pref).holdings A = {x | ∃ b, x ∈ M.choiceB b A} := by
  ext x
  change (∃ b, x ∈ M.choiceB b (M.buyerSide b A)) ↔ _
  simp only [hlocal.1]

/-- No current holding involves this proposer. -/
def Unheld (A : Set X) (s : S) : Prop :=
  ∀ x ∈ P.holdings A, P.seller x ≠ s

/-- Unoffered own contracts strictly preferred to nonparticipation. -/
def remaining (A : Set X) (s : S) : Set (P.Own s) :=
  {x | x.val ∉ A ∧ (P.pref s).lt none (some x)}

/-- Eligibility records economic availability, not attainment of a best offer. -/
def Eligible (A : Set X) (s : S) : Prop :=
  P.Unheld A s ∧ (P.remaining A s).Nonempty

/-- All weakly best remaining acceptable offers of an unheld proposer. -/
def Admissible (A : Set X) (x : X) : Prop :=
  ∃ s (y : P.Own s), y.val = x ∧ P.Unheld A s ∧
    y ∈ maximizers (P.contractPreference s) (P.remaining A s)

/-- An admissible proposal is fresh. -/
theorem Admissible.not_mem {A : Set X} {x : X} (h : P.Admissible A x) : x ∉ A := by
  rcases h with ⟨s, y, rfl, _, hy⟩
  exact hy.1.1

/-- The owner of an admissible proposal is eligible. -/
theorem Admissible.eligible {A : Set X} {x : X} (h : P.Admissible A x) :
    P.Eligible A (P.seller x) := by
  rcases h with ⟨s, y, rfl, hu, hy⟩
  rw [y.property]
  exact ⟨hu, y, hy.1⟩

/-- Economic exhaustion: every unheld proposer has no remaining acceptable contract.
On infinite domains this differs from inability to find a greatest remaining contract. -/
def Terminal (A : Set X) : Prop := ∀ s, ¬ P.Eligible A s

/-- A productive batch uses one admissible contract per participating agent.
Every proposal is evaluated at the same pre-round state. -/
def ValidBatch (A Q : Set X) : Prop :=
  Q.Nonempty ∧ (∀ x ∈ Q, P.Admissible A x) ∧ Set.InjOn P.seller Q

/-- A singleton batch is valid exactly when its contract is admissible. -/
theorem validBatch_singleton_iff (A : Set X) (x : X) :
    P.ValidBatch A {x} ↔ P.Admissible A x := by
  constructor
  · intro h
    exact h.2.1 x (Set.mem_singleton x)
  · intro h
    refine ⟨Set.singleton_nonempty x, ?_, ?_⟩
    · intro y hy
      simpa only [Set.mem_singleton_iff.mp hy] using h
    · intro y hy z hz _
      exact (Set.mem_singleton_iff.mp hy).trans (Set.mem_singleton_iff.mp hz).symm

/-- A productive batch cannot occur at an exhausted state. -/
theorem ValidBatch.not_terminal {A Q : Set X} (h : P.ValidBatch A Q) :
    ¬ P.Terminal A := by
  obtain ⟨x, hx⟩ := h.1
  exact fun ht => ht (P.seller x) ((h.2.1 x hx).eligible P)

/-- New proposals are disjoint from all previous offers. -/
theorem ValidBatch.disjoint {A Q : Set X} (h : P.ValidBatch A Q) :
    Disjoint A Q := by
  rw [Set.disjoint_left]
  intro x hxA hxQ
  exact (h.2.1 x hxQ).not_mem P hxA

/-- Every productive round strictly enlarges the offer set. -/
theorem ValidBatch.ssubset {A Q : Set X} (h : P.ValidBatch A Q) : A ⊂ A ∪ Q := by
  refine ⟨Set.subset_union_left, ?_⟩
  intro hsub
  obtain ⟨x, hx⟩ := h.1
  exact (h.2.1 x hx).not_mem P (hsub (Or.inr hx))

/-- Accumulated offers of a reverse-chronological batch history. -/
def offers : List (Set X) → Set X
  | [] => ∅
  | Q :: h => offers h ∪ Q

@[simp] theorem offers_nil : offers ([] : List (Set X)) = ∅ := rfl

@[simp] theorem offers_cons (Q : Set X) (h : List (Set X)) :
    offers (Q :: h) = offers h ∪ Q := rfl

/-- A finite productive history, newest batch first. -/
inductive Run : List (Set X) → Prop
  | nil : Run []
  | cons {h Q} : Run h → P.ValidBatch (offers h) Q → Run (Q :: h)

/-- The terminal outcome relation does not select a schedule or assert feasibility. -/
def Outcome (Z : Set X) : Prop :=
  ∃ h, P.Run h ∧ P.Terminal (offers h) ∧ Z = P.holdings (offers h)

/-- Finite remaining menus supply an admissible contract for an eligible agent. -/
theorem Eligible.exists_admissible {A : Set X} {s : S} (h : P.Eligible A s)
    (hfin : (P.remaining A s).Finite) :
    ∃ x, P.Admissible A x ∧ P.seller x = s := by
  obtain ⟨y, hy⟩ := maximizers_nonempty_of_finite (P.contractPreference s) hfin h.2
  exact ⟨y.val, ⟨s, y, rfl, h.1, hy⟩, y.property⟩

/-- On finite contracts, every nonterminal state has a valid singleton step. -/
theorem exists_validBatch [Finite X] {A : Set X} (h : ¬ P.Terminal A) :
    ∃ Q, P.ValidBatch A Q := by
  classical
  obtain ⟨s, hs⟩ := not_forall.mp h
  have he : P.Eligible A s := not_not.mp hs
  obtain ⟨x, hx, _⟩ := he.exists_admissible P (Set.toFinite _)
  exact ⟨{x}, (P.validBatch_singleton_iff A x).2 hx⟩

end Process
end MathEconLib.Matching.CumulativeOffer
