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
The cumulative offer process retains the possibility of recalling rejected contracts
and does not assume substitutability, IRC, or feasibility of held contract sets. Seller
preferences are fixed complete weak preferences over own contracts and the outside option.
Only (strictly) acceptable contracts may be proposed [this is WLOG].

Admissibility is relational: every weakly best remaining acceptable contract is allowed.
A proposal batch contains at most one proposal per seller, all evaluated before the round.
Policies, including fixed tie-breaking, specialize these runs in the policy module.

Histories are lists of proposed-contract batches in reverse chronological order.
Their accumulated offers and held contract sets are derived data. The raw terminal output
is a set of contracts, without a feasibility requirement.

## Terminology

We retain the market API's `seller` and `buyer` names: sellers propose contracts and buyers
hold contracts chosen from their accumulated offers. These roles correspond to doctors and
hospitals in Hatfield–Milgrom and Hatfield–Kojima, and workers and firms in the labor-market
formulation of Hatfield–Kominers–Westkamp.

- `offers h` is the cumulative set of contracts proposed during history `h`, including
  contracts subsequently rejected.
- `heldContracts A` is the set currently chosen by buyers from those accumulated offers.
  Holding a contract is provisional; it is not a final acceptance or a feasible matching.
- `NoHeldContract A s` says that no buyer currently holds a contract involving seller `s`.
- `remaining A s` consists of seller `s`'s unoffered strictly acceptable contracts.
- `Admissible A x` permits a weakly best remaining contract of a seller with no held contract.

A policy is this library's proposal-selection rule. Histories and batches support the
generalization to history-dependent scheduling and simultaneous proposals; they do not
assert equivalence with a particular paper's cumulative offer process. On a finite contract set, a cumulative offer process with fixed preferences and
a valid policy produces a terminal set of held contracts. A mechanism mapping reported preference
profiles to outcomes is a separate construction.

## References

John William Hatfield and Fuhito Kojima (2010), *Substitutes and Stability for Matching
with Contracts*, Journal of Economic Theory 145(5), 1704–1723, §2.3.
https://doi.org/10.1016/j.jet.2010.01.007.
This module generalizes the sequential cumulative offer process to accommodate weak preferences and
batched proposals. Source correspondence, stability, and incentive theorems are separate work
under #139.

Hatfield and Milgrom (2005), *Matching with Contracts*, American Economic Review 95(4),
913–935, §§II–III. https://doi.org/10.1257/0002828054825466.
Their cumulative offers include past offers, from which hospitals hold chosen contracts.

Hatfield, Kominers, and Westkamp, *Stability, Strategy-Proofness, and Cumulative Offer
Mechanisms*, July 30, 2015 working-paper version, §§2.3 and 3 (published in Review of Economic
Studies 88(3), 2021, 1457–1502, https://doi.org/10.1093/restud/rdaa052).
The proposal condition refers to a proposer having no contract currently held.
-/

@[expose] public section

namespace MathEconLib.Matching.CumulativeOffer

open MathEconLib.Choice MathEconLib.Preferences

/-- The data of a unit-demand cumulative offer process. Each buyer chooses a subset of its
accumulated offers. Restricting each buyer's menu to its own contracts ensures that it can
hold only contracts involving that buyer. -/
structure CumulativeOfferProcess (B S X : Type*) where
  /-- The buyer to whom this contract is proposed. -/
  buyer : X → B
  /-- The seller who proposes this contract. -/
  seller : X → S
  /-- Buyer choice from accumulated offers, without substitutability or IRC assumptions. -/
  choiceB : B → ChoiceFunction X
  /-- Fixed weak preferences over own contracts and nonparticipation. -/
  pref : ∀ s, CompletePreference (Option {x : X // seller x = s})

variable {B S X : Type*}

/-- Use an existing market's incidence and buyer choices. The supplied preferences determine
proposals; the market's seller choice functions are not used by this raw cumulative offer process. -/
def ofMarket (M : Market B S X)
    (pref : ∀ s, CompletePreference (Option {x : X // M.seller x = s})) :
    CumulativeOfferProcess B S X :=
  ⟨M.buyer, M.seller, M.choiceB, pref⟩

namespace CumulativeOfferProcess

variable (P : CumulativeOfferProcess B S X)

/-- A proposing seller's own contracts. -/
abbrev Own (s : S) := {x : X // P.seller x = s}

/-- The weak preference restricted to contracts. -/
def contractPreference (s : S) : CompletePreference (P.Own s) :=
  (P.pref s).comap some

/-- Contracts currently held by buyers: each buyer chooses from all contracts proposed to it.
Previously rejected contracts remain in this menu; rejection need not be permanent. -/
def heldContracts (A : Set X) : Set X :=
  {x | ∃ b, x ∈ P.choiceB b {y ∈ A | P.buyer y = b}}

/-- Held contracts always belong to the accumulated offers. -/
theorem heldContracts_subset (A : Set X) : P.heldContracts A ⊆ A := by
  rintro x ⟨b, hx⟩
  exact ((P.choiceB b).choose_subset _ hx).1

/-- Under market locality, own-menu and global-menu held contracts agree. -/
theorem heldContracts_ofMarket (M : Market B S X)
    (pref : ∀ s, CompletePreference (Option {x : X // M.seller x = s}))
    (hlocal : M.Local) (A : Set X) :
    (ofMarket M pref).heldContracts A = {x | ∃ b, x ∈ M.choiceB b A} := by
  ext x
  change (∃ b, x ∈ M.choiceB b (M.buyerSide b A)) ↔ _
  simp only [hlocal.1, Set.mem_ofPred_eq]

/-- No contract involving this seller is currently held by any buyer. -/
def NoHeldContract (A : Set X) (s : S) : Prop :=
  ∀ x ∈ P.heldContracts A, P.seller x ≠ s

/-- Unoffered own contracts strictly preferred to nonparticipation. -/
def remaining (A : Set X) (s : S) : Set (P.Own s) :=
  {x | x.val ∉ A ∧ (P.pref s).lt none (some x)}

/-- A seller is eligible to propose if no contract involving it is currently held and it has
an unoffered strictly acceptable contract. Eligibility does not assert attainment of a best offer. -/
def Eligible (A : Set X) (s : S) : Prop :=
  P.NoHeldContract A s ∧ (P.remaining A s).Nonempty

/-- All weakly best remaining acceptable offers of an proposer with no held contract. -/
def Admissible (A : Set X) (x : X) : Prop :=
  ∃ (s : S) (y : P.Own s), y.val = x ∧ P.NoHeldContract A s ∧
    y ∈ maximizers (P.contractPreference s) (P.remaining A s)

/-- An admissible proposal is fresh. -/
theorem Admissible.not_mem {A : Set X} {x : X} (h : P.Admissible A x) : x ∉ A := by
  rcases h with ⟨s, y, rfl, _, hy⟩
  exact hy.1.1

/-- The seller proposing an admissible contract is eligible. -/
theorem Admissible.eligible {A : Set X} {x : X} (h : P.Admissible A x) :
    P.Eligible A (P.seller x) := by
  rcases h with ⟨s, y, rfl, hu, hy⟩
  rw [y.property]
  exact ⟨hu, y, hy.1⟩

/-- Economic exhaustion: every proposer with no held contract has no remaining acceptable contract.
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
  ∃ h, P.Run h ∧ P.Terminal (offers h) ∧ Z = P.heldContracts (offers h)

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

end CumulativeOfferProcess
end MathEconLib.Matching.CumulativeOffer
