/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
module

public import MathEconLib.Matching.Contracts.CumulativeOffer.Basic

/-!
# Cumulative offer policies

Policies select batches from reverse-chronological histories. Validity is a separate proposition.
State policies lift by forgetting history beyond accumulated offers. Singleton and simultaneous
restrictions constrain participation; fixed tie-breaking additionally constrains contract selection.
The fixed-order constructor uses one contract order for both scheduling and tie-breaking.
Higher elements in that supplied order have priority. All constructors preserve strict preferences.
-/

@[expose] public section

namespace MathEconLib.Matching.CumulativeOffer.Process

open MathEconLib.Choice MathEconLib.Preferences

variable {B S X : Type*} (P : Process B S X)

/-- A deterministic history-dependent batch rule. -/
abbrev Policy (X : Type*) := List (Set X) → Set X

/-- Validity is required only along valid nonterminal histories. -/
def ValidPolicy (π : Policy X) : Prop :=
  ∀ h, P.Run h → ¬ P.Terminal (offers h) → P.ValidBatch (offers h) (π h)

/-- A state rule needs only accumulated offers. -/
abbrev StatePolicy (X : Type*) := Set X → Set X

/-- State-rule validity, before restriction to reachable histories. -/
def ValidStatePolicy (σ : StatePolicy X) : Prop :=
  ∀ A, ¬ P.Terminal A → P.ValidBatch A (σ A)

/-- Lift a state rule to histories without adding mutable state. -/
def liftStatePolicy (σ : StatePolicy X) : Policy X := fun h => σ (offers h)

/-- A valid state rule gives a valid history policy. -/
theorem ValidStatePolicy.lift {σ : StatePolicy X} (hσ : P.ValidStatePolicy σ) :
    P.ValidPolicy (liftStatePolicy σ) :=
  fun h _ ht => hσ (offers h) ht

/-- State rules give identical batches at histories with identical accumulated offers. -/
theorem liftStatePolicy_eq (σ : StatePolicy X) {h k : List (Set X)}
    (he : offers h = offers k) : liftStatePolicy σ h = liftStatePolicy σ k := by
  simp only [liftStatePolicy, he]

/-- Exactly one proposal at each nonterminal valid history. -/
def Sequential (π : Policy X) : Prop :=
  ∀ h, P.Run h → ¬ P.Terminal (offers h) → ∃ x, π h = {x}

/-- Every eligible proposer participates. Combined with validity, each proposes exactly once. -/
def Simultaneous (π : Policy X) : Prop :=
  ∀ h, P.Run h → ∀ s, P.Eligible (offers h) s →
    ∃ x ∈ π h, P.seller x = s

/-- Selected proposals have greatest priority among their owner's admissible proposals.
This fixes tie selection, not the scheduling of different owners. -/
def FixedTieBreaking (priority : LinearOrder X) (π : Policy X) : Prop :=
  ∀ h, P.Run h → ∀ x ∈ π h, ∀ y, P.Admissible (offers h) y →
    P.seller y = P.seller x → priority.le y x

/-- A run follows a policy when each newest batch is the policy's choice at its prior history. -/
def Follows (π : Policy X) : List (Set X) → Prop
  | [] => True
  | Q :: h => Follows π h ∧ Q = π h

/-- Follows for a lifted state policy exposes only the previous offer set. -/
theorem follows_lift_cons (σ : StatePolicy X) (Q : Set X) (h : List (Set X)) :
    Follows (liftStatePolicy σ) (Q :: h) ↔
      Follows (liftStatePolicy σ) h ∧ Q = σ (offers h) := Iff.rfl

/-- All currently admissible contracts of a specified proposer. -/
def agentOffers (A : Set X) (s : S) : Set X :=
  {x | P.Admissible A x ∧ P.seller x = s}

/-- Eligible agents have a nonempty admissible set when contracts are finite. -/
theorem agentOffers_nonempty [Finite X] {A : Set X} {s : S}
    (h : P.Eligible A s) : (P.agentOffers A s).Nonempty :=
  h.exists_admissible P (Set.toFinite _)

/-- Highest-priority admissible offer of an eligible agent on a finite contract type. -/
noncomputable def selectOffer [Finite X] (priority : LinearOrder X)
    (A : Set X) (s : S) (h : P.Eligible A s) : X :=
  (maximizers_nonempty_of_finite (CompletePreference.ofLinearOrder priority)
    (Set.toFinite (P.agentOffers A s)) (P.agentOffers_nonempty h)).choose

/-- The selection is admissible, belongs to its owner, and has greatest admissible priority. -/
theorem selectOffer_spec [Finite X] (priority : LinearOrder X)
    (A : Set X) (s : S) (h : P.Eligible A s) :
    P.Admissible A (P.selectOffer priority A s h) ∧
      P.seller (P.selectOffer priority A s h) = s ∧
      ∀ y, P.Admissible A y → P.seller y = s →
        priority.le y (P.selectOffer priority A s h) := by
  have hm := (maximizers_nonempty_of_finite (CompletePreference.ofLinearOrder priority)
    (Set.toFinite (P.agentOffers A s)) (P.agentOffers_nonempty h)).choose_spec
  exact ⟨hm.1.1, hm.1.2, fun y hy hs => hm.2 ⟨hy, hs⟩⟩

/-- A subset of eligible agents submits one fixed-priority proposal each. -/
noncomputable def selectedBatch [Finite X] (priority : LinearOrder X)
    (A : Set X) (T : Set S) : Set X :=
  {x | ∃ s ∈ T, ∃ h : P.Eligible A s, P.selectOffer priority A s h = x}

/-- Agent-subset selection realizes the relational batch definition. -/
theorem selectedBatch_valid [Finite X] (priority : LinearOrder X)
    {A : Set X} {T : Set S} (hne : T.Nonempty)
    (hel : ∀ s ∈ T, P.Eligible A s) :
    P.ValidBatch A (P.selectedBatch priority A T) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨s, hs⟩ := hne
    exact ⟨P.selectOffer priority A s (hel s hs), s, hs, hel s hs, rfl⟩
  · rintro x ⟨s, _, h, rfl⟩
    exact (P.selectOffer_spec priority A s h).1
  · rintro x ⟨s, _, hs, rfl⟩ y ⟨t, _, ht, rfl⟩ he
    have hs' := (P.selectOffer_spec priority A s hs).2.1
    have ht' := (P.selectOffer_spec priority A t ht).2.1
    have hst : s = t := hs'.symm.trans (he.trans ht')
    subst t
    rfl

/-- Every eligible agent proposes with fixed contract tie-breaking. -/
noncomputable def simultaneous [Finite X] (priority : LinearOrder X) : StatePolicy X :=
  fun A => P.selectedBatch priority A {s | P.Eligible A s}

/-- The simultaneous constructor is valid on finite contracts. -/
theorem simultaneous_valid [Finite X] (priority : LinearOrder X) :
    P.ValidStatePolicy (P.simultaneous priority) := by
  intro A h
  classical
  obtain ⟨s, hs⟩ := not_forall.mp h
  exact P.selectedBatch_valid priority ⟨s, not_not.mp hs⟩ (fun _ hs => hs)

/-- The constructor really includes every eligible agent. -/
theorem simultaneous_all [Finite X] (priority : LinearOrder X) :
    P.Simultaneous (liftStatePolicy (P.simultaneous priority)) := by
  intro h _ s hs
  refine ⟨P.selectOffer priority (offers h) s hs, ?_,
    (P.selectOffer_spec priority (offers h) s hs).2.1⟩
  exact ⟨s, hs, hs, rfl⟩

/-- Simultaneous selection respects the supplied fixed tie-breaking order. -/
theorem simultaneous_fixedTieBreaking [Finite X] (priority : LinearOrder X) :
    P.FixedTieBreaking priority (liftStatePolicy (P.simultaneous priority)) := by
  rintro h _ x ⟨s, _, hs, rfl⟩ y hy he
  exact (P.selectOffer_spec priority (offers h) s hs).2.2 y hy
    (he.trans (P.selectOffer_spec priority (offers h) s hs).2.1)

/-- A nonterminal finite state has a globally highest-priority admissible offer. -/
theorem exists_priority_offer [Finite X] (priority : LinearOrder X)
    {A : Set X} (h : ¬ P.Terminal A) :
    ∃ x, P.Admissible A x ∧ ∀ y, P.Admissible A y → priority.le y x := by
  obtain ⟨Q, hQ⟩ := P.exists_validBatch h
  obtain ⟨x, hx⟩ := hQ.1
  exact maximizers_nonempty_of_finite (CompletePreference.ofLinearOrder priority)
    (Set.toFinite {y | P.Admissible A y}) ⟨x, hQ.2.1 x hx⟩

/-- One fixed contract order determines both scheduling and tie selection.
The rule returns no batch at terminal states; those are not productive rounds. -/
noncomputable def fixedOrder [Finite X] (priority : LinearOrder X) : StatePolicy X :=
  by
    classical
    exact fun A => if h : P.Terminal A then ∅ else {(P.exists_priority_offer priority h).choose}

/-- The fixed-order constructor selects a valid singleton batch. -/
theorem fixedOrder_spec [Finite X] (priority : LinearOrder X)
    {A : Set X} (h : ¬ P.Terminal A) :
    ∃ x, P.fixedOrder priority A = {x} ∧ P.Admissible A x ∧
      ∀ y, P.Admissible A y → priority.le y x := by
  classical
  refine ⟨(P.exists_priority_offer priority h).choose, ?_,
    (P.exists_priority_offer priority h).choose_spec⟩
  simp only [fixedOrder, dif_neg h]

/-- Fixed contract-order scheduling is valid. -/
theorem fixedOrder_valid [Finite X] (priority : LinearOrder X) :
    P.ValidStatePolicy (P.fixedOrder priority) := by
  intro A h
  obtain ⟨x, hx, ha, _⟩ := P.fixedOrder_spec priority h
  rw [hx]
  exact (P.validBatch_singleton_iff A x).2 ha

/-- Fixed contract-order scheduling is sequential. -/
theorem fixedOrder_sequential [Finite X] (priority : LinearOrder X) :
    P.Sequential (liftStatePolicy (P.fixedOrder priority)) := by
  intro h _ ht
  obtain ⟨x, hx, _, _⟩ := P.fixedOrder_spec priority ht
  exact ⟨x, hx⟩

/-- Fixed contract-order scheduling also fixes each agent's tie-breaking. -/
theorem fixedOrder_fixedTieBreaking [Finite X] (priority : LinearOrder X) :
    P.FixedTieBreaking priority (liftStatePolicy (P.fixedOrder priority)) := by
  intro h _ x hx y hy _
  have ht : ¬ P.Terminal (offers h) := by
    intro ht
    have he : P.fixedOrder priority (offers h) = ∅ := by
      simp only [fixedOrder, dif_pos ht]
    change x ∈ P.fixedOrder priority (offers h) at hx
    rw [he] at hx
    exact hx
  obtain ⟨z, hz, _, hbest⟩ := P.fixedOrder_spec priority ht
  change x ∈ P.fixedOrder priority (offers h) at hx
  rw [hz] at hx
  have hxe : x = z := Set.mem_singleton_iff.mp hx
  exact hxe.symm ▸ hbest y hy

end MathEconLib.Matching.CumulativeOffer.Process
