/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
module

public import MathEconLib.Matching.Contracts.CumulativeOffer.Attainment
public import Mathlib.Order.WithBot

/-!
# Cumulative offer policies

Policies select batches from reverse-chronological histories. Validity is a separate proposition.
State policies lift by forgetting history beyond accumulated offers. Singleton and simultaneous
restrictions constrain participation; fixed tie-breaking additionally constrains contract selection.
The fixed-order constructor uses one contract order for both scheduling and tie-breaking.
Higher elements in that supplied order have priority. All constructors preserve strict preferences.

## Main definitions

`Policy`, `ValidPolicy`, and `Follows` describe policy-following valid histories.
`selectedOffers`, `selectedBatch`, `simultaneous`, and `fixedOrder` define choices without
finiteness assumptions; `selectOfferOfAttainment` extracts an attained choice.

## Main statements

`selectedBatch_valid` and `simultaneous_valid` use per-seller attainment.
`fixedOrder_valid` requires attainment across all admissible proposals.
Finite-contract and finite-menu corollaries discharge these hypotheses.
-/

@[expose] public section

namespace MathEconLib.Matching.CumulativeOffer.CumulativeOfferProcess

open MathEconLib.Choice MathEconLib.Choice.ChoiceFunction MathEconLib.Preferences

variable {B S X : Type*} (P : CumulativeOfferProcess B S X)

/-- A deterministic history-dependent batch rule. -/
abbrev Policy (X : Type*) := List (Set X) → Set X

/-- A run follows a policy when each newest batch is the policy's choice at its prior history. -/
def Follows (π : Policy X) : List (Set X) → Prop
  | [] => True
  | Q :: h => Follows π h ∧ Q = π h

/-- Validity is required only along valid nonterminal histories following the policy. -/
def ValidPolicy (π : Policy X) : Prop :=
  ∀ h, P.Run h → Follows π h → ¬ P.Terminal (offers h) → P.ValidBatch (offers h) (π h)

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
  fun h _ _ ht => hσ (offers h) ht

/-- State rules give identical batches at histories with identical accumulated offers. -/
theorem liftStatePolicy_eq (σ : StatePolicy X) {h k : List (Set X)}
    (he : offers h = offers k) : liftStatePolicy σ h = liftStatePolicy σ k := by
  simp only [liftStatePolicy, he]

/-- Exactly one proposal at each nonterminal valid history following the policy. -/
def Sequential (π : Policy X) : Prop :=
  ∀ h, P.Run h → Follows π h → ¬ P.Terminal (offers h) → ∃ x, π h = {x}

/-- Every eligible proposer participates. Combined with validity, each proposes exactly once. -/
def Simultaneous (π : Policy X) : Prop :=
  ∀ h, P.Run h → Follows π h → ∀ s, P.Eligible (offers h) s →
    ∃ x ∈ π h, P.seller x = s

/-- Selected proposals have greatest priority among the proposing seller's admissible proposals.
This fixes tie selection, not the scheduling of different sellers. -/
def FixedTieBreaking (priority : LinearOrder X) (π : Policy X) : Prop :=
  ∀ h, P.Run h → Follows π h → ∀ x ∈ π h, ∀ y, P.Admissible (offers h) y →
    P.seller y = P.seller x → priority.le y x

/-- Follows for a lifted state policy exposes only the previous offer set. -/
theorem follows_lift_cons (σ : StatePolicy X) (Q : Set X) (h : List (Set X)) :
    Follows (liftStatePolicy σ) (Q :: h) ↔
      Follows (liftStatePolicy σ) h ∧ Q = σ (offers h) := Iff.rfl

/-- All currently admissible contracts of a specified proposer. -/
def admissibleProposals (A : Set X) (s : S) : Set X :=
  {x | P.Admissible A x ∧ P.seller x = s}

/-- Eligible agents have a nonempty admissible set when contracts are finite. -/
theorem admissibleProposals_nonempty [Finite X] {A : Set X} {s : S}
    (h : P.Eligible A s) : (P.admissibleProposals A s).Nonempty :=
  h.exists_admissible P (Set.toFinite _)

/-- Lift the contract order to option priorities, ranking the outside option first at a tie. -/
def proposalPriority (s : S) : Option (P.Own s) ↪ WithTop X :=
  (Function.Embedding.subtype (fun x : X ↦ P.seller x = s)).optionMap

/-- The proposal order compares the seller's preference first and contract priority at a tie. -/
@[instance_reducible]
noncomputable def proposalOrder (priority : LinearOrder X) (s : S) :
    LinearOrder (Option (P.Own s)) :=
  let := priority
  (P.pref s).tieBreak (P.proposalPriority s)

private theorem admissible_val_iff (A : Set X) {s : S} (x : P.Own s) :
    P.Admissible A x.val ↔
      P.NoHeldContract A s ∧ x ∈ maximizers (P.contractPreference s) (P.remaining A s) := by
  constructor
  · rintro ⟨t, y, hy, hheld, hbest⟩
    have hts : t = s := y.property.symm.trans ((congrArg P.seller hy).trans x.property)
    subst t
    have hyx : y = x := Subtype.ext hy
    subst y
    exact ⟨hheld, hbest⟩
  · rintro ⟨hheld, hbest⟩
    exact ⟨s, x, rfl, hheld, hbest⟩

/-- Refined option choice on a seller's unoffered menu, whether or not it attains.
The empty set may mean declining or nonattainment; eligibility and attainment are separate. -/
noncomputable def selectedOffers (priority : LinearOrder X) (A : Set X) (s : S) : Set X :=
  Subtype.val '' ofOptionLinearOrder (P.proposalOrder priority s) (P.unofferedOwnMenu A s)

/-- Eligible sellers with attained refined choice supply a proposal. -/
theorem selectedOffers_nonempty (priority : LinearOrder X) {A : Set X} {s : S}
    (h : P.Eligible A s)
    (hatt : HasBundleOptimum (P.proposalOrder priority s) optionBundle
      (P.unofferedOwnMenu A s)) : (P.selectedOffers priority A s).Nonempty := by
  let := priority
  have hne : (ofOptionLinearOrder (P.proposalOrder priority s)
      (P.unofferedOwnMenu A s)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun he ↦ h.not_hasBundleOptimum_of_optionChoice_eq_empty P
      (P.proposalPriority s) (fun _ ↦ le_top) he hatt
  exact hne.image Subtype.val

/-- Select from attained refined option choice, without a finite contract type. -/
noncomputable def selectOfferOfAttainment (priority : LinearOrder X)
    (A : Set X) (s : S) (h : P.Eligible A s)
    (hatt : HasBundleOptimum (P.proposalOrder priority s) optionBundle
      (P.unofferedOwnMenu A s)) : X :=
  (P.selectedOffers_nonempty priority h hatt).choose

/-- The attained selector is admissible and greatest among this seller's admissible proposals. -/
theorem selectOfferOfAttainment_spec (priority : LinearOrder X)
    (A : Set X) (s : S) (h : P.Eligible A s)
    (hatt : HasBundleOptimum (P.proposalOrder priority s) optionBundle
      (P.unofferedOwnMenu A s)) :
    P.Admissible A (P.selectOfferOfAttainment priority A s h hatt) ∧
      P.seller (P.selectOfferOfAttainment priority A s h hatt) = s ∧
      ∀ y, P.Admissible A y → P.seller y = s →
        priority.le y (P.selectOfferOfAttainment priority A s h hatt) := by
  let := priority
  obtain ⟨x, hx, he⟩ := (P.selectedOffers_nonempty priority h hatt).choose_spec
  change x.val = P.selectOfferOfAttainment priority A s h hatt at he
  rw [← he]
  have hbest := (P.mem_tieBreak_optionChoice_iff A s (P.proposalPriority s)
    (fun _ ↦ le_top) x).mp hx
  refine ⟨(P.admissible_val_iff A x).mpr ⟨h.1, hbest.1⟩, x.property, ?_⟩
  intro y hy hs
  let z : P.Own s := ⟨y, hs⟩
  exact WithTop.coe_le_coe.mp (hbest.2 z ((P.admissible_val_iff A z).mp hy).2)

/-- Finite-contract convenience wrapper for the attained option-choice selector. -/
noncomputable def selectOffer [Finite X] (priority : LinearOrder X)
    (A : Set X) (s : S) (h : P.Eligible A s) : X :=
  P.selectOfferOfAttainment priority A s h
    (P.hasBundleOptimum_unofferedOwnMenu_of_finite _ (Set.toFinite _))

/-- The finite wrapper preserves admissibility and greatest priority. -/
theorem selectOffer_spec [Finite X] (priority : LinearOrder X)
    (A : Set X) (s : S) (h : P.Eligible A s) :
    P.Admissible A (P.selectOffer priority A s h) ∧
      P.seller (P.selectOffer priority A s h) = s ∧
      ∀ y, P.Admissible A y → P.seller y = s →
        priority.le y (P.selectOffer priority A s h) :=
  P.selectOfferOfAttainment_spec priority A s h _

/-- For an eligible seller, strict option choice on the unoffered menu selects the same
contract as the finite policy. -/
theorem ofOptionLinearOrder_proposalOrder_eq_singleton_selectOffer [Finite X]
    (priority : LinearOrder X) (A : Set X) (s : S) (h : P.Eligible A s) :
    Subtype.val '' ofOptionLinearOrder (P.proposalOrder priority s) (P.unofferedOwnMenu A s) =
      {P.selectOffer priority A s h} := by
  let := priority
  obtain ⟨had, hs, hmax⟩ := P.selectOffer_spec priority A s h
  let x : P.Own s := ⟨P.selectOffer priority A s h, hs⟩
  have hxbest := ((P.admissible_val_iff A x).mp had).2
  have hx : x ∈ ofOptionLinearOrder (P.proposalOrder priority s) (P.unofferedOwnMenu A s) := by
    refine (P.mem_tieBreak_optionChoice_iff A s (P.proposalPriority s) (fun _ ↦ le_top) x).mpr
      ⟨hxbest, fun y hy ↦ ?_⟩
    change (y.val : WithTop X) ≤ (x.val : WithTop X)
    exact WithTop.coe_le_coe.mpr (hmax y.val ((P.admissible_val_iff A y).mpr ⟨h.1, hy⟩) y.property)
  rw [(unitDemand_ofOptionLinearOrder (P.proposalOrder priority s) _).eq_singleton_of_mem hx,
    Set.image_singleton]

/-- A subset of eligible sellers submits its refined option choices. -/
noncomputable def selectedBatch (priority : LinearOrder X)
    (A : Set X) (T : Set S) : Set X :=
  {x | ∃ s ∈ T, P.Eligible A s ∧ x ∈ P.selectedOffers priority A s}

/-- Attainment is needed only for participating sellers, not the whole contract type. -/
theorem selectedBatch_valid (priority : LinearOrder X)
    {A : Set X} {T : Set S} (hne : T.Nonempty)
    (hel : ∀ s ∈ T, P.Eligible A s)
    (hatt : ∀ s ∈ T, HasBundleOptimum (P.proposalOrder priority s) optionBundle
      (P.unofferedOwnMenu A s)) :
    P.ValidBatch A (P.selectedBatch priority A T) := by
  let := priority
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨s, hs⟩ := hne
    obtain ⟨x, hx⟩ := P.selectedOffers_nonempty priority (hel s hs) (hatt s hs)
    exact ⟨x, s, hs, hel s hs, hx⟩
  · rintro x ⟨s, _, hs, y, hy, rfl⟩
    exact (P.admissible_val_iff A y).mpr ⟨hs.1,
      ((P.mem_tieBreak_optionChoice_iff A s (P.proposalPriority s)
        (fun _ ↦ le_top) y).mp hy).1⟩
  · rintro x ⟨s, _, _, u, hu, rfl⟩ y ⟨t, _, _, v, hv, rfl⟩ he
    have hst : s = t := u.property.symm.trans (he.trans v.property)
    subst t
    exact congrArg Subtype.val
      ((unitDemand_ofOptionLinearOrder (P.proposalOrder priority s) _) hu hv)

/-- Every eligible seller proposes according to refined option choice. -/
noncomputable def simultaneous (priority : LinearOrder X) : StatePolicy X :=
  fun A => P.selectedBatch priority A {s | P.Eligible A s}

/-- Per-seller attainment suffices for simultaneous validity, even with infinitely many sellers. -/
theorem simultaneous_valid (priority : LinearOrder X)
    (hatt : ∀ A s, P.Eligible A s →
      HasBundleOptimum (P.proposalOrder priority s) optionBundle (P.unofferedOwnMenu A s)) :
    P.ValidStatePolicy (P.simultaneous priority) := by
  intro A h
  classical
  obtain ⟨s, hs⟩ := not_forall.mp h
  exact P.selectedBatch_valid priority ⟨s, not_not.mp hs⟩ (fun _ hs => hs) (hatt A)

/-- Finite own menus are sufficient for validity; the global contract type may be infinite. -/
theorem simultaneous_valid_of_finite_menus (priority : LinearOrder X)
    (hfin : ∀ A s, P.Eligible A s → (P.unofferedOwnMenu A s).Finite) :
    P.ValidStatePolicy (P.simultaneous priority) :=
  P.simultaneous_valid priority (fun A s hs ↦
    P.hasBundleOptimum_unofferedOwnMenu_of_finite _ (hfin A s hs))

/-- Finiteness of the contract type is one sufficient condition. -/
theorem simultaneous_valid_of_finite [Finite X] (priority : LinearOrder X) :
    P.ValidStatePolicy (P.simultaneous priority) :=
  P.simultaneous_valid_of_finite_menus priority (fun _ _ _ ↦ Set.toFinite _)

/-- Attainment ensures that every eligible seller participates. -/
theorem simultaneous_all (priority : LinearOrder X)
    (hatt : ∀ A s, P.Eligible A s →
      HasBundleOptimum (P.proposalOrder priority s) optionBundle (P.unofferedOwnMenu A s)) :
    P.Simultaneous (liftStatePolicy (P.simultaneous priority)) := by
  intro h _ _ s hs
  obtain ⟨x, hx⟩ := P.selectedOffers_nonempty priority hs (hatt _ s hs)
  refine ⟨x, ⟨s, hs, hs, hx⟩, ?_⟩
  obtain ⟨y, _, rfl⟩ := hx
  exact y.property

/-- Refined option choice fixes tie-breaking without an attainment assumption. -/
theorem simultaneous_fixedTieBreaking (priority : LinearOrder X) :
    P.FixedTieBreaking priority (liftStatePolicy (P.simultaneous priority)) := by
  let := priority
  rintro h _ _ x ⟨s, _, hs, u, hu, rfl⟩ y hy he
  let v : P.Own s := ⟨y, he.trans u.property⟩
  have hv := ((P.admissible_val_iff (offers h) v).mp hy).2
  have hle := ((P.mem_tieBreak_optionChoice_iff (offers h) s (P.proposalPriority s)
    (fun _ ↦ le_top) u).mp hu).2 v hv
  exact WithTop.coe_le_coe.mp hle

/-- A nonterminal finite state has a globally highest-priority admissible offer. -/
theorem exists_priority_offer [Finite X] (priority : LinearOrder X)
    {A : Set X} (h : ¬ P.Terminal A) :
    ∃ x, P.Admissible A x ∧ ∀ y, P.Admissible A y → priority.le y x := by
  obtain ⟨Q, hQ⟩ := P.exists_validBatch h
  obtain ⟨x, hx⟩ := hQ.1
  exact maximizers_nonempty_of_finite (CompletePreference.ofLinearOrder priority)
    (Set.toFinite {y | P.Admissible A y}) ⟨x, hQ.2.1 x hx⟩

/-- One fixed contract order determines scheduling and tie selection.
The rule is empty when the admissible union has no greatest element. -/
noncomputable def fixedOrder (priority : LinearOrder X) : StatePolicy X := by
  classical
  exact fun A => if h : ∃ x, P.Admissible A x ∧
    ∀ y, P.Admissible A y → priority.le y x then {h.choose} else ∅

/-- Global attainment supplies the fixed-order proposal. -/
theorem fixedOrder_spec (priority : LinearOrder X) {A : Set X}
    (h : ∃ x, P.Admissible A x ∧ ∀ y, P.Admissible A y → priority.le y x) :
    ∃ x, P.fixedOrder priority A = {x} ∧ P.Admissible A x ∧
      ∀ y, P.Admissible A y → priority.le y x := by
  classical
  exact ⟨h.choose, by simp only [fixedOrder, dite_eq_left h], h.choose_spec⟩

/-- Fixed-order validity requires attainment on the union of admissible proposals.
Per-seller attainment alone does not suffice with infinitely many eligible sellers. -/
theorem fixedOrder_valid (priority : LinearOrder X)
    (hatt : ∀ A, ¬ P.Terminal A →
      ∃ x, P.Admissible A x ∧ ∀ y, P.Admissible A y → priority.le y x) :
    P.ValidStatePolicy (P.fixedOrder priority) := by
  intro A h
  obtain ⟨x, hx, ha, _⟩ := P.fixedOrder_spec priority (hatt A h)
  rw [hx]
  exact (P.validBatch_singleton_iff A x).2 ha

/-- Finiteness implies the global attainment needed for fixed-order validity. -/
theorem fixedOrder_valid_of_finite [Finite X] (priority : LinearOrder X) :
    P.ValidStatePolicy (P.fixedOrder priority) :=
  P.fixedOrder_valid priority (fun _ h ↦ P.exists_priority_offer priority h)

/-- Fixed contract-order scheduling is sequential whenever the admissible union attains. -/
theorem fixedOrder_sequential (priority : LinearOrder X)
    (hatt : ∀ A, ¬ P.Terminal A →
      ∃ x, P.Admissible A x ∧ ∀ y, P.Admissible A y → priority.le y x) :
    P.Sequential (liftStatePolicy (P.fixedOrder priority)) := by
  intro h _ _ ht
  obtain ⟨x, hx, _, _⟩ := P.fixedOrder_spec priority (hatt _ ht)
  exact ⟨x, hx⟩

/-- Fixed contract-order scheduling fixes tie-breaking even without attainment. -/
theorem fixedOrder_fixedTieBreaking (priority : LinearOrder X) :
    P.FixedTieBreaking priority (liftStatePolicy (P.fixedOrder priority)) := by
  classical
  intro h _ _ x hx y hy _
  change x ∈ P.fixedOrder priority (offers h) at hx
  unfold fixedOrder at hx
  split at hx
  next hatt =>
    have he : x = hatt.choose := Set.mem_singleton_iff.mp hx
    exact he.symm ▸ hatt.choose_spec.2 y hy
  next => exact hx.elim

end MathEconLib.Matching.CumulativeOffer.CumulativeOfferProcess
