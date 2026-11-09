/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
module

public import MathEconLib.Matching.Contracts.CumulativeOffer.Termination
public import MathEconLib.Matching.Contracts.ManyToOne

/-!
# Feasibility and individual rationality of cumulative offers

The hypotheses differ across the invariant statements:

* Rejection persistence (`held_of_held_of_subset`, `rejected_mono`, and
  `heldContracts_union_subset`) assumes buyer substitutability, for arbitrary offer sets.
* One-step proposer feasibility assumes buyer substitutability, a valid batch, and proposer
  feasibility before the batch. Run feasibility assumes buyer substitutability and a valid run.
* Proposer acceptability assumes a valid run, without buyer substitutability or IRC.
* Choosing held contracts from themselves assumes buyer IRC, for arbitrary offer sets.
* Market individual rationality assumes a valid run, buyer substitutability and IRC, seller
  locality, and seller acceptance of strictly acceptable singleton menus. The strict
  preference-induced seller-choice specialization supplies these last two conditions and
  assumes buyer choices respect buyer identities.
* Policy-outcome corollaries assume a finite contract type and a valid policy, together with
  the choice hypotheses of the corresponding run result.

Under buyer substitutability, rejected contracts remain rejected as accumulated offers grow.
Consequently every valid batched run holds at most one contract per proposer: previously
rejected contracts cannot be recalled, new offers come from proposers with no held contract,
and a batch has at most one offer per proposer. No restriction on buyer choices' off-run
counterparty feasibility is needed.

Every offered contract is strictly acceptable to its proposer. Buyer IRC makes held contracts
chosen from themselves, independently of substitutability. To conclude the existing
`Market.IndRational` predicate, the market's seller choices must agree with the cumulative offer process:
we use buyer substitutability for proposer feasibility, buyer IRC for buyer individual
rationality, and seller locality and acceptance of strictly acceptable singleton menus. These are
explicit hypotheses, since `ofMarket` deliberately ignores the market's seller choices.
Strict preference-induced seller choices satisfy this compatibility on arbitrary contract
types; only the finite policy-outcome corollary requires finiteness.

These are invariants of every valid run, including partial runs. Terminality, fixed
refinements, scheduling independence, stability, and optimality are not assumed or proved.
-/

@[expose] public section

namespace MathEconLib.Matching.CumulativeOffer

open MathEconLib.Choice MathEconLib.Preferences

variable {B S X : Type*}

namespace CumulativeOfferProcess

variable (P : CumulativeOfferProcess B S X)

/-- Strict acceptability relative to the proposer's outside option. -/
def Acceptable (x : X) : Prop :=
  (P.pref (P.seller x)).lt none (some ⟨x, rfl⟩)

/-- A contract is held precisely when its own buyer chooses it from that buyer's offer menu. -/
theorem mem_heldContracts_iff {A : Set X} {x : X} :
    x ∈ P.heldContracts A ↔ x ∈ P.choiceB (P.buyer x) {y ∈ A | P.buyer y = P.buyer x} := by
  constructor
  · rintro ⟨b, hx⟩
    have hb := ((P.choiceB b).choose_subset _ hx).2
    simpa only [hb] using hx
  · intro hx
    exact ⟨P.buyer x, hx⟩

/-- An admissible proposal is strictly acceptable. -/
theorem Admissible.acceptable {A : Set X} {x : X} (h : P.Admissible A x) :
    P.Acceptable x := by
  rcases h with ⟨s, ⟨x, hs⟩, rfl, _, hx⟩
  subst s
  exact hx.1.2

/-- Under buyer substitutability, a previously offered contract held after offer-set expansion
was already held before it. Requires nested offer sets and membership in the smaller set;
no valid-run, IRC, or finiteness hypothesis is used. -/
theorem held_of_held_of_subset (hsub : ∀ b, (P.choiceB b).Substitutable)
    {A D : Set X} (hAD : A ⊆ D) {x : X}
    (hx : x ∈ P.heldContracts D) (hxA : x ∈ A) : x ∈ P.heldContracts A := by
  apply (P.mem_heldContracts_iff).2
  have hmenus : {y ∈ A | P.buyer y = P.buyer x} ⊆
      {y ∈ D | P.buyer y = P.buyer x} := fun _ hy => ⟨hAD hy.1, hy.2⟩
  exact (hsub (P.buyer x)).mem_of_subset hmenus ((P.mem_heldContracts_iff).1 hx) ⟨hxA, rfl⟩

/-- Under buyer substitutability, rejections persist under expansion of accumulated offers.
No valid-run, IRC, or finiteness hypothesis is used. -/
theorem rejected_mono (hsub : ∀ b, (P.choiceB b).Substitutable) :
    Monotone (fun A => A \ P.heldContracts A) := by
  intro A D hAD x hx
  exact ⟨hAD hx.1, fun hheld => hx.2 (P.held_of_held_of_subset hsub hAD hheld hx.1)⟩

/-- Under buyer substitutability, every contract held from enlarged offers was previously held
or belongs to the newly added set. The added set need not be a valid batch. -/
theorem heldContracts_union_subset (hsub : ∀ b, (P.choiceB b).Substitutable) (A Q : Set X) :
    P.heldContracts (A ∪ Q) ⊆ P.heldContracts A ∪ Q := by
  intro x hx
  rcases P.heldContracts_subset (A ∪ Q) hx with hxA | hxQ
  · exact Or.inl (P.held_of_held_of_subset hsub Set.subset_union_left hx hxA)
  · exact Or.inr hxQ

/-- Buyer substitutability and a valid batch preserve at most one held contract per proposer,
assuming this property before the batch. No IRC or finiteness hypothesis is used. -/
theorem ValidBatch.heldContracts_injOn (hsub : ∀ b, (P.choiceB b).Substitutable)
    {A Q : Set X} (hQ : P.ValidBatch A Q) (hA : Set.InjOn P.seller (P.heldContracts A)) :
    Set.InjOn P.seller (P.heldContracts (A ∪ Q)) := by
  intro x hx y hy hxy
  rcases P.heldContracts_union_subset hsub A Q hx with hx | hx
  · rcases P.heldContracts_union_subset hsub A Q hy with hy | hy
    · exact hA hx hy hxy
    · exact ((hQ.2.1 y hy).eligible P).1 x hx hxy |>.elim
  · rcases P.heldContracts_union_subset hsub A Q hy with hy | hy
    · exact ((hQ.2.1 x hx).eligible P).1 y hy hxy.symm |>.elim
    · exact hQ.2.2 hx hy hxy

/-- Every valid run has at most one held contract per proposer under buyer substitutability.
Buyer choices may select multiple contracts with a proposer off the run. -/
theorem Run.heldContracts_injOn (hsub : ∀ b, (P.choiceB b).Substitutable)
    {h : List (Set X)} (hr : P.Run h) : Set.InjOn P.seller (P.heldContracts (offers h)) := by
  induction hr with
  | nil =>
    intro x hx
    exact (P.heldContracts_subset ∅ hx).elim
  | cons _ hQ ih => exact hQ.heldContracts_injOn P hsub ih

/-- Every contract offered during a valid run is strictly acceptable to its proposer.
No buyer substitutability, IRC, or finiteness hypothesis is used. -/
theorem Run.acceptable_offers {h : List (Set X)} (hr : P.Run h) :
    ∀ x ∈ offers h, P.Acceptable x := by
  induction hr with
  | nil => exact fun _ hx => hx.elim
  | cons _ hQ ih =>
    intro x hx
    rcases hx with hx | hx
    · exact ih x hx
    · exact (hQ.2.1 x hx).acceptable P

/-- Held contracts inherit proposer acceptability, with no buyer regularity assumptions. -/
theorem Run.acceptable_heldContracts {h : List (Set X)} (hr : P.Run h) :
    ∀ x ∈ P.heldContracts (offers h), P.Acceptable x :=
  fun x hx => hr.acceptable_offers P x (P.heldContracts_subset _ hx)

/-- A buyer's part of aggregate held contracts is exactly that buyer's choice from its own offers. -/
theorem buyer_heldContracts_eq (A : Set X) (b : B) :
    {x ∈ P.heldContracts A | P.buyer x = b} = P.choiceB b {x ∈ A | P.buyer x = b} := by
  ext x
  constructor
  · rintro ⟨hx, hb⟩
    simpa only [hb] using (P.mem_heldContracts_iff).1 hx
  · intro hx
    exact ⟨⟨b, hx⟩, ((P.choiceB b).choose_subset _ hx).2⟩

/-- Buyer IRC makes each buyer choose its held contracts from those held contracts.
This holds for arbitrary offer sets, without substitutability or a valid-run hypothesis. -/
theorem choice_heldContracts_eq (hcons : ∀ b, (P.choiceB b).Consistent) (A : Set X) (b : B) :
    P.choiceB b {x ∈ P.heldContracts A | P.buyer x = b} =
      {x ∈ P.heldContracts A | P.buyer x = b} := by
  rw [P.buyer_heldContracts_eq]
  exact (hcons b).idempotent _

/-- On a finite contract type, a valid policy produces at most one held contract per proposer
under buyer substitutability. No buyer IRC hypothesis is used. -/
theorem rawOutcome_injOn [Finite X] (hsub : ∀ b, (P.choiceB b).Substitutable)
    {π : Policy X} (hp : P.ValidPolicy π) : Set.InjOn P.seller (P.rawOutcome π) :=
  (P.execute_run hp _).heldContracts_injOn P hsub

end CumulativeOfferProcess

/-- Under buyer substitutability, valid market-adapted runs satisfy the library's many-to-one
feasibility predicate. No buyer IRC, seller-choice compatibility, or finiteness is assumed. -/
theorem manyToOneFeasible_of_run (M : Market B S X)
    (pref : ∀ s, CompletePreference (Option {x : X // M.seller x = s}))
    (hsub : ∀ b, (M.choiceB b).Substitutable)
    {h : List (Set X)} (hr : (ofMarket M pref).Run h) :
    M.ManyToOneFeasible ((ofMarket M pref).heldContracts (CumulativeOfferProcess.offers h)) :=
  hr.heldContracts_injOn (ofMarket M pref) hsub

/-- Buyer substitutability and IRC, together with seller locality and acceptance of strictly
acceptable singleton menus, give market individual rationality along valid runs.
Substitutability supplies proposer feasibility, IRC gives buyer individual rationality, and
seller compatibility gives seller individual rationality. No finiteness is assumed. -/
theorem indRational_of_run (M : Market B S X)
    (pref : ∀ s, CompletePreference (Option {x : X // M.seller x = s}))
    (hsub : ∀ b, (M.choiceB b).Substitutable)
    (hcons : ∀ b, (M.choiceB b).Consistent)
    (hlocal : ∀ s A, M.choiceS s (M.sellerSide s A) = M.choiceS s A)
    (haccept : ∀ x, (ofMarket M pref).Acceptable x → x ∈ M.choiceS (M.seller x) {x})
    {h : List (Set X)} (hr : (ofMarket M pref).Run h) :
    M.IndRational ((ofMarket M pref).heldContracts (CumulativeOfferProcess.offers h)) := by
  let P := ofMarket M pref
  let Z := P.heldContracts (CumulativeOfferProcess.offers h)
  have hfeas := hr.heldContracts_injOn P hsub
  refine ⟨?_, ?_⟩
  · intro b
    rw [← M.choiceB_buyerSide (hcons b) Z]
    exact P.choice_heldContracts_eq hcons _ b
  · intro s
    apply Set.Subset.antisymm (M.choiceS_subset_sellerSide s _)
    intro x hx
    have hsingle : M.sellerSide s Z = {x} := by
      ext y
      constructor
      · intro hy
        exact Set.mem_singleton_iff.mpr (hfeas hy.1 hx.1 (hy.2.trans hx.2.symm))
      · intro hy
        simpa only [Set.mem_singleton_iff.mp hy] using hx
    rw [← hlocal s Z, hsingle, ← hx.2]
    exact haccept x (hr.acceptable_heldContracts P x hx.1)

/-- On a finite contract type, a valid policy inherits market individual rationality under
buyer substitutability and IRC, seller locality, and acceptance of strictly acceptable singleton
menus. The policy may depend on the history and select batches. -/
theorem indRational_rawOutcome [Finite X] (M : Market B S X)
    (pref : ∀ s, CompletePreference (Option {x : X // M.seller x = s}))
    (hsub : ∀ b, (M.choiceB b).Substitutable)
    (hcons : ∀ b, (M.choiceB b).Consistent)
    (hlocal : ∀ s A, M.choiceS s (M.sellerSide s A) = M.choiceS s A)
    (haccept : ∀ x, (ofMarket M pref).Acceptable x → x ∈ M.choiceS (M.seller x) {x})
    {π : CumulativeOfferProcess.Policy X} (hp : (ofMarket M pref).ValidPolicy π) :
    M.IndRational ((ofMarket M pref).rawOutcome π) :=
  indRational_of_run M pref hsub hcons hlocal haccept ((ofMarket M pref).execute_run hp _)

/-- Under buyer substitutability and IRC, a valid run has market individual rationality when
seller choices are induced by strict preferences and buyer choices respect buyer identities.
The seller choices supply locality and acceptance of strictly acceptable singleton menus.
No finiteness or off-run buyer feasibility is needed. -/
theorem indRational_ofSellerPreferences_of_run
    (buyer : X → B) (seller : X → S) (choiceB : B → ChoiceFunction X)
    (hB : ∀ ⦃b Y x⦄, x ∈ choiceB b Y → buyer x = b)
    (pref : ∀ s, LinearOrder (Option {x : X // seller x = s}))
    (hsub : ∀ b, (choiceB b).Substitutable)
    (hcons : ∀ b, (choiceB b).Consistent)
    {h : List (Set X)}
    (hr : (ofMarket (Market.ofSellerPreferences buyer seller choiceB hB pref)
      (fun s => CompletePreference.ofLinearOrder (pref s))).Run h) :
    (Market.ofSellerPreferences buyer seller choiceB hB pref).IndRational
      ((ofMarket (Market.ofSellerPreferences buyer seller choiceB hB pref)
        (fun s => CompletePreference.ofLinearOrder (pref s))).heldContracts (CumulativeOfferProcess.offers h)) := by
  apply indRational_of_run _ _ hsub hcons ?_ ?_ hr
  · intro s A
    have hmenu : (fun y : {x : X // seller x = s} => y.val) ⁻¹' {x ∈ A | seller x = s} =
        (fun y : {x : X // seller x = s} => y.val) ⁻¹' A := by
      ext y
      exact ⟨fun hy => hy.1, fun hy => ⟨hy, y.property⟩⟩
    change Subtype.val '' (ChoiceFunction.ofOptionLinearOrder (pref s))
      ((fun y : {x : X // seller x = s} => y.val) ⁻¹' {x ∈ A | seller x = s}) =
        Subtype.val '' (ChoiceFunction.ofOptionLinearOrder (pref s))
          ((fun y : {x : X // seller x = s} => y.val) ⁻¹' A)
    rw [hmenu]
  · intro x hx
    change ∃ y : {z : X // seller z = seller x},
      y ∈ ChoiceFunction.ofOptionLinearOrder (pref (seller x))
        ((fun z : {z : X // seller z = seller x} => z.val) ⁻¹' {x}) ∧ y.val = x
    refine ⟨⟨x, rfl⟩, (ChoiceFunction.mem_ofOptionLinearOrder _).2 ⟨?_, hx.1, ?_⟩, rfl⟩
    · exact Set.mem_singleton x
    · intro y hy
      have he : y = ⟨x, rfl⟩ := Subtype.ext (Set.mem_singleton_iff.mp hy)
      rw [he]

end MathEconLib.Matching.CumulativeOffer
