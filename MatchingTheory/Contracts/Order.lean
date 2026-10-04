import MatchingTheory.Contracts.FixedPointCore

/-!
# The order and lattice of stable outcomes

The fixed-point order is unanimous seller choice and reverse unanimous
buyer choice. This yields both side-optimality results and the stable-outcome
lattice, without finiteness, unit demand, or the law of aggregate demand.
-/

open Function OrderDual

universe u v w

variable {B : Type u} {S : Type v} {X : Type w}

namespace Market

variable (M : Market B S X)

/-! ### The order dictionary

The three statements

* `p ≤ q` in the state lattice,
* `SellerChosen (outcomeOf q) (outcomeOf p)` — every seller chooses their part
  of the `q`-outcome out of the union,
* `BuyerChosen (outcomeOf p) (outcomeOf q)` — every buyer chooses their part
  of the `p`-outcome out of the union,

are equivalent.  This is *opposition of interests*, and it is phrased through
choice functions rather than preference relations: at many-to-many generality
there is no primitive preference over sets, and `Cˢ(A ∪ A') = A'` is the form
that survives (and the form that feeds comparative statics).  The many-to-one
"each seller weakly prefers their contract in `A'`" reading is a unit-demand
specialisation and belongs downstream, not here — that is the Blair trap.

None of this uses `SizeMonotone`. -/

section OrderDictionary

variable (hsub : M.Substitutable) (hcons : M.Consistent)

include hsub hcons

/-- `→`, seller side.  Two IRC sandwiches at `q` and individual rationality. -/
theorem sellerChosen_outcomeOf_of_le {p q : Set X × (Set X)ᵒᵈ}
    (hq : IsFixedPt M.daFun q) (h : p ≤ q) :
    M.SellerChosen (M.outcomeOf q) (M.outcomeOf p) := by
  intro s
  have h1 : p.1 ⊆ q.1 := h.1
  have hop : M.outcomeOf p ⊆ q.1 := fun x hx => h1 hx.1
  have hoq : M.outcomeOf q ⊆ q.1 := fun x hx => hx.1
  have e1 : M.choiceS s (M.outcomeOf q ∪ M.outcomeOf p) = M.choiceS s q.1 :=
    M.choiceS_eq_of_isFixedPt_sandwich hcons hq s (fun x hx => Or.inl hx)
      (Set.union_subset hoq hop)
  have e2 : M.choiceS s (M.outcomeOf q) = M.choiceS s q.1 :=
    M.choiceS_eq_of_isFixedPt_sandwich hcons hq s (subset_refl _) hoq
  have hstable : M.Stable (M.outcomeOf q) := M.stable_outcomeOf hsub hcons hq
  show M.choiceS s (M.outcomeOf q ∪ M.outcomeOf p)
      = M.sellerSide s (M.outcomeOf q)
  rw [e1, ← e2]
  exact hstable.1.2 s

/-- `→`, buyer side.  The dual coordinate of `h` says exactly that the
`q`-outcome sits inside the contracts still available to buyers at `p`. -/
theorem buyerChosen_outcomeOf_of_le {p q : Set X × (Set X)ᵒᵈ}
    (hp : IsFixedPt M.daFun p) (h : p ≤ q) :
    M.BuyerChosen (M.outcomeOf p) (M.outcomeOf q) := by
  intro b
  have hA : M.Stable (M.outcomeOf p) := M.stable_outcomeOf hsub hcons hp
  have h2 : (ofDual q.2 : Set X) ⊆ (ofDual p.2 : Set X) := h.2
  have hb : M.toBuyers (M.outcomeOf p) = (ofDual p.2 : Set X) :=
    M.toBuyers_outcomeOf hsub hcons hp
  have key : ∀ y ∈ M.outcomeOf p ∪ M.outcomeOf q, y ∉ M.outcomeOf p →
      y ∈ M.toBuyers (M.outcomeOf p) := by
    intro y hy hyA
    rcases hy with h' | h'
    · exact absurd h' hyA
    · rw [hb]; exact h2 h'.2
  have e : M.choiceB b (M.outcomeOf p ∪ M.outcomeOf q)
      = M.choiceB b (M.outcomeOf p) :=
    M.choiceB_eq_of_stable hsub hcons hA b (subset_refl _)
      (fun x hx => Or.inl hx) key
  show M.choiceB b (M.outcomeOf p ∪ M.outcomeOf q)
      = M.buyerSide b (M.outcomeOf p)
  rw [e, hA.1.1 b]

/-- Opposition of interests, seller ⇒ buyer.  If a buyer chose some
`y ∈ A' \ A` out of `A ∪ A'`, Chernoff on *both* sides drops the menu to
`insert y A` and `y` blocks `A`.  Only `A` need be stable. -/
theorem buyerChosen_of_sellerChosen {A A' : Set X} (hA : M.Stable A)
    (h : M.SellerChosen A' A) : M.BuyerChosen A A' := by
  intro b
  have hchB : (M.choiceB b).Chernoff :=
    ChoiceFunction.substitutable_iff_chernoff.mp (hsub.1 b)
  have key : M.choiceB b (A ∪ A') ⊆ A := by
    intro y hy
    by_contra hyA
    have hyU : y ∈ A ∪ A' := (M.choiceB b).choose_subset _ hy
    have hyA' : y ∈ A' := hyU.resolve_left hyA
    have hby : M.buyer y = b := M.buyer_eq_of_mem hy
    have hins : insert y A ⊆ A ∪ A' :=
      Set.insert_subset_iff.mpr ⟨Or.inr hyA', fun x hx => Or.inl hx⟩
    have hyB : y ∈ M.choiceB (M.buyer y) (insert y A) := by
      rw [hby]; exact hchB hins ⟨hy, Set.mem_insert _ _⟩
    have hchS : (M.choiceS (M.seller y)).Chernoff :=
      ChoiceFunction.substitutable_iff_chernoff.mp (hsub.2 (M.seller y))
    have hyS0 : y ∈ M.choiceS (M.seller y) (A' ∪ A) := by
      rw [h (M.seller y)]; exact ⟨hyA', rfl⟩
    have hins' : insert y A ⊆ A' ∪ A :=
      Set.insert_subset_iff.mpr ⟨Or.inl hyA', fun x hx => Or.inr hx⟩
    have hyS : y ∈ M.choiceS (M.seller y) (insert y A) :=
      hchS hins' ⟨hyS0, Set.mem_insert _ _⟩
    exact hyA (M.not_blocking_singleton hA hyB hyS)
  show M.choiceB b (A ∪ A') = M.buyerSide b A
  rw [← hcons.1 b key (fun x hx => Or.inl hx), hA.1.1 b]

/-- Opposition of interests, buyer ⇒ seller. -/
theorem sellerChosen_of_buyerChosen {A A' : Set X} (hA' : M.Stable A')
    (h : M.BuyerChosen A A') : M.SellerChosen A' A := by
  intro s
  have hchS : (M.choiceS s).Chernoff :=
    ChoiceFunction.substitutable_iff_chernoff.mp (hsub.2 s)
  have key : M.choiceS s (A' ∪ A) ⊆ A' := by
    intro y hy
    by_contra hyA'
    have hyU : y ∈ A' ∪ A := (M.choiceS s).choose_subset _ hy
    have hyA : y ∈ A := hyU.resolve_left hyA'
    have hsy : M.seller y = s := M.seller_eq_of_mem hy
    have hins : insert y A' ⊆ A' ∪ A :=
      Set.insert_subset_iff.mpr ⟨Or.inr hyA, fun x hx => Or.inl hx⟩
    have hyS : y ∈ M.choiceS (M.seller y) (insert y A') := by
      rw [hsy]; exact hchS hins ⟨hy, Set.mem_insert _ _⟩
    have hchB : (M.choiceB (M.buyer y)).Chernoff :=
      ChoiceFunction.substitutable_iff_chernoff.mp (hsub.1 (M.buyer y))
    have hyB0 : y ∈ M.choiceB (M.buyer y) (A ∪ A') := by
      rw [h (M.buyer y)]; exact ⟨hyA, rfl⟩
    have hins' : insert y A' ⊆ A ∪ A' :=
      Set.insert_subset_iff.mpr ⟨Or.inl hyA, fun x hx => Or.inr hx⟩
    have hyB : y ∈ M.choiceB (M.buyer y) (insert y A') :=
      hchB hins' ⟨hyB0, Set.mem_insert _ _⟩
    exact hyA' (M.not_blocking_singleton hA' hyB hyS)
  show M.choiceS s (A' ∪ A) = M.sellerSide s A'
  rw [← hcons.2 s key (fun x hx => Or.inl hx), hA'.1.2 s]

/-- `←`, buyer coordinate.  Substitutability rejects all of `A \ A'` from
`A ∪ A'` and hence from any larger menu; IRC then collapses
`Cˢ(x + (A' ∪ A))` to `Cˢ(x + A')`, and one Chernoff step lands in
`insert x A`.  No stability is used. -/
theorem toBuyers_subset_of_sellerChosen {A A' : Set X}
    (h : M.SellerChosen A' A) : M.toBuyers A' ⊆ M.toBuyers A := by
  intro x hx
  have hxA' : x ∈ M.choiceS (M.seller x) (insert x A') := hx
  have hch : (M.choiceS (M.seller x)).Chernoff :=
    ChoiceFunction.substitutable_iff_chernoff.mp (hsub.2 (M.seller x))
  have hkey : M.choiceS (M.seller x) (insert x (A' ∪ A)) ⊆ insert x A' := by
    intro y hy
    rcases eq_or_ne y x with rfl | hyx
    · exact Set.mem_insert _ _
    · have hyW : y ∈ insert x (A' ∪ A) :=
        (M.choiceS (M.seller x)).choose_subset _ hy
      have hyU : y ∈ A' ∪ A := (Set.mem_insert_iff.mp hyW).resolve_left hyx
      have hy' : y ∈ M.choiceS (M.seller x) (A' ∪ A) :=
        hch (Set.subset_insert _ _) ⟨hy, hyU⟩
      rw [h (M.seller x)] at hy'
      exact Set.mem_insert_of_mem _ hy'.1
  have e : M.choiceS (M.seller x) (insert x A')
      = M.choiceS (M.seller x) (insert x (A' ∪ A)) :=
    hcons.2 (M.seller x) hkey (Set.insert_subset_insert (fun y hy => Or.inl hy))
  have hxW : x ∈ M.choiceS (M.seller x) (insert x (A' ∪ A)) := by
    rw [← e]; exact hxA'
  show x ∈ M.choiceS (M.seller x) (insert x A)
  exact hch (Set.insert_subset_insert (fun y hy => Or.inr hy))
    ⟨hxW, Set.mem_insert _ _⟩

/-- `←`, seller coordinate: the mirror image. -/
theorem toSellers_subset_of_buyerChosen {A A' : Set X}
    (h : M.BuyerChosen A A') : M.toSellers A ⊆ M.toSellers A' := by
  intro x hx
  have hxA : x ∈ M.choiceB (M.buyer x) (insert x A) := hx
  have hch : (M.choiceB (M.buyer x)).Chernoff :=
    ChoiceFunction.substitutable_iff_chernoff.mp (hsub.1 (M.buyer x))
  have hkey : M.choiceB (M.buyer x) (insert x (A ∪ A')) ⊆ insert x A := by
    intro y hy
    rcases eq_or_ne y x with rfl | hyx
    · exact Set.mem_insert _ _
    · have hyW : y ∈ insert x (A ∪ A') :=
        (M.choiceB (M.buyer x)).choose_subset _ hy
      have hyU : y ∈ A ∪ A' := (Set.mem_insert_iff.mp hyW).resolve_left hyx
      have hy' : y ∈ M.choiceB (M.buyer x) (A ∪ A') :=
        hch (Set.subset_insert _ _) ⟨hy, hyU⟩
      rw [h (M.buyer x)] at hy'
      exact Set.mem_insert_of_mem _ hy'.1
  have e : M.choiceB (M.buyer x) (insert x A)
      = M.choiceB (M.buyer x) (insert x (A ∪ A')) :=
    hcons.1 (M.buyer x) hkey (Set.insert_subset_insert (fun y hy => Or.inl hy))
  have hxW : x ∈ M.choiceB (M.buyer x) (insert x (A ∪ A')) := by
    rw [← e]; exact hxA
  show x ∈ M.choiceB (M.buyer x) (insert x A')
  exact hch (Set.insert_subset_insert (fun y hy => Or.inr hy))
    ⟨hxW, Set.mem_insert _ _⟩

/-- `←`: unanimous seller choice implies the state inequality. -/
theorem le_of_sellerChosen_outcomeOf {p q : Set X × (Set X)ᵒᵈ}
    (hp : IsFixedPt M.daFun p) (hq : IsFixedPt M.daFun q)
    (h : M.SellerChosen (M.outcomeOf q) (M.outcomeOf p)) : p ≤ q := by
  have hA : M.Stable (M.outcomeOf p) := M.stable_outcomeOf hsub hcons hp
  have hbc : M.BuyerChosen (M.outcomeOf p) (M.outcomeOf q) :=
    M.buyerChosen_of_sellerChosen hsub hcons hA h
  have h1 : M.toSellers (M.outcomeOf p) ⊆ M.toSellers (M.outcomeOf q) :=
    M.toSellers_subset_of_buyerChosen hsub hcons hbc
  have h2 : M.toBuyers (M.outcomeOf q) ⊆ M.toBuyers (M.outcomeOf p) :=
    M.toBuyers_subset_of_sellerChosen hsub hcons h
  refine ⟨?_, ?_⟩
  · rw [← M.toSellers_outcomeOf hsub hcons hp,
      ← M.toSellers_outcomeOf hsub hcons hq]
    exact h1
  · show (ofDual q.2 : Set X) ⊆ (ofDual p.2 : Set X)
    rw [← M.toBuyers_outcomeOf hsub hcons hp,
      ← M.toBuyers_outcomeOf hsub hcons hq]
    exact h2

/-- **The order dictionary, seller form.**  The lattice order *is* unanimous
seller choice. -/
theorem le_iff_sellerChosen_outcomeOf {p q : Set X × (Set X)ᵒᵈ}
    (hp : IsFixedPt M.daFun p) (hq : IsFixedPt M.daFun q) :
    p ≤ q ↔ M.SellerChosen (M.outcomeOf q) (M.outcomeOf p) :=
  ⟨M.sellerChosen_outcomeOf_of_le hsub hcons hq,
   M.le_of_sellerChosen_outcomeOf hsub hcons hp hq⟩

/-- **The order dictionary, buyer form.**  The same order is the *reverse* of
unanimous buyer choice. -/
theorem le_iff_buyerChosen_outcomeOf {p q : Set X × (Set X)ᵒᵈ}
    (hp : IsFixedPt M.daFun p) (hq : IsFixedPt M.daFun q) :
    p ≤ q ↔ M.BuyerChosen (M.outcomeOf p) (M.outcomeOf q) :=
  ⟨M.buyerChosen_outcomeOf_of_le hsub hcons hp,
   fun h => M.le_of_sellerChosen_outcomeOf hsub hcons hp hq
     (M.sellerChosen_of_buyerChosen hsub hcons
       (M.stable_outcomeOf hsub hcons hq) h)⟩

/-- Opposition of interests, packaged: on stable outcomes the two unanimity
statements are the same statement. -/
theorem sellerChosen_iff_buyerChosen {A A' : Set X} (hA : M.Stable A)
    (hA' : M.Stable A') : M.SellerChosen A' A ↔ M.BuyerChosen A A' :=
  ⟨M.buyerChosen_of_sellerChosen hsub hcons hA,
   M.sellerChosen_of_buyerChosen hsub hcons hA'⟩

end OrderDictionary

/-! ### The extremal outcomes

Seller-optimality and buyer-pessimality of `gfp` (and the duals at `lfp`) are
now instances of the dictionary at `q := gfp`, not separate arguments. -/

theorem sellerChosen_sellerOptimal (hsub : M.Substitutable)
    (hcons : M.Consistent) {A : Set X} (hA : M.Stable A) :
    M.SellerChosen (M.sellerOptimal hsub) A := by
  have hp : IsFixedPt M.daFun (M.stateOf A) := M.isFixedPt_stateOf hsub hcons hA
  have h := M.sellerChosen_outcomeOf_of_le hsub hcons
    (M.isFixedPt_gfp_daHom hsub) (M.le_gfp_daHom hsub hp)
  rw [M.outcomeOf_stateOf hsub hcons hA] at h
  exact h

/-- Buyer-pessimality of the seller-optimal outcome: every stable `A` is
buyer-chosen over it. -/
theorem buyerChosen_sellerOptimal (hsub : M.Substitutable)
    (hcons : M.Consistent) {A : Set X} (hA : M.Stable A) :
    M.BuyerChosen A (M.sellerOptimal hsub) := by
  have hp : IsFixedPt M.daFun (M.stateOf A) := M.isFixedPt_stateOf hsub hcons hA
  have h := M.buyerChosen_outcomeOf_of_le hsub hcons hp
    (M.le_gfp_daHom hsub hp)
  rw [M.outcomeOf_stateOf hsub hcons hA] at h
  exact h

theorem buyerChosen_buyerOptimal (hsub : M.Substitutable)
    (hcons : M.Consistent) {A : Set X} (hA : M.Stable A) :
    M.BuyerChosen (M.buyerOptimal hsub) A := by
  have hq : IsFixedPt M.daFun (M.stateOf A) := M.isFixedPt_stateOf hsub hcons hA
  have h := M.buyerChosen_outcomeOf_of_le hsub hcons
    (M.isFixedPt_lfp_daHom hsub) (M.lfp_le_daHom hsub hq)
  rw [M.outcomeOf_stateOf hsub hcons hA] at h
  exact h

theorem sellerChosen_buyerOptimal (hsub : M.Substitutable)
    (hcons : M.Consistent) {A : Set X} (hA : M.Stable A) :
    M.SellerChosen A (M.buyerOptimal hsub) := by
  have hq : IsFixedPt M.daFun (M.stateOf A) := M.isFixedPt_stateOf hsub hcons hA
  have h := M.sellerChosen_outcomeOf_of_le hsub hcons hq
    (M.lfp_le_daHom hsub hq)
  rw [M.outcomeOf_stateOf hsub hcons hA] at h
  exact h

/-! ### The lattice of fixed points and its stable-outcome interpretation

Using fixed points as the carrier inherits mathlib's `CompleteLattice`
instance directly. `StableOutcomes hsub` exists with substitutability alone;
its interpretation as stable outcomes, and injectivity of `outcome`, require
IRC. All economic statements below expose that additional hypothesis.

The lattice operations need not agree with ambient componentwise operations.
The API uses the order characterization rather than unfolding those operations.
-/

/-- The Knaster–Tarski lattice of stable outcomes, carried by the fixed points
of the deferred-acceptance operator.  Reducible, so that the `CompleteLattice`
instance on `fixedPoints` applies. -/
abbrev StableOutcomes (M : Market B S X) (hsub : M.Substitutable) : Type w :=
  fixedPoints (M.daHom hsub)

/-- Package a stable outcome as a lattice element. -/
def ofStable (hsub : M.Substitutable) (hcons : M.Consistent) {A : Set X}
    (hA : M.Stable A) : M.StableOutcomes hsub :=
  ⟨M.stateOf A, M.isFixedPt_stateOf hsub hcons hA⟩

section StableOutcomesAPI

variable {M}

namespace StableOutcomes

variable {hsub : M.Substitutable}

/-- The state of a lattice element. -/
def state (A : M.StableOutcomes hsub) : Set X × (Set X)ᵒᵈ := A.1

theorem isFixedPt (A : M.StableOutcomes hsub) : IsFixedPt M.daFun A.state := A.2

/-- The outcome of a lattice element. -/
def outcome (A : M.StableOutcomes hsub) : Set X := M.outcomeOf A.state

theorem stable (A : M.StableOutcomes hsub) (hcons : M.Consistent) :
    M.Stable A.outcome :=
  M.stable_outcomeOf hsub hcons A.isFixedPt

theorem state_eq_stateOf (A : M.StableOutcomes hsub) (hcons : M.Consistent) :
    A.state = M.stateOf A.outcome :=
  (M.stateOf_outcomeOf hsub hcons A.isFixedPt).symm

/-- The inherited lattice order is the subtype order on states. -/
@[simp] theorem le_iff_state_le {A A' : M.StableOutcomes hsub} :
    A ≤ A' ↔ A.state ≤ A'.state := Iff.rfl

theorem state_injective :
    Function.Injective (fun A : M.StableOutcomes hsub => A.state) :=
  fun _ _ h => Subtype.ext h

theorem outcome_injective (hcons : M.Consistent) :
    Function.Injective (fun A : M.StableOutcomes hsub => A.outcome) := by
  intro A A' hout
  apply state_injective
  calc
    A.state = M.stateOf A.outcome := A.state_eq_stateOf hcons
    _ = M.stateOf A'.outcome := congrArg M.stateOf hout
    _ = A'.state := (A'.state_eq_stateOf hcons).symm

/-- The order dictionary on the lattice: `≤` is unanimous seller choice. -/
theorem le_iff_sellerChosen (hcons : M.Consistent)
    {A A' : M.StableOutcomes hsub} :
    A ≤ A' ↔ M.SellerChosen A'.outcome A.outcome :=
  M.le_iff_sellerChosen_outcomeOf hsub hcons A.isFixedPt A'.isFixedPt

/-- …and the reverse of unanimous buyer choice. -/
theorem le_iff_buyerChosen (hcons : M.Consistent)
    {A A' : M.StableOutcomes hsub} :
    A ≤ A' ↔ M.BuyerChosen A.outcome A'.outcome :=
  M.le_iff_buyerChosen_outcomeOf hsub hcons A.isFixedPt A'.isFixedPt

end StableOutcomes

end StableOutcomesAPI

/-- Lemma 2.1, packaged as an equivalence with the lattice carrier. -/
def stableEquivFixedPoints (hsub : M.Substitutable)
    (hcons : M.Consistent) :
    {A : Set X // M.Stable A} ≃ M.StableOutcomes hsub where
  toFun A := M.ofStable hsub hcons A.2
  invFun p := ⟨p.outcome, p.stable hcons⟩
  left_inv A := Subtype.ext (M.outcomeOf_stateOf hsub hcons A.2)
  right_inv p := Subtype.ext (M.stateOf_outcomeOf hsub hcons p.isFixedPt)

@[simp] theorem outcome_ofStable (hsub : M.Substitutable) (hcons : M.Consistent)
    {A : Set X} (hA : M.Stable A) :
    (M.ofStable hsub hcons hA).outcome = A :=
  M.outcomeOf_stateOf hsub hcons hA

/-! #### Orientation

`⊤` is seller-optimal and buyer-pessimal.  This is the one fact in the file
that is a coin flip fixed by which coordinate carries the `ᵒᵈ`; state it once,
here, and route every downstream result through the two abbreviations rather
than through bare `⊤`/`⊥`. -/

/-- The **seller-optimal** stable outcome: the top of the lattice. -/
abbrev sellerOptimalOutcome (M : Market B S X) (hsub : M.Substitutable) :
    M.StableOutcomes hsub := ⊤

/-- The **buyer-optimal** stable outcome: the bottom of the lattice. -/
abbrev buyerOptimalOutcome (M : Market B S X) (hsub : M.Substitutable) :
    M.StableOutcomes hsub := ⊥

/-- The top fixed point is the greatest fixed point of the DA operator. -/
theorem state_sellerOptimalOutcome (hsub : M.Substitutable) :
    (M.sellerOptimalOutcome hsub).state = OrderHom.gfp (M.daHom hsub) := by
  refine le_antisymm ?_ ?_
  · exact (M.daHom hsub).isGreatest_gfp.2 (M.sellerOptimalOutcome hsub).isFixedPt
  · exact le_top (a := (⟨OrderHom.gfp (M.daHom hsub),
      M.isFixedPt_gfp_daHom hsub⟩ : M.StableOutcomes hsub))

theorem state_buyerOptimalOutcome (hsub : M.Substitutable) :
    (M.buyerOptimalOutcome hsub).state = OrderHom.lfp (M.daHom hsub) := by
  refine le_antisymm ?_ ?_
  · exact bot_le (a := (⟨OrderHom.lfp (M.daHom hsub),
      M.isFixedPt_lfp_daHom hsub⟩ : M.StableOutcomes hsub))
  · exact (M.daHom hsub).isLeast_lfp.2 (M.buyerOptimalOutcome hsub).isFixedPt

theorem outcome_sellerOptimalOutcome (hsub : M.Substitutable) :
    (M.sellerOptimalOutcome hsub).outcome = M.sellerOptimal hsub :=
  congrArg M.outcomeOf (M.state_sellerOptimalOutcome hsub)

theorem outcome_buyerOptimalOutcome (hsub : M.Substitutable) :
    (M.buyerOptimalOutcome hsub).outcome = M.buyerOptimal hsub :=
  congrArg M.outcomeOf (M.state_buyerOptimalOutcome hsub)

/-- Seller-optimality, lattice form. -/
theorem sellerChosen_sellerOptimalOutcome (hsub : M.Substitutable)
    (hcons : M.Consistent) (A : M.StableOutcomes hsub) :
    M.SellerChosen (M.sellerOptimalOutcome hsub).outcome A.outcome :=
  (StableOutcomes.le_iff_sellerChosen hcons).mp le_top

/-- Buyer-pessimality, lattice form. -/
theorem buyerChosen_sellerOptimalOutcome (hsub : M.Substitutable)
    (hcons : M.Consistent) (A : M.StableOutcomes hsub) :
    M.BuyerChosen A.outcome (M.sellerOptimalOutcome hsub).outcome :=
  (StableOutcomes.le_iff_buyerChosen hcons).mp le_top

theorem buyerChosen_buyerOptimalOutcome (hsub : M.Substitutable)
    (hcons : M.Consistent) (A : M.StableOutcomes hsub) :
    M.BuyerChosen (M.buyerOptimalOutcome hsub).outcome A.outcome :=
  (StableOutcomes.le_iff_buyerChosen hcons).mp bot_le

theorem sellerChosen_buyerOptimalOutcome (hsub : M.Substitutable)
    (hcons : M.Consistent) (A : M.StableOutcomes hsub) :
    M.SellerChosen A.outcome (M.buyerOptimalOutcome hsub).outcome :=
  (StableOutcomes.le_iff_sellerChosen hcons).mp bot_le

/-! ### Ambient and fixed-point lattice operations

Monotonicity makes the ambient join of two fixed points post-fixed and their
ambient meet pre-fixed. Equality with the join or meet in the fixed-point
lattice requires a separate closure proof; the two conditional theorems
below make that premise explicit. No closure theorem or counterexample is
asserted here. In particular, a hypothetical configuration for one agent
alone does not establish a counterexample in a market with two stable outcomes.
-/

/-- The componentwise join of two fixed points is a post-fixed point. -/
theorem le_daFun_sup (hsub : M.Substitutable) {p q : Set X × (Set X)ᵒᵈ}
    (hp : IsFixedPt M.daFun p) (hq : IsFixedPt M.daFun q) :
    p ⊔ q ≤ M.daFun (p ⊔ q) := by
  refine sup_le ?_ ?_
  · calc p = M.daFun p := hp.symm
      _ ≤ M.daFun (p ⊔ q) := M.monotone_daFun hsub le_sup_left
  · calc q = M.daFun q := hq.symm
      _ ≤ M.daFun (p ⊔ q) := M.monotone_daFun hsub le_sup_right

/-- The componentwise meet of two fixed points is a pre-fixed point. -/
theorem daFun_inf_le (hsub : M.Substitutable) {p q : Set X × (Set X)ᵒᵈ}
    (hp : IsFixedPt M.daFun p) (hq : IsFixedPt M.daFun q) :
    M.daFun (p ⊓ q) ≤ p ⊓ q := by
  refine le_inf ?_ ?_
  · calc M.daFun (p ⊓ q) ≤ M.daFun p := M.monotone_daFun hsub inf_le_left
      _ = p := hp
  · calc M.daFun (p ⊓ q) ≤ M.daFun q := M.monotone_daFun hsub inf_le_right
      _ = q := hq

/-- *If* the componentwise join is a fixed point, it is the lattice join.
The closure hypothesis is explicit; specialized models may discharge it. -/
theorem state_sup_of_isFixedPt {hsub : M.Substitutable}
    {A A' : M.StableOutcomes hsub}
    (h : IsFixedPt M.daFun (A.state ⊔ A'.state)) :
    (A ⊔ A').state = A.state ⊔ A'.state := by
  let C : M.StableOutcomes hsub := ⟨A.state ⊔ A'.state, h⟩

  have hAC : A ≤ C := by
    change A.state ≤ A.state ⊔ A'.state
    exact le_sup_left

  have hA'C : A' ≤ C := by
    change A'.state ≤ A.state ⊔ A'.state
    exact le_sup_right

  have hjoinC : A ⊔ A' ≤ C :=
    sup_le hAC hA'C

  have hCjoin : C ≤ A ⊔ A' := by
    change A.state ⊔ A'.state ≤ (A ⊔ A').state
    refine sup_le ?_ ?_
    · exact (le_sup_left : A ≤ A ⊔ A')
    · exact (le_sup_right : A' ≤ A ⊔ A')

  have heq : A ⊔ A' = C :=
    le_antisymm hjoinC hCjoin

  simpa [C] using congrArg StableOutcomes.state heq

/-- Dual of `state_sup_of_isFixedPt`. -/
theorem state_inf_of_isFixedPt {hsub : M.Substitutable}
    {A A' : M.StableOutcomes hsub}
    (h : IsFixedPt M.daFun (A.state ⊓ A'.state)) :
    (A ⊓ A').state = A.state ⊓ A'.state := by
  let C : M.StableOutcomes hsub := ⟨A.state ⊓ A'.state, h⟩

  have hCA : C ≤ A := by
    change A.state ⊓ A'.state ≤ A.state
    exact inf_le_left

  have hCA' : C ≤ A' := by
    change A.state ⊓ A'.state ≤ A'.state
    exact inf_le_right

  have hCinf : C ≤ A ⊓ A' :=
    le_inf hCA hCA'

  have hinfC : A ⊓ A' ≤ C := by
    change (A ⊓ A').state ≤ A.state ⊓ A'.state
    refine le_inf ?_ ?_
    · exact (inf_le_left : A ⊓ A' ≤ A)
    · exact (inf_le_right : A ⊓ A' ≤ A')

  have heq : A ⊓ A' = C :=
    le_antisymm hinfC hCinf

  simpa [C] using congrArg StableOutcomes.state heq

end Market
