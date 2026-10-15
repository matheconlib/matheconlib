import MathEconLib.Matching.Contracts.StableFixedPoints
import MathEconLib.ForMathlib.Order.FixedPointLattice

/-!
# The order and lattice of stable outcomes

Under substitutability and IRC, the fixed-point order corresponds to unanimous
seller choice and reverse unanimous buyer choice. This yields both
side-optimality results without finiteness, unit demand, or the law of
aggregate demand.
The complete lattice is carried by the operator's fixed points;
`stableEquivFixedPoints` identifies this carrier with stable contract sets.

## References

HKSurvey2025: John William Hatfield and Scott Duke Kominers, *The theory of
matching with contracts*, Chapter 5, Handbook of the Economics of Matching
**2** (2025), 409–487. Theorem 3.2 (p. 440) states the many-to-many
choice-order lattice and the opposing optimal/pessimal endpoints.
https://doi.org/10.1016/bs.hesmat.2025.10.005

HKContractDesign2017: John William Hatfield and Scott Duke Kominers,
*Contract design and stability in many-to-many matching*, Games and Economic
Behavior **101** (2017), 78–97. Lemma 1 (p. 87) gives the fixed-point
correspondence. Theorem 1 and the following paragraph (p. 87) give a
preference-order lattice and opposition of interests. Here the lattice uses
choice relations; no general bridge from primitive preferences is formalized.
https://doi.org/10.1016/j.geb.2016.01.002
-/

namespace MathEconLib.Matching

open MathEconLib.Choice

open Function OrderDual

universe u v w

variable {B : Type u} {S : Type v} {X : Type w}

namespace Market

variable (M : Market B S X)

/-! ### The order dictionary

For fixed points `p` and `q`, under substitutability and IRC, the three statements

* `p ≤ q` in the state lattice,
* `SellerChosen (outcomeOf q) (outcomeOf p)` — every seller chooses their part
  of the `q`-outcome out of the union,
* `BuyerChosen (outcomeOf p) (outcomeOf q)` — every buyer chooses their part
  of the `p`-outcome out of the union,

are equivalent. This is opposition of interests expressed through choice
functions. The market structure has no primitive preferences over sets.
In a preference-induced unit-demand model, the seller-choice relation can
also be read as each seller weakly preferring their assigned contract; the
marriage layer proves that interpretation separately.

None of this uses `SizeMonotone`. -/

/-- IRC and a fixed point suffice for the forward seller-order implication.
Only the first state coordinate is used; the smaller state need not be fixed. -/
theorem sellerChosen_outcomeOf_of_le_of_consistent (hcons : M.Consistent)
    {p q : Set X × (Set X)ᵒᵈ} (hq : IsFixedPt M.deferredAcceptanceOperator q) (h : p ≤ q) :
    M.SellerChosen (M.outcomeOf q) (M.outcomeOf p) := by
  intro s
  have hop : M.outcomeOf p ⊆ q.1 := fun _ hx => h.1 hx.1
  have hoq : M.outcomeOf q ⊆ q.1 := fun _ hx => hx.1
  have e1 := M.choiceS_eq_of_isFixedPt_sandwich hcons hq s
    (Set.subset_union_left : M.outcomeOf q ⊆ M.outcomeOf q ∪ M.outcomeOf p)
    (Set.union_subset hoq hop)
  have e2 := M.choiceS_eq_of_isFixedPt_sandwich hcons hq s (subset_refl _) hoq
  show M.choiceS s (M.outcomeOf q ∪ M.outcomeOf p) = M.sellerSide s (M.outcomeOf q)
  rw [e1, ← e2]
  exact (M.indRational_outcomeOf hcons hq).2 s

/-- IRC and a fixed point suffice for the forward buyer-order implication.
Only the dual second coordinate is used; the larger state need not be fixed. -/
theorem buyerChosen_outcomeOf_of_le_of_consistent (hcons : M.Consistent)
    {p q : Set X × (Set X)ᵒᵈ} (hp : IsFixedPt M.deferredAcceptanceOperator p) (h : p ≤ q) :
    M.BuyerChosen (M.outcomeOf p) (M.outcomeOf q) := by
  intro b
  have hop : M.outcomeOf p ⊆ (ofDual p.2 : Set X) := fun _ hx => hx.2
  have hoq : M.outcomeOf q ⊆ (ofDual p.2 : Set X) := fun _ hx => h.2 hx.2
  have e1 := M.choiceB_eq_of_isFixedPt_sandwich hcons hp b
    (Set.subset_union_left : M.outcomeOf p ⊆ M.outcomeOf p ∪ M.outcomeOf q)
    (Set.union_subset hop hoq)
  have e2 := M.choiceB_eq_of_isFixedPt_sandwich hcons hp b (subset_refl _) hop
  show M.choiceB b (M.outcomeOf p ∪ M.outcomeOf q) = M.buyerSide b (M.outcomeOf p)
  rw [e1, ← e2]
  exact (M.indRational_outcomeOf hcons hp).1 b

section OrderDictionary

variable (hsub : M.Substitutable) (hcons : M.Consistent)

include hsub hcons

omit hsub in
/-- Compatibility form of `sellerChosen_outcomeOf_of_le_of_consistent`. -/
theorem sellerChosen_outcomeOf_of_le {p q : Set X × (Set X)ᵒᵈ}
    (hq : IsFixedPt M.deferredAcceptanceOperator q) (h : p ≤ q) :
    M.SellerChosen (M.outcomeOf q) (M.outcomeOf p) :=
  M.sellerChosen_outcomeOf_of_le_of_consistent hcons hq h

omit hsub in
/-- Compatibility form of `buyerChosen_outcomeOf_of_le_of_consistent`. -/
theorem buyerChosen_outcomeOf_of_le {p q : Set X × (Set X)ᵒᵈ}
    (hp : IsFixedPt M.deferredAcceptanceOperator p) (h : p ≤ q) :
    M.BuyerChosen (M.outcomeOf p) (M.outcomeOf q) :=
  M.buyerChosen_outcomeOf_of_le_of_consistent hcons hp h

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

/-- Unanimous seller choice identifies the choices from `A' ∪ A` and `A'`.
Path independence preserves this equality after inserting a contract, and
substitutability contracts the menu to `insert x A`. No stability is used. -/
theorem toBuyers_subset_of_sellerChosen {A A' : Set X}
    (h : M.SellerChosen A' A) : M.toBuyers A' ⊆ M.toBuyers A := by
  intro x hx
  have hchoice : M.choiceS (M.seller x) (A' ∪ A) ⊆ A' := by
    rw [h (M.seller x)]
    exact M.sellerSide_subset _ _
  have heq := hcons.2 (M.seller x) hchoice (fun _ hy => Or.inl hy)
  have hpi := (hsub.2 (M.seller x)).pathIndependent (hcons.2 (M.seller x))
  have hins : M.choiceS (M.seller x) (insert x A') =
      M.choiceS (M.seller x) (insert x (A' ∪ A)) := by
    simpa only [Set.union_singleton] using hpi.union_congr_left heq ({x} : Set X)
  have hxU : x ∈ M.choiceS (M.seller x) (insert x (A' ∪ A)) := by
    rw [← hins]
    exact hx
  exact (hsub.2 (M.seller x)).mem_insert_of_subset (fun _ hy => Or.inr hy) hxU

/-- The buyer-choice counterpart of `toBuyers_subset_of_sellerChosen`. -/
theorem toSellers_subset_of_buyerChosen {A A' : Set X}
    (h : M.BuyerChosen A A') : M.toSellers A ⊆ M.toSellers A' := by
  intro x hx
  have hchoice : M.choiceB (M.buyer x) (A ∪ A') ⊆ A := by
    rw [h (M.buyer x)]
    exact M.buyerSide_subset _ _
  have heq := hcons.1 (M.buyer x) hchoice (fun _ hy => Or.inl hy)
  have hpi := (hsub.1 (M.buyer x)).pathIndependent (hcons.1 (M.buyer x))
  have hins : M.choiceB (M.buyer x) (insert x A) =
      M.choiceB (M.buyer x) (insert x (A ∪ A')) := by
    simpa only [Set.union_singleton] using hpi.union_congr_left heq ({x} : Set X)
  have hxU : x ∈ M.choiceB (M.buyer x) (insert x (A ∪ A')) := by
    rw [← hins]
    exact hx
  exact (hsub.1 (M.buyer x)).mem_insert_of_subset (fun _ hy => Or.inr hy) hxU

/-- `←`: unanimous seller choice implies the state inequality. -/
theorem le_of_sellerChosen_outcomeOf {p q : Set X × (Set X)ᵒᵈ}
    (hp : IsFixedPt M.deferredAcceptanceOperator p) (hq : IsFixedPt M.deferredAcceptanceOperator q)
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
    (hp : IsFixedPt M.deferredAcceptanceOperator p) (hq : IsFixedPt M.deferredAcceptanceOperator q) :
    p ≤ q ↔ M.SellerChosen (M.outcomeOf q) (M.outcomeOf p) :=
  ⟨M.sellerChosen_outcomeOf_of_le_of_consistent hcons hq,
   M.le_of_sellerChosen_outcomeOf hsub hcons hp hq⟩

/-- **The order dictionary, buyer form.**  The same order is the *reverse* of
unanimous buyer choice. -/
theorem le_iff_buyerChosen_outcomeOf {p q : Set X × (Set X)ᵒᵈ}
    (hp : IsFixedPt M.deferredAcceptanceOperator p) (hq : IsFixedPt M.deferredAcceptanceOperator q) :
    p ≤ q ↔ M.BuyerChosen (M.outcomeOf p) (M.outcomeOf q) :=
  ⟨M.buyerChosen_outcomeOf_of_le_of_consistent hcons hp,
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
    M.SellerChosen (M.sellerOptimal hsub hcons) A := by
  have hp : IsFixedPt M.deferredAcceptanceOperator (M.stateOf A) := M.isFixedPt_stateOf hsub hcons hA
  have h := M.sellerChosen_outcomeOf_of_le_of_consistent hcons
    (M.isFixedPt_gfp_deferredAcceptanceOrderHom hsub) (M.le_gfp_deferredAcceptanceOrderHom hsub hp)
  rw [M.outcomeOf_stateOf_of_stable hA] at h
  exact h

/-- Buyer-pessimality of the seller-optimal outcome: every stable `A` is
buyer-chosen over it. -/
theorem buyerChosen_sellerOptimal (hsub : M.Substitutable)
    (hcons : M.Consistent) {A : Set X} (hA : M.Stable A) :
    M.BuyerChosen A (M.sellerOptimal hsub hcons) := by
  have hp : IsFixedPt M.deferredAcceptanceOperator (M.stateOf A) := M.isFixedPt_stateOf hsub hcons hA
  have h := M.buyerChosen_outcomeOf_of_le_of_consistent hcons hp
    (M.le_gfp_deferredAcceptanceOrderHom hsub hp)
  rw [M.outcomeOf_stateOf_of_stable hA] at h
  exact h

theorem buyerChosen_buyerOptimal (hsub : M.Substitutable)
    (hcons : M.Consistent) {A : Set X} (hA : M.Stable A) :
    M.BuyerChosen (M.buyerOptimal hsub hcons) A := by
  have hq : IsFixedPt M.deferredAcceptanceOperator (M.stateOf A) := M.isFixedPt_stateOf hsub hcons hA
  have h := M.buyerChosen_outcomeOf_of_le_of_consistent hcons
    (M.isFixedPt_lfp_deferredAcceptanceOrderHom hsub) (M.lfp_le_deferredAcceptanceOrderHom hsub hq)
  rw [M.outcomeOf_stateOf_of_stable hA] at h
  exact h

theorem sellerChosen_buyerOptimal (hsub : M.Substitutable)
    (hcons : M.Consistent) {A : Set X} (hA : M.Stable A) :
    M.SellerChosen A (M.buyerOptimal hsub hcons) := by
  have hq : IsFixedPt M.deferredAcceptanceOperator (M.stateOf A) := M.isFixedPt_stateOf hsub hcons hA
  have h := M.sellerChosen_outcomeOf_of_le_of_consistent hcons hq
    (M.lfp_le_deferredAcceptanceOrderHom hsub hq)
  rw [M.outcomeOf_stateOf_of_stable hA] at h
  exact h

/-! ### The lattice of fixed points and its stable-outcome interpretation

`FixedPointStates hsub` inherits mathlib's `CompleteLattice` instance without
IRC. The economic interface `StableOutcomes hsub hcons` also requests IRC,
which ensures that every carried outcome is stable and uniquely determines
its state. This is a reducible abbreviation of the same carrier, so its proof
parameter is an API convention, not a distinct type-level restriction.

The lattice operations need not agree with ambient componentwise operations.
The API uses the order characterization rather than unfolding those operations.
-/

/-- The Knaster–Tarski lattice of deferred-acceptance fixed points.
No IRC assumption is needed for this order-theoretic carrier. -/
abbrev FixedPointStates (M : Market B S X) (hsub : M.Substitutable) : Type w :=
  fixedPoints (M.deferredAcceptanceOrderHom hsub)

/-- The stable-outcome interface to the fixed-point lattice.
IRC gives the economic interpretation. The carrier and its complete lattice
are definitionally those of `FixedPointStates`; the extra proof parameter
records the assumptions expected at this interface. -/
abbrev StableOutcomes (M : Market B S X) (hsub : M.Substitutable)
    (_hcons : M.Consistent) : Type w :=
  M.FixedPointStates hsub

section FixedPointStatesAPI

variable {M}

namespace FixedPointStates

variable {hsub : M.Substitutable}

/-- The state of a fixed-point lattice element. -/
def state (A : M.FixedPointStates hsub) : Set X × (Set X)ᵒᵈ := A.1

theorem isFixedPt (A : M.FixedPointStates hsub) : IsFixedPt M.deferredAcceptanceOperator A.state := A.2

/-- The contract set carried by a fixed point; its stability requires IRC. -/
def outcome (A : M.FixedPointStates hsub) : Set X := M.outcomeOf A.state

/-- The inherited lattice order is the subtype order on states. -/
@[simp] theorem le_iff_state_le {A A' : M.FixedPointStates hsub} :
    A ≤ A' ↔ A.state ≤ A'.state := Iff.rfl

theorem state_injective :
    Function.Injective (fun A : M.FixedPointStates hsub => A.state) :=
  fun _ _ h => Subtype.ext h

end FixedPointStates

end FixedPointStatesAPI

/-- Package a stable outcome as a lattice element. -/
def ofStable (hsub : M.Substitutable) (hcons : M.Consistent) {A : Set X}
    (hA : M.Stable A) : M.StableOutcomes hsub hcons :=
  ⟨M.stateOf A, M.isFixedPt_stateOf hsub hcons hA⟩

section StableOutcomesAPI

variable {M}

namespace StableOutcomes

variable {hsub : M.Substitutable}

section Accessors

variable {hcons : M.Consistent}

-- Field notation needs a parameter whose declared type is `StableOutcomes`.
-- Keep these wrappers while retaining the separate, IRC-free raw accessors.
/-- The state of a stable-outcome lattice element. -/
def state (A : M.StableOutcomes hsub hcons) : Set X × (Set X)ᵒᵈ :=
  FixedPointStates.state A

theorem isFixedPt (A : M.StableOutcomes hsub hcons) : IsFixedPt M.deferredAcceptanceOperator A.state :=
  FixedPointStates.isFixedPt A

/-- The contract set carried by a stable-outcome lattice element. -/
def outcome (A : M.StableOutcomes hsub hcons) : Set X :=
  FixedPointStates.outcome A

/-- The inherited lattice order is the subtype order on states. -/
@[simp] theorem le_iff_state_le {A A' : M.StableOutcomes hsub hcons} :
    A ≤ A' ↔ A.state ≤ A'.state := Iff.rfl

theorem state_injective :
    Function.Injective (fun A : M.StableOutcomes hsub hcons => A.state) :=
  fun _ _ h => Subtype.ext h

end Accessors

/-- Individual rationality uses only IRC once the state is known to be fixed. -/
theorem indRational (hcons : M.Consistent) (A : M.StableOutcomes hsub hcons) :
    M.IndRational A.outcome :=
  M.indRational_outcomeOf hcons A.isFixedPt

theorem stable (hcons : M.Consistent) (A : M.StableOutcomes hsub hcons) :
    M.Stable A.outcome :=
  M.stable_outcomeOf hsub hcons A.isFixedPt

theorem state_eq_stateOf (hcons : M.Consistent) (A : M.StableOutcomes hsub hcons) :
    A.state = M.stateOf A.outcome :=
  (M.stateOf_outcomeOf hsub hcons A.isFixedPt).symm

theorem outcome_injective (hcons : M.Consistent) :
    Function.Injective (fun A : M.StableOutcomes hsub hcons => A.outcome) := by
  intro A A' hout
  exact Subtype.ext (M.outcomeOf_injOn_fixedPoints hsub hcons A.isFixedPt A'.isFixedPt hout)

/-- The order dictionary on the lattice: `≤` is unanimous seller choice. -/
theorem le_iff_sellerChosen (hcons : M.Consistent)
    {A A' : M.StableOutcomes hsub hcons} :
    A ≤ A' ↔ M.SellerChosen A'.outcome A.outcome :=
  M.le_iff_sellerChosen_outcomeOf hsub hcons A.isFixedPt A'.isFixedPt

/-- …and the reverse of unanimous buyer choice. -/
theorem le_iff_buyerChosen (hcons : M.Consistent)
    {A A' : M.StableOutcomes hsub hcons} :
    A ≤ A' ↔ M.BuyerChosen A.outcome A'.outcome :=
  M.le_iff_buyerChosen_outcomeOf hsub hcons A.isFixedPt A'.isFixedPt

end StableOutcomes

end StableOutcomesAPI

/-- The fixed-point correspondence, packaged as an equivalence with the
lattice carrier (HKContractDesign2017, Lemma 1, p. 87; see `StableFixedPoints`).
This is an `Equiv`; no preference-order instance is installed on the subtype
of stable contract sets. The order dictionary is supplied separately. -/
def stableEquivFixedPoints (hsub : M.Substitutable)
    (hcons : M.Consistent) :
    {A : Set X // M.Stable A} ≃ M.StableOutcomes hsub hcons where
  toFun A := M.ofStable hsub hcons A.2
  invFun p := ⟨p.outcome, StableOutcomes.stable hcons p⟩
  left_inv A := Subtype.ext (M.outcomeOf_stateOf_of_stable A.2)
  right_inv p := Subtype.ext (M.stateOf_outcomeOf hsub hcons p.isFixedPt)

@[simp] theorem outcome_ofStable (hsub : M.Substitutable) (hcons : M.Consistent)
    {A : Set X} (hA : M.Stable A) :
    (M.ofStable hsub hcons hA).outcome = A :=
  M.outcomeOf_stateOf_of_stable hA

/-! #### Orientation

`⊤` is seller-optimal and buyer-pessimal, while `⊥` is buyer-optimal and
seller-pessimal. This orientation follows from placing `OrderDual` on the
buyer-available coordinate. The named extrema request IRC to expose their
economic interpretation to downstream results. -/

/-- The seller-optimal stable outcome, carried by the greatest fixed point. -/
abbrev sellerOptimalOutcome (M : Market B S X) (hsub : M.Substitutable)
    (hcons : M.Consistent) : M.StableOutcomes hsub hcons := ⊤

/-- The buyer-optimal stable outcome, carried by the least fixed point. -/
abbrev buyerOptimalOutcome (M : Market B S X) (hsub : M.Substitutable)
    (hcons : M.Consistent) : M.StableOutcomes hsub hcons := ⊥

/-- The top fixed point is the greatest fixed point of the deferred-acceptance operator. -/
theorem state_sellerOptimalOutcome (hsub : M.Substitutable) (hcons : M.Consistent) :
    (M.sellerOptimalOutcome hsub hcons).state = OrderHom.gfp (M.deferredAcceptanceOrderHom hsub) :=
  (M.deferredAcceptanceOrderHom hsub).fixedPoints_val_top

/-- The bottom fixed point is the least fixed point of the deferred-acceptance operator. -/
theorem state_buyerOptimalOutcome (hsub : M.Substitutable) (hcons : M.Consistent) :
    (M.buyerOptimalOutcome hsub hcons).state = OrderHom.lfp (M.deferredAcceptanceOrderHom hsub) :=
  (M.deferredAcceptanceOrderHom hsub).fixedPoints_val_bot

theorem outcome_sellerOptimalOutcome (hsub : M.Substitutable) (hcons : M.Consistent) :
    (M.sellerOptimalOutcome hsub hcons).outcome = M.sellerOptimal hsub hcons :=
  congrArg M.outcomeOf (M.state_sellerOptimalOutcome hsub hcons)

theorem outcome_buyerOptimalOutcome (hsub : M.Substitutable) (hcons : M.Consistent) :
    (M.buyerOptimalOutcome hsub hcons).outcome = M.buyerOptimal hsub hcons :=
  congrArg M.outcomeOf (M.state_buyerOptimalOutcome hsub hcons)

/-- Seller-optimality, lattice form. -/
theorem sellerChosen_sellerOptimalOutcome (hsub : M.Substitutable)
    (hcons : M.Consistent) (A : M.StableOutcomes hsub hcons) :
    M.SellerChosen (M.sellerOptimalOutcome hsub hcons).outcome A.outcome :=
  (StableOutcomes.le_iff_sellerChosen hcons).mp le_top

/-- Buyer-pessimality, lattice form. -/
theorem buyerChosen_sellerOptimalOutcome (hsub : M.Substitutable)
    (hcons : M.Consistent) (A : M.StableOutcomes hsub hcons) :
    M.BuyerChosen A.outcome (M.sellerOptimalOutcome hsub hcons).outcome :=
  (StableOutcomes.le_iff_buyerChosen hcons).mp le_top

theorem buyerChosen_buyerOptimalOutcome (hsub : M.Substitutable)
    (hcons : M.Consistent) (A : M.StableOutcomes hsub hcons) :
    M.BuyerChosen (M.buyerOptimalOutcome hsub hcons).outcome A.outcome :=
  (StableOutcomes.le_iff_buyerChosen hcons).mp bot_le

theorem sellerChosen_buyerOptimalOutcome (hsub : M.Substitutable)
    (hcons : M.Consistent) (A : M.StableOutcomes hsub hcons) :
    M.SellerChosen A.outcome (M.buyerOptimalOutcome hsub hcons).outcome :=
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
theorem le_deferredAcceptanceOperator_sup (hsub : M.Substitutable) {p q : Set X × (Set X)ᵒᵈ}
    (hp : IsFixedPt M.deferredAcceptanceOperator p) (hq : IsFixedPt M.deferredAcceptanceOperator q) :
    p ⊔ q ≤ M.deferredAcceptanceOperator (p ⊔ q) :=
  (M.deferredAcceptanceOrderHom hsub).le_map_sup_fixedPoints ⟨p, hp⟩ ⟨q, hq⟩

/-- The componentwise meet of two fixed points is a pre-fixed point. -/
theorem deferredAcceptanceOperator_inf_le (hsub : M.Substitutable) {p q : Set X × (Set X)ᵒᵈ}
    (hp : IsFixedPt M.deferredAcceptanceOperator p) (hq : IsFixedPt M.deferredAcceptanceOperator q) :
    M.deferredAcceptanceOperator (p ⊓ q) ≤ p ⊓ q :=
  (M.deferredAcceptanceOrderHom hsub).map_inf_fixedPoints_le ⟨p, hp⟩ ⟨q, hq⟩

/-- If the componentwise join is fixed, it agrees with the fixed-point join. -/
theorem state_sup_of_isFixedPt {hsub : M.Substitutable}
    {A A' : M.FixedPointStates hsub}
    (h : IsFixedPt M.deferredAcceptanceOperator (A.state ⊔ A'.state)) :
    (A ⊔ A').state = A.state ⊔ A'.state :=
  (M.deferredAcceptanceOrderHom hsub).fixedPoints_val_sup_of_isFixedPt (p := A) (q := A') h

/-- If the componentwise meet is fixed, it agrees with the fixed-point meet. -/
theorem state_inf_of_isFixedPt {hsub : M.Substitutable}
    {A A' : M.FixedPointStates hsub}
    (h : IsFixedPt M.deferredAcceptanceOperator (A.state ⊓ A'.state)) :
    (A ⊓ A').state = A.state ⊓ A'.state :=
  (M.deferredAcceptanceOrderHom hsub).fixedPoints_val_inf_of_isFixedPt (p := A) (q := A') h

end Market

end MathEconLib.Matching
