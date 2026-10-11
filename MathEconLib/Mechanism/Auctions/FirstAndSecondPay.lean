/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under license as described in the file LICENSE.
Authors: Scott Duke Kominers

Migrated from Auctionlib/Mechanism/FirstAndSecondPay.lean in PR #15, commit b51c018.
-/
module

public import MathEconLib.Mechanism.Auctions.Allocation
public import MathEconLib.Mechanism.Core.SolutionConcepts
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Tactic.FinCases

/-!
# First-and-second-pay auctions

Bidders submit real bids. The unique strictly highest bidder receives the object. On a profile
with distinct bids and at least two bidders, the two highest bidders each pay their own bid and
all others pay zero. Transfers record money received by bidders, so they negate these payments.

The total rule at ties is explicit: a tie for the highest bid leaves the object unallocated;
with a unique highest bid and a tie for second, every bidder tied for second pays their own bid.
The top-two revenue theorem assumes injective bids. No probabilistic no-ties assertion or
Bayesian equilibrium is established here. Negative bids are permitted by the real bid domain.

## Main definitions and results

* `IsFirstAndSecondPay` specifies allocation and payments as a proposition.
* `firstAndSecondPay` implements this specification, proved by `firstAndSecondPay_spec`.
* `NoTies.existsUnique_isWinner` and `NoTies.existsUnique_isRunnerUp` identify the top two ranks.
* `sum_allocation_le_one` proves feasibility, including at ties.
* `NoTies.sum_payment_eq` states that revenue on an injective profile is the sum of the top bids.
* `not_isDSIC` and `not_isExPostIR` use the library's economic predicates for two bidders.

The last two results concern truthful reporting and ex-post participation with outside utility
zero. They do not assert that the auction has no Bayesian equilibrium or fails interim IR there.
-/

@[expose] public section

-- `Set` only: opening `Finset` too would make `univ`/`mem_univ` ambiguous.
open Set

namespace MathEconLib.Mechanism.Auctions.FirstAndSecondPay

variable {n : ℕ}

/-! ### No-ties predicate -/

/-- A bid profile has **no ties** when no two distinct bidders submit the
same bid, i.e.\ `b` is injective. -/
abbrev NoTies (b : Fin n → ℝ) : Prop := Function.Injective b

/-! ### Winner and runner-up -/

/-- Bidder `i` is the **winner**: every *other* bidder bids strictly below `b i`. -/
def IsWinner (b : Fin n → ℝ) (i : Fin n) : Prop :=
  ∀ j ≠ i, b j < b i

/-- Bidder `i` is the **runner-up**: some bidder bids strictly higher than
`i`, but any two bidders who do must coincide—equivalently, exactly one
bidder bids strictly above `i`. -/
def IsRunnerUp (b : Fin n → ℝ) (i : Fin n) : Prop :=
  (∃ j, b i < b j) ∧ ∀ j k, b i < b j → b i < b k → j = k

/-! ### General lemmas -/

/-- The winner bids weakly above everybody, themselves included. -/
theorem IsWinner.le {b : Fin n → ℝ} {i : Fin n} (h : IsWinner b i) (j : Fin n) :
    b j ≤ b i := by
  rcases eq_or_ne j i with rfl | hj
  · exact le_rfl
  · exact (h j hj).le

/-- The winner is unique. No tie-breaking hypothesis is needed: strictness
does the work. -/
theorem isWinner_unique {b : Fin n → ℝ} {i j : Fin n}
    (hi : IsWinner b i) (hj : IsWinner b j) : i = j := by
  by_contra hne
  exact lt_asymm (hi j (Ne.symm hne)) (hj i hne)

/-- The runner-up is not the winner. -/
theorem not_isWinner_of_isRunnerUp {b : Fin n → ℝ} {i : Fin n}
    (h : IsRunnerUp b i) : ¬IsWinner b i := by
  obtain ⟨⟨j, hj⟩, -⟩ := h
  intro hw
  have hji : j ≠ i := by rintro rfl; exact lt_irrefl _ hj
  exact lt_asymm hj (hw j hji)

/-- The winner is not the runner-up. -/
theorem not_isRunnerUp_of_isWinner {b : Fin n → ℝ} {i : Fin n}
    (h : IsWinner b i) : ¬IsRunnerUp b i :=
  fun hr => not_isWinner_of_isRunnerUp hr h

/-! ### Measurability for probabilistic auction models -/

theorem measurableSet_isWinner (i : Fin n) :
    MeasurableSet {f : Fin n → ℝ | ∀ j ≠ i, f j < f i} := by
  have h : {f : Fin n → ℝ | ∀ j ≠ i, f j < f i}
      = ⋂ j : {j : Fin n // j ≠ i},
          {f : Fin n → ℝ | f j.1 < f i} := by
    ext f
    simp only [mem_setOf_eq, mem_iInter, Subtype.forall]
  rw [h]
  exact MeasurableSet.iInter fun j =>
    (isOpen_lt (continuous_apply j.1) (continuous_apply i)).measurableSet

/-! ### Allocation -/

section Allocation

variable (M : Mechanism (Fin n) (fun _ => ℝ) (Fin n → ℝ))
    (halloc : UsesStrictHighestBidAllocation M (fun o i => o i))
    {b : Fin n → ℝ} {i : Fin n}

include halloc

/-- A strict highest bidder receives the object. -/
theorem allocation_eq_one_of_isWinner (h : IsWinner b i) : M.outcome b i = 1 := by
  change (fun b => M.outcome b i) b = 1
  rw [halloc i, indicator_of_mem h, Pi.one_apply]

/-- A bidder who is not strictly highest receives nothing. -/
theorem allocation_eq_zero_of_not_isWinner (h : ¬IsWinner b i) : M.outcome b i = 0 := by
  change (fun b => M.outcome b i) b = 0
  rw [halloc i, indicator_of_notMem h]

/-- The object is allocated at most once, including at tied profiles. -/
theorem sum_allocation_le_one (b : Fin n → ℝ) : ∑ j, M.outcome b j ≤ 1 := by
  by_cases h : ∃ w, IsWinner b w
  · obtain ⟨w, hw⟩ := h
    have : ∑ j, M.outcome b j = 1 := by
      rw [Finset.sum_eq_single_of_mem w (Finset.mem_univ w) fun j _ hj =>
        allocation_eq_zero_of_not_isWinner M halloc fun hjw => hj (isWinner_unique hjw hw)]
      exact allocation_eq_one_of_isWinner M halloc hw
    exact this.le
  · rw [Finset.sum_eq_zero fun j _ =>
      allocation_eq_zero_of_not_isWinner M halloc fun hjw => h ⟨j, hjw⟩]
    exact zero_le_one

end Allocation

/-! ### First-and-second-pay specification -/

/-- Strict-highest-bid allocation, with the winner and every bidder having exactly one
strictly higher bidder paying their own bid. On injective profiles these are exactly the top
two bidders (when at least two bidders participate). The formula also fixes payments at ties;
no equilibrium or participation claim is implicit in this specification. -/
structure IsFirstAndSecondPay (M : Mechanism (Fin n) (fun _ => ℝ) (Fin n → ℝ)) : Prop where
  /-- The unique strict highest bidder receives the object. -/
  allocation : UsesStrictHighestBidAllocation M (fun o i => o i)
  /-- The winner and each runner-up pay their own bid. -/
  payment_of_pay : ∀ i b, IsWinner b i ∨ IsRunnerUp b i → M.payment i b = b i
  /-- All other bidders pay zero. -/
  payment_of_lose : ∀ i b, ¬(IsWinner b i ∨ IsRunnerUp b i) → M.payment i b = 0

section Payments

variable (M : Mechanism (Fin n) (fun _ => ℝ) (Fin n → ℝ)) (hM : IsFirstAndSecondPay M)

include hM

/-- Payment is the own bid for a winner or runner-up, and zero otherwise. -/
theorem IsFirstAndSecondPay.payment_eq (i : Fin n) (b : Fin n → ℝ)
    [Decidable (IsWinner b i ∨ IsRunnerUp b i)] :
    M.payment i b = if IsWinner b i ∨ IsRunnerUp b i then b i else 0 := by
  by_cases h : IsWinner b i ∨ IsRunnerUp b i
  · rw [if_pos h]; exact hM.payment_of_pay i b h
  · rw [if_neg h]; exact hM.payment_of_lose i b h

/-- The winner pays their own bid. -/
theorem payment_of_isWinner {i : Fin n} {b : Fin n → ℝ} (h : IsWinner b i) :
    M.payment i b = b i := hM.payment_of_pay i b (Or.inl h)

/-- Each runner-up pays their own bid. -/
theorem payment_of_isRunnerUp {i : Fin n} {b : Fin n → ℝ} (h : IsRunnerUp b i) :
    M.payment i b = b i := hM.payment_of_pay i b (Or.inr h)

/-- A bidder who is neither winner nor runner-up pays zero. -/
theorem payment_of_not_winner_not_runnerUp {i : Fin n} {b : Fin n → ℝ}
    (hw : ¬IsWinner b i) (hr : ¬IsRunnerUp b i) : M.payment i b = 0 :=
  hM.payment_of_lose i b (not_or.mpr ⟨hw, hr⟩)

end Payments

/-! ### Consequences of no ties -/

section NoTies

variable {b : Fin n → ℝ} (hb : NoTies b)

include hb

/-- Under no ties, distinct bidders have strictly ordered bids. -/
theorem NoTies.lt_or_lt {i j : Fin n} (hne : i ≠ j) :
    b i < b j ∨ b j < b i :=
  lt_or_gt_of_ne (fun h => hne (hb h))

/-- Under no ties, weak inequality between distinct bidders is strict. -/
theorem NoTies.lt_of_le {i j : Fin n} (hle : b i ≤ b j) (hne : i ≠ j) :
    b i < b j :=
  lt_of_le_of_ne hle (fun h => hne (hb h))

/-- Under no ties, the runner-up is unique. If two distinct bidders were
both runner-ups, one bids strictly above the other (by injectivity); the
higher one together with the witness above it furnishes two distinct bidders
strictly above the lower one, contradicting the runner-up condition. -/
theorem NoTies.isRunnerUp_unique {i j : Fin n}
    (hi : IsRunnerUp b i) (hj : IsRunnerUp b j) : i = j := by
  by_contra hij
  have hbne : b i ≠ b j := fun heq => hij (hb heq)
  rcases lt_or_gt_of_ne hbne with h | h
  · -- b i < b j: j beats i, and the witness w above j also beats i
    obtain ⟨⟨w, hw⟩, _⟩ := hj
    obtain ⟨_, huniq⟩ := hi
    have heq := huniq _ _ h (lt_trans h hw)
    rw [heq] at hw
    exact lt_irrefl _ hw
  · -- b j < b i: symmetric
    obtain ⟨⟨w, hw⟩, _⟩ := hi
    obtain ⟨_, huniq⟩ := hj
    have heq := huniq _ _ h (lt_trans h hw)
    rw [heq] at hw
    exact lt_irrefl _ hw

end NoTies

/-! ### The two paying bidders

Injectivity ensures unique first and second ranks. Lower-rank ties need not prevent a winner,
but can produce multiple runner-ups; a tie for the highest bid prevents allocation. -/

section Paying

variable {b : Fin n → ℝ}

/-- Injectivity upgrades a maximiser to a winner. -/
theorem NoTies.isWinner_of_forall_le (hb : NoTies b) {i : Fin n} (h : ∀ j, b j ≤ b i) :
    IsWinner b i :=
  fun j hj => (h j).lt_of_ne fun hEq => hj (hb hEq)

/-- **Existence of a winner.** `NoTies` is essential: for `b = fun _ => 1` with
`2 ≤ n` a maximiser exists but no bidder is a winner. -/
theorem NoTies.exists_isWinner [Nonempty (Fin n)] (hb : NoTies b) : ∃ i, IsWinner b i := by
  obtain ⟨i, hi⟩ := Finite.exists_max b
  exact ⟨i, hb.isWinner_of_forall_le hi⟩

theorem NoTies.existsUnique_isWinner [Nonempty (Fin n)] (hb : NoTies b) :
    ∃! i, IsWinner b i := by
  obtain ⟨i, hi⟩ := hb.exists_isWinner
  exact ⟨i, hi, fun j hj => isWinner_unique hj hi⟩

/-- The winner of a tie-free profile. Noncomputable (choice); independent of the
proof `hb` by proof irrelevance. -/
noncomputable abbrev NoTies.winner [Nonempty (Fin n)] (hb : NoTies b) : Fin n :=
  hb.exists_isWinner.choose

theorem NoTies.isWinner_winner [Nonempty (Fin n)] (hb : NoTies b) :
    IsWinner b hb.winner :=
  hb.exists_isWinner.choose_spec

theorem NoTies.eq_winner [Nonempty (Fin n)] (hb : NoTies b) {i : Fin n}
    (hi : IsWinner b i) : i = hb.winner :=
  isWinner_unique hi hb.isWinner_winner

theorem NoTies.isWinner_iff_eq_winner [Nonempty (Fin n)] (hb : NoTies b) {i : Fin n} :
    IsWinner b i ↔ i = hb.winner :=
  ⟨hb.eq_winner, fun h => h ▸ hb.isWinner_winner⟩

theorem NoTies.le_winner [Nonempty (Fin n)] (hb : NoTies b) (j : Fin n) :
    b j ≤ b hb.winner :=
  hb.isWinner_winner.le j

/-- **Existence of a runner-up**, needing two bidders: maximise over the
complement of the winner. -/
theorem NoTies.exists_isRunnerUp [Nontrivial (Fin n)] (hb : NoTies b) :
    ∃ i, IsRunnerUp b i := by
  obtain ⟨j₀, hj₀⟩ := exists_ne hb.winner
  haveI : Nonempty {j : Fin n // j ≠ hb.winner} := ⟨⟨j₀, hj₀⟩⟩
  obtain ⟨r, hr⟩ := Finite.exists_max fun j : {j : Fin n // j ≠ hb.winner} => b j.1
  refine ⟨r.1, ⟨hb.winner, hb.isWinner_winner r.1 r.2⟩, fun j k hj hk => ?_⟩
  have key : ∀ m, b r.1 < b m → m = hb.winner := by
    intro m hm
    by_contra hmw
    exact absurd (hr ⟨m, hmw⟩) (not_le.mpr hm)
  rw [key j hj, key k hk]

theorem NoTies.existsUnique_isRunnerUp [Nontrivial (Fin n)] (hb : NoTies b) :
    ∃! i, IsRunnerUp b i := by
  obtain ⟨i, hi⟩ := hb.exists_isRunnerUp
  exact ⟨i, hi, fun j hj => hb.isRunnerUp_unique hj hi⟩

/-- The runner-up of a tie-free profile with at least two bidders. -/
noncomputable abbrev NoTies.runnerUp [Nontrivial (Fin n)] (hb : NoTies b) : Fin n :=
  hb.exists_isRunnerUp.choose

theorem NoTies.isRunnerUp_runnerUp [Nontrivial (Fin n)] (hb : NoTies b) :
    IsRunnerUp b hb.runnerUp :=
  hb.exists_isRunnerUp.choose_spec

theorem NoTies.eq_runnerUp [Nontrivial (Fin n)] (hb : NoTies b) {i : Fin n}
    (hi : IsRunnerUp b i) : i = hb.runnerUp :=
  hb.isRunnerUp_unique hi hb.isRunnerUp_runnerUp

theorem NoTies.winner_ne_runnerUp [Nontrivial (Fin n)] (hb : NoTies b) :
    hb.winner ≠ hb.runnerUp := by
  intro h
  refine not_isRunnerUp_of_isWinner hb.isWinner_winner ?_
  rw [h]; exact hb.isRunnerUp_runnerUp

/-- **The "top two" reading of `IsRunnerUp`.** Under no ties, being a runner-up is
exactly being the strict maximiser among the non-winners. This is what makes
`IsFirstAndSecondPay.payment_eq` legible as an auction rule. -/
theorem NoTies.isRunnerUp_iff [Nontrivial (Fin n)] (hb : NoTies b) {i : Fin n} :
    IsRunnerUp b i ↔ i ≠ hb.winner ∧ ∀ j ≠ i, j ≠ hb.winner → b j < b i := by
  constructor
  · intro hi
    have hiw : i ≠ hb.winner := by
      intro h
      exact not_isWinner_of_isRunnerUp hi (by rw [h]; exact hb.isWinner_winner)
    refine ⟨hiw, fun j hji hjw => ?_⟩
    by_contra hlt
    exact hjw (hi.2 j hb.winner (hb.lt_of_le (not_lt.mp hlt) (Ne.symm hji))
      (hb.isWinner_winner i hiw))
  · rintro ⟨hiw, hlt⟩
    refine ⟨⟨hb.winner, hb.isWinner_winner i hiw⟩, fun j k hj hk => ?_⟩
    have key : ∀ m, b i < b m → m = hb.winner := by
      intro m hm
      by_contra hmw
      rcases eq_or_ne m i with rfl | hmi
      · exact lt_irrefl _ hm
      · exact absurd hm (not_lt.mpr (hlt m hmi hmw).le)
    rw [key j hj, key k hk]

/-- On a tie-free profile the object is allocated exactly once. A tie for the highest bid
instead leaves the object unallocated. -/
theorem NoTies.sum_allocation_eq_one (M : Mechanism (Fin n) (fun _ => ℝ) (Fin n → ℝ))
    (halloc : UsesStrictHighestBidAllocation M (fun o i => o i)) [Nonempty (Fin n)]
    (hb : NoTies b) : ∑ j, M.outcome b j = 1 := by
  rw [Finset.sum_eq_single_of_mem hb.winner (Finset.mem_univ _) fun j _ hj =>
    allocation_eq_zero_of_not_isWinner M halloc fun hjw => hj (hb.eq_winner hjw)]
  exact allocation_eq_one_of_isWinner M halloc hb.isWinner_winner

/-- **Revenue.** On a tie-free profile the seller collects the top two bids. -/
theorem NoTies.sum_payment_eq (M : Mechanism (Fin n) (fun _ => ℝ) (Fin n → ℝ))
    (hM : IsFirstAndSecondPay M) [Nontrivial (Fin n)]
    (hb : NoTies b) : ∑ j, M.payment j b = b hb.winner + b hb.runnerUp := by
  classical
  have hne := hb.winner_ne_runnerUp
  have h₁ : ∑ j, M.payment j b
      = M.payment hb.winner b + ∑ j ∈ Finset.univ.erase hb.winner, M.payment j b :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ _)).symm
  have h₂ : ∑ j ∈ Finset.univ.erase hb.winner, M.payment j b
      = M.payment hb.runnerUp b
        + ∑ j ∈ (Finset.univ.erase hb.winner).erase hb.runnerUp, M.payment j b :=
    (Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩)).symm
  have h₃ : ∑ j ∈ (Finset.univ.erase hb.winner).erase hb.runnerUp, M.payment j b = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    obtain ⟨hjr, hj'⟩ := Finset.mem_erase.mp hj
    obtain ⟨hjw, -⟩ := Finset.mem_erase.mp hj'
    exact payment_of_not_winner_not_runnerUp M hM (fun hw => hjw (hb.eq_winner hw))
      (fun hr => hjr (hb.eq_runnerUp hr))
  rw [h₁, h₂, h₃, add_zero, payment_of_isWinner M hM hb.isWinner_winner,
    payment_of_isRunnerUp M hM hb.isRunnerUp_runnerUp]

end Paying

/-! ### Canonical mechanism and values -/

/-- A total implementation: allocation is zero at top ties, and a bidder pays their own bid
exactly when they are a strict winner or have exactly one strictly higher bidder. Negative bids
are allowed and correspond to subsidies when paid. -/
noncomputable def firstAndSecondPay (n : ℕ) :
    Mechanism (Fin n) (fun _ => ℝ) (Fin n → ℝ) := by
  classical
  exact {
    outcome := fun b i => {f : Fin n → ℝ | ∀ j ≠ i, f j < f i}.indicator 1 b
    transfer := fun i b => -(if IsWinner b i ∨ IsRunnerUp b i then b i else 0) }

/-- The canonical implementation realizes the first-and-second-pay specification. -/
theorem firstAndSecondPay_spec : IsFirstAndSecondPay (firstAndSecondPay n) where
  allocation _ := rfl
  payment_of_pay _ _ h := by simp [Mechanism.payment, firstAndSecondPay, if_pos h]
  payment_of_lose _ _ h := by simp [Mechanism.payment, firstAndSecondPay, if_neg h]

/-- The allocation of each bidder is measurable, as needed to use these rules in an `Auction`. -/
theorem firstAndSecondPay_allocation_measurable (i : Fin n) :
    Measurable (fun b => (firstAndSecondPay n).outcome b i) :=
  measurable_one.indicator (measurableSet_isWinner i)

/-- Private values for allocation vectors: a bidder values their own allocation at their type
times their allocation. -/
def privateValues (n : ℕ) :
    QuasilinearEnvironment (Fin n) (fun _ => ℝ) (Fin n → ℝ) :=
  QuasilinearEnvironment.ofPrivate fun i v o => v * o i

/-- A runner-up receives nothing and pays their own bid. -/
theorem allocation_eq_zero_and_payment_eq_of_isRunnerUp
    (M : Mechanism (Fin n) (fun _ => ℝ) (Fin n → ℝ)) (hM : IsFirstAndSecondPay M)
    {i : Fin n} {b : Fin n → ℝ} (h : IsRunnerUp b i) :
    M.outcome b i = 0 ∧ M.payment i b = b i :=
  ⟨allocation_eq_zero_of_not_isWinner M hM.allocation (not_isWinner_of_isRunnerUp h),
    payment_of_isRunnerUp M hM h⟩

section TwoBidders

variable {v : ℝ}

/-- With two bidders the low bidder is the runner-up. -/
theorem isRunnerUp_one_of_lt_one (hv : v < 1) : IsRunnerUp ![(1 : ℝ), v] 1 := by
  have e0 : (![(1 : ℝ), v] : Fin 2 → ℝ) 0 = 1 := by simp
  have e1 : (![(1 : ℝ), v] : Fin 2 → ℝ) 1 = v := by simp
  have key : ∀ m : Fin 2, ![(1 : ℝ), v] 1 < ![(1 : ℝ), v] m → m = 0 := by
    rw [Fin.forall_fin_two]
    exact ⟨fun _ => rfl, fun hm => absurd hm (by simp)⟩
  exact ⟨⟨0, by rw [e0, e1]; exact hv⟩, fun j k hj hk => by rw [key j hj, key k hk]⟩

/-- A profitable deviation from truthful bidding. Against a bid of `1`,
a bidder of value `v ∈ (0,1)` is the runner-up: they win nothing and pay their
own bid. Shading to `0` keeps them a runner-up, so they still win nothing — but
now pay nothing, strictly improving their quasi-linear payoff from `-v` to `0`.

`not_isDSIC` below expresses this failure using the library's incentive predicate. -/
theorem lt_payoff_of_shade (M : Mechanism (Fin 2) (fun _ => ℝ) (Fin 2 → ℝ))
    (hM : IsFirstAndSecondPay M)
    (hv0 : 0 < v) (hv1 : v < 1) :
    v * M.outcome ![1, v] 1 - M.payment 1 ![1, v] <
      v * M.outcome ![1, 0] 1 - M.payment 1 ![1, 0] := by
  obtain ⟨hx, ht⟩ :=
    allocation_eq_zero_and_payment_eq_of_isRunnerUp M hM (isRunnerUp_one_of_lt_one hv1)
  obtain ⟨hx0, ht0⟩ :=
    allocation_eq_zero_and_payment_eq_of_isRunnerUp M hM (isRunnerUp_one_of_lt_one (v := 0) one_pos)
  have e1 : (![(1 : ℝ), v] : Fin 2 → ℝ) 1 = v := by simp
  have e0 : (![(1 : ℝ), (0 : ℝ)] : Fin 2 → ℝ) 1 = 0 := by simp
  rw [hx, ht, hx0, ht0, e1, e0]
  linarith

/-- At the truthful profile `(1,v)` with `0 < v < 1`, the runner-up gets negative payoff.
This is an ex-post statement, with outside utility normalized to zero. -/
theorem payoff_neg (M : Mechanism (Fin 2) (fun _ => ℝ) (Fin 2 → ℝ)) (hM : IsFirstAndSecondPay M)
    (hv0 : 0 < v) (hv1 : v < 1) :
    v * M.outcome ![1, v] 1 - M.payment 1 ![1, v] < 0 := by
  obtain ⟨hx, ht⟩ :=
    allocation_eq_zero_and_payment_eq_of_isRunnerUp M hM (isRunnerUp_one_of_lt_one hv1)
  have e1 : (![(1 : ℝ), v] : Fin 2 → ℝ) 1 = v := by simp
  rw [hx, ht, e1]
  linarith

/-- Truthful reporting is not a dominant strategy, even on nonnegative, tie-free profiles.
This does not rule out a Bayesian equilibrium in nontruthful strategies. -/
theorem not_isDSIC (M : Mechanism (Fin 2) (fun _ => ℝ) (Fin 2 → ℝ))
    (hM : IsFirstAndSecondPay M) : ¬DirectMechanism.IsDSIC (privateValues 2) M := by
  intro h
  have hgain := lt_payoff_of_shade M hM (v := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hle := h 1 ![1, (1 / 2 : ℝ)] ![1, 0]
  have hupdate : Function.update (![1, 0] : Fin 2 → ℝ) 1 (1 / 2) = ![1, 1 / 2] := by
    ext i
    fin_cases i <;> simp
  rw [show (![1, (1 / 2 : ℝ)] : Fin 2 → ℝ) 1 = 1 / 2 by simp, hupdate] at hle
  simp only [QuasilinearEnvironment.utility_eq_value_sub_payment] at hle
  change (1 / 2 : ℝ) * M.outcome ![1, 0] 1 - M.payment 1 ![1, 0] ≤
    (1 / 2 : ℝ) * M.outcome ![1, 1 / 2] 1 - M.payment 1 ![1, 1 / 2] at hle
  exact (not_le_of_gt hgain) hle

/-- Truthful participation is not ex-post individually rational when outside utility is zero. -/
theorem not_isExPostIR (M : Mechanism (Fin 2) (fun _ => ℝ) (Fin 2 → ℝ))
    (hM : IsFirstAndSecondPay M) : ¬DirectMechanism.IsExPostIR (privateValues 2) M := by
  intro h
  have hneg := payoff_neg M hM (v := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hnonneg := h 1 ![1, (1 / 2 : ℝ)]
  change 0 ≤ (1 / 2 : ℝ) * M.outcome ![1, 1 / 2] 1 + M.transfer 1 ![1, 1 / 2] at hnonneg
  simp only [Mechanism.payment, sub_neg_eq_add] at hneg
  exact (not_le_of_gt hneg) hnonneg

end TwoBidders

end MathEconLib.Mechanism.Auctions.FirstAndSecondPay

end
