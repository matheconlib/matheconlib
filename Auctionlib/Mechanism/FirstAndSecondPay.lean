module

public import Auctionlib.Mechanism.Basic

/-!
# First-and-Second-Pay Auction

A mechanism is a **first-and-second-pay auction** when:
- The highest bidder wins (efficient allocation).
- The two highest bidders each pay their own bid; all other bidders pay zero.

## Main definitions

* `Mechanism.NoTies b`: the bid profile `b` is injective (no two distinct
  bidders submit the same bid).
* `Mechanism.isWinner b i`: bidder `i` strictly beats every other bidder.
* `Mechanism.isRunnerUp b i`: exactly one bidder bids strictly higher
  than `i`.
* `Mechanism.IsFirstAndSecondPay`: typeclass extending `IsEfficient` for
  first-and-second-pay mechanisms.

## Tie handling

`IsFirstAndSecondPay` defines `t i b` as a closed-form expression on **all**
bid profiles, but at tied profiles the resulting payments are not
economically meaningful (e.g. at second-place ties, multiple bidders satisfy
`isRunnerUp` and all pay their bid). All equilibrium-level results in this
file require the hypothesis `NoTies b` (= `Function.Injective b`). Under
continuous, atomless type distributions and the symmetric BNE, the
strict-monotone equilibrium strategy implies `NoTies` holds almost surely,
so behavior at tied profiles never appears in any expectation-level theorem.
-/

@[expose] public section

open scoped Classical

namespace Mechanism

variable {n : ℕ}

/-! ### No-ties predicate -/

/-- A bid profile has **no ties** when no two distinct bidders submit the
same bid, i.e.\ `b` is injective. -/
def NoTies (b : Fin n → ℝ) : Prop := Function.Injective b

/-! ### Winner and runner-up -/

/-- Bidder `i` is the **winner**: `i` strictly beats every other bidder.
Aligned with `IsEfficient.x_efficient`, so under top ties no one is the
winner. -/
def isWinner (b : Fin n → ℝ) (i : Fin n) : Prop :=
  ∀ j ≠ i, b j < b i

/-- Bidder `i` is the **runner-up**: some bidder bids strictly higher than
`i`, but any two bidders who do must coincide—equivalently, exactly one
bidder bids strictly above `i`. -/
def isRunnerUp (b : Fin n → ℝ) (i : Fin n) : Prop :=
  (∃ j, b i < b j) ∧ ∀ j k, b i < b j → b i < b k → j = k

/-! ### General lemmas -/

/-- The runner-up is not the winner. -/
theorem not_isWinner_of_isRunnerUp {b : Fin n → ℝ} {i : Fin n}
    (h : isRunnerUp b i) : ¬isWinner b i := by
  obtain ⟨⟨j, hj⟩, _⟩ := h
  intro hw
  have hji : j ≠ i := fun heq => by rw [heq] at hj; exact lt_irrefl _ hj
  exact lt_asymm hj (hw j hji)

/-- The winner is not the runner-up. -/
theorem not_isRunnerUp_of_isWinner {b : Fin n → ℝ} {i : Fin n}
    (h : isWinner b i) : ¬isRunnerUp b i :=
  fun hr => not_isWinner_of_isRunnerUp hr h

/-! ### First-and-second-pay mechanism -/

/-- A **first-and-second-pay auction**: efficient allocation (highest bidder
wins) with the winner and runner-up each paying their own bid.

The payment for bidder `i` given bids `b` is:
* `bᵢ`  if `i` is the winner or the runner-up,
* `0`   otherwise. -/
class IsFirstAndSecondPay (M : Mechanism n) extends IsEfficient M where
  /-- Payment equals own bid for the winner and runner-up, zero otherwise. -/
  t_eq : ∀ i b, M.t i b = if isWinner b i ∨ isRunnerUp b i then b i else 0

variable (M : Mechanism n) [IsFirstAndSecondPay M]

/-- The winner pays their own bid. -/
theorem t_of_isWinner {i : Fin n} {b : Fin n → ℝ} (h : isWinner b i) :
    M.t i b = b i := by
  rw [IsFirstAndSecondPay.t_eq, if_pos (Or.inl h)]

/-- The runner-up pays their own bid. -/
theorem t_of_isRunnerUp {i : Fin n} {b : Fin n → ℝ} (h : isRunnerUp b i) :
    M.t i b = b i := by
  rw [IsFirstAndSecondPay.t_eq, if_pos (Or.inr h)]

/-- A bidder who is neither the winner nor the runner-up pays zero. -/
theorem t_of_not_winner_not_runnerUp {i : Fin n} {b : Fin n → ℝ}
    (hw : ¬isWinner b i) (hr : ¬isRunnerUp b i) :
    M.t i b = 0 := by
  rw [IsFirstAndSecondPay.t_eq, if_neg (not_or.mpr ⟨hw, hr⟩)]

/-! ### Consequences of no ties -/

section NoTies

variable {b : Fin n → ℝ}

/-- Under no ties, distinct bidders have strictly ordered bids. -/
theorem NoTies.lt_or_lt (hb : NoTies b) {i j : Fin n} (hne : i ≠ j) :
    b i < b j ∨ b j < b i :=
  lt_or_gt_of_ne (fun h => hne (hb h))

/-- Under no ties, weak inequality between distinct bidders is strict. -/
theorem NoTies.lt_of_le (hb : NoTies b) {i j : Fin n}
    (hle : b i ≤ b j) (hne : i ≠ j) :
    b i < b j :=
  lt_of_le_of_ne hle (fun h => hne (hb h))

/-- Under strict `isWinner`, the winner is unique even without `NoTies`,
but stated here for namespace consistency. -/
theorem NoTies.isWinner_unique {i j : Fin n}
    (hi : isWinner b i) (hj : isWinner b j) : i = j := by
  by_contra hij
  exact lt_asymm (hi j (Ne.symm hij)) (hj i hij)

/-- Under no ties, the runner-up is unique. If two distinct bidders were
both runner-ups, one bids strictly above the other (by injectivity); the
higher one together with the witness above it furnishes two distinct bidders
strictly above the lower one, contradicting the runner-up condition. -/
theorem NoTies.isRunnerUp_unique (hb : NoTies b) {i j : Fin n}
    (hi : isRunnerUp b i) (hj : isRunnerUp b j) : i = j := by
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

end Mechanism

end
