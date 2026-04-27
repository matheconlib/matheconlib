module

public import Auctionlib.Mechanism.Basic

/-!
# First-and-Second-Pay Auction

A mechanism is a **first-and-second-pay auction** when:
- The highest bidder wins (efficient allocation).
- The two highest bidders each pay their own bid; all other bidders pay zero.

Concretely, bidder `i` pays `bᵢ` whenever at most one other bidder has a
strictly higher bid—that is, `i` is either the winner or the runner-up—and
pays `0` otherwise.

## Main definitions

* `Mechanism.isTopTwo b i`: predicate that bidder `i` is among the top two
  in bid profile `b` (at most one bidder bids strictly higher).
* `Mechanism.IsFirstAndSecondPay`: typeclass extending `IsEfficient` for
  first-and-second-pay mechanisms.

## Tie behavior

The `isTopTwo` predicate counts bidders with *strictly* higher bids. In
particular, if `k` bidders tie at the highest bid value, all `k` of them
satisfy `isTopTwo` (each sees zero bidders strictly above). This convention
is consistent with `IsEfficient`, which assigns allocation `x i b = 0` for
every `i` whenever there is no unique maximum. In applications where bids
are drawn from a continuous distribution, ties occur with probability zero.
-/

@[expose] public section

open Finset

namespace Mechanism

variable {n : ℕ}

/-- Bidder `i` is among the **top two** in bid profile `b`: at most one
bidder has a strictly higher bid than `i`.

* `card = 0`: no bidder bids strictly higher — `i` is the highest bidder.
* `card = 1`: exactly one bidder bids strictly higher — `i` is the runner-up.
* `card ≥ 2`: two or more bidders bid strictly higher — `i` is not in the
  top two. -/
def isTopTwo (b : Fin n → ℝ) (i : Fin n) : Prop :=
  (univ.filter (fun j => b i < b j)).card ≤ 1

instance isTopTwo.instDecidable (b : Fin n → ℝ) (i : Fin n) :
    Decidable (isTopTwo b i) := by
  unfold isTopTwo; infer_instance

/-- A **first-and-second-pay auction**: efficient allocation (highest bidder
wins) with the two highest bidders each paying their own bid.

The payment for bidder `i` given bids `b` is:
* `bᵢ`  if `isTopTwo b i` (at most one bidder bids strictly higher),
* `0`   otherwise. -/
class IsFirstAndSecondPay (M : Mechanism n) extends IsEfficient M where
  /-- Payment equals own bid for top-two bidders, zero otherwise. -/
  t_eq : ∀ i b, M.t i b = if isTopTwo b i then b i else 0

variable (M : Mechanism n) [IsFirstAndSecondPay M]

/-- A top-two bidder pays their own bid. -/
theorem t_of_isTopTwo {i : Fin n} {b : Fin n → ℝ} (h : isTopTwo b i) :
    M.t i b = b i := by
  rw [IsFirstAndSecondPay.t_eq, if_pos h]

/-- A bidder outside the top two pays zero. -/
theorem t_of_not_isTopTwo {i : Fin n} {b : Fin n → ℝ} (h : ¬isTopTwo b i) :
    M.t i b = 0 := by
  rw [IsFirstAndSecondPay.t_eq, if_neg h]

end Mechanism

end
