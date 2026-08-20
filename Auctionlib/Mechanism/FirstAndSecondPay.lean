module

public import Auctionlib.Mechanism.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# First-and-Second-Pay Auction

A mechanism is a **first-and-second-pay auction** when:
- The highest bidder wins (efficient allocation).
- The two highest bidders each pay their own bid; all other bidders pay zero.
- Tied profiles currently out-of-scope.

## Main definitions

* `Mechanism.NoTies b`: the bid profile `b` is injective (no two distinct
  bidders submit the same bid).
* `Mechanism.isWinner b i`: bidder `i` bids strictly above every *other* bidder.
* `Mechanism.isRunnerUp b i`: exactly one bidder bids strictly higher than `i`.
* `Mechanism.IsFirstAndSecondPay`: typeclass extending `IsEfficient` for
  first-and-second-pay mechanisms.
* `Mechanism.NoTies.winner`, `Mechanism.NoTies.runnerUp`: the two paying bidders
  of a tie-free profile.
* `Mechanism.firstAndSecondPay`: the canonical example, witnessing that the
  typeclass is inhabited.

## The `≠ i` in `isWinner`

`isWinner` quantifies over `j ≠ i`, *not* over all `j`: the unguarded form
`∀ j, b j < b i` is instantiable at `j := i` and is therefore unsatisfiable.
The guarded form is also, on the nose, the set appearing in
`IsEfficient.x_efficient`; `isWinner_iff_mem_efficientSet` is that bridge, and it
is `Iff.rfl`. Strictness makes `isWinner` uniquely satisfiable without any
tie-breaking hypothesis (`isWinner_unique`), at the cost of being *unsatisfiable*
on tied profiles — which is why `NoTies` appears in every existence, total-allocation
and revenue statement below.

## No-ties assumption

Under `NoTies b`, bids induce a strict total order on bidders: there is a
unique winner, a unique runner-up, and all remaining bidders are losers who
pay nothing. In the symmetric BNE with continuous value distributions the
equilibrium strategy is strictly monotone, so `NoTies` holds almost surely.
-/

@[expose] public section

-- `Set` only: opening `Finset` too would make `univ`/`mem_univ` ambiguous.
open Set

namespace Mechanism

variable {n : ℕ}

/-! ### No-ties predicate -/

/-- A bid profile has **no ties** when no two distinct bidders submit the
same bid, i.e.\ `b` is injective. -/
def NoTies (b : Fin n → ℝ) : Prop := Function.Injective b

/-! ### Winner and runner-up -/

/-- Bidder `i` is the **winner**: every *other* bidder bids strictly below `b i`.

The `j ≠ i` guard is essential — see the module docstring. -/
def isWinner (b : Fin n → ℝ) (i : Fin n) : Prop :=
  ∀ j ≠ i, b j < b i

/-- `isWinner` is exactly the set whose indicator is the efficient allocation. -/
theorem isWinner_iff_mem_efficientSet (b : Fin n → ℝ) (i : Fin n) :
    b ∈ {f : Fin n → ℝ | ∀ j ≠ i, f j < f i} ↔ isWinner b i := Iff.rfl

/-- Bidder `i` is the **runner-up**: some bidder bids strictly higher than
`i`, but any two bidders who do must coincide—equivalently, exactly one
bidder bids strictly above `i`. -/
def isRunnerUp (b : Fin n → ℝ) (i : Fin n) : Prop :=
  (∃ j, b i < b j) ∧ ∀ j k, b i < b j → b i < b k → j = k

/-! ### General lemmas -/

/-- The winner bids weakly above everybody, themselves included. -/
theorem isWinner.le {b : Fin n → ℝ} {i : Fin n} (h : isWinner b i) (j : Fin n) :
    b j ≤ b i := by
  rcases eq_or_ne j i with rfl | hj
  · exact le_rfl
  · exact (h j hj).le

/-- The winner is unique. No tie-breaking hypothesis is needed: strictness
does the work. -/
theorem isWinner_unique {b : Fin n → ℝ} {i j : Fin n}
    (hi : isWinner b i) (hj : isWinner b j) : i = j := by
  by_contra hne
  exact lt_asymm (hi j (Ne.symm hne)) (hj i hne)

/-- The runner-up is not the winner. -/
theorem not_isWinner_of_isRunnerUp {b : Fin n → ℝ} {i : Fin n}
    (h : isRunnerUp b i) : ¬isWinner b i := by
  obtain ⟨⟨j, hj⟩, -⟩ := h
  intro hw
  have hji : j ≠ i := by rintro rfl; exact lt_irrefl _ hj
  exact lt_asymm hj (hw j hji)

/-- The winner is not the runner-up. -/
theorem not_isRunnerUp_of_isWinner {b : Fin n → ℝ} {i : Fin n}
    (h : isWinner b i) : ¬isRunnerUp b i :=
  fun hr => not_isWinner_of_isRunnerUp hr h

/-! ### Measurability of the efficient allocation

Required to build a `Mechanism` at all, since `x_measurable` is a field. -/

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

/-! ### Consequences of efficiency

`IsEfficient` determines `x` outright, so these are equalities, not bounds. -/

section Efficient

variable (M : Mechanism n) [IsEfficient M] {b : Fin n → ℝ} {i : Fin n}

/-- Two efficient mechanisms share an allocation rule. -/
theorem IsEfficient.x_eq (M M' : Mechanism n) [IsEfficient M] [IsEfficient M'] :
    M.x = M'.x := by
  funext i
  rw [IsEfficient.x_efficient (M := M) i, IsEfficient.x_efficient (M := M') i]

theorem x_eq_one_of_isWinner (h : isWinner b i) : M.x i b = 1 := by
  rw [IsEfficient.x_efficient (M := M) i,
    indicator_of_mem ((isWinner_iff_mem_efficientSet b i).mpr h), Pi.one_apply]

theorem x_eq_zero_of_not_isWinner (h : ¬isWinner b i) : M.x i b = 0 := by
  rw [IsEfficient.x_efficient (M := M) i,
    indicator_of_notMem fun hm => h ((isWinner_iff_mem_efficientSet b i).mp hm)]

theorem x_eq_one_iff : M.x i b = 1 ↔ isWinner b i := by
  refine ⟨fun h => ?_, x_eq_one_of_isWinner M⟩
  by_contra hw
  rw [x_eq_zero_of_not_isWinner M hw] at h
  exact zero_ne_one h

/-- Closed form for the allocation. The `Decidable` instance is an *argument*, so
this unifies with whatever instance the caller's goal happens to carry. -/
theorem x_eq (i : Fin n) (b : Fin n → ℝ) [Decidable (isWinner b i)] :
    M.x i b = if isWinner b i then 1 else 0 := by
  by_cases h : isWinner b i
  · rw [if_pos h]; exact x_eq_one_of_isWinner M h
  · rw [if_neg h]; exact x_eq_zero_of_not_isWinner M h

/-- The object is allocated at most once. Needs no `NoTies`, by `isWinner_unique`. -/
theorem sum_x_le_one (b : Fin n → ℝ) : ∑ j, M.x j b ≤ 1 := by
  by_cases h : ∃ w, isWinner b w
  · obtain ⟨w, hw⟩ := h
    have : ∑ j, M.x j b = 1 := by
      rw [Finset.sum_eq_single_of_mem w (Finset.mem_univ w) fun j _ hj =>
        x_eq_zero_of_not_isWinner M fun hjw => hj (isWinner_unique hjw hw)]
      exact x_eq_one_of_isWinner M hw
    exact this.le
  · rw [Finset.sum_eq_zero fun j _ => x_eq_zero_of_not_isWinner M fun hjw => h ⟨j, hjw⟩]
    exact zero_le_one

end Efficient

/-! ### First-and-second-pay mechanism -/

section FirstAndSecondPay

/-- A **first-and-second-pay auction**: efficient allocation (highest bidder
wins) with the winner and runner-up each paying their own bid.

The payment for bidder `i` given bids `b` is:
* `bᵢ`  if `i` is the winner or the runner-up,
* `0`   otherwise.

Stated as two propositional fields rather than one `ite` equation: the `ite` form
needs `Decidable (isWinner b i ∨ isRunnerUp b i)` *in the type of the field*, and the
only such instance is `Classical.propDecidable`, which is `scoped` and hence not in
scope here. See `IsFirstAndSecondPay.t_eq` for the closed form. -/
class IsFirstAndSecondPay (M : Mechanism n) extends IsEfficient M where
  /-- The winner and the runner-up pay their own bid. -/
  t_of_pay : ∀ i b, isWinner b i ∨ isRunnerUp b i → M.t i b = b i
  /-- Everybody else pays zero. -/
  t_of_lose : ∀ i b, ¬(isWinner b i ∨ isRunnerUp b i) → M.t i b = 0

variable (M : Mechanism n) [IsFirstAndSecondPay M]

/-- Payment equals own bid for the winner and runner-up, zero otherwise.

Kept in the `IsFirstAndSecondPay` namespace so that existing
`rw [IsFirstAndSecondPay.t_eq]` call sites continue to resolve. -/
theorem IsFirstAndSecondPay.t_eq (i : Fin n) (b : Fin n → ℝ)
    [Decidable (isWinner b i ∨ isRunnerUp b i)] :
    M.t i b = if isWinner b i ∨ isRunnerUp b i then b i else 0 := by
  by_cases h : isWinner b i ∨ isRunnerUp b i
  · rw [if_pos h]; exact IsFirstAndSecondPay.t_of_pay i b h
  · rw [if_neg h]; exact IsFirstAndSecondPay.t_of_lose i b h

/-- The winner pays their own bid. -/
theorem t_of_isWinner {i : Fin n} {b : Fin n → ℝ} (h : isWinner b i) :
    M.t i b = b i :=
  IsFirstAndSecondPay.t_of_pay i b (Or.inl h)

/-- The runner-up pays their own bid. -/
theorem t_of_isRunnerUp {i : Fin n} {b : Fin n → ℝ} (h : isRunnerUp b i) :
    M.t i b = b i :=
  IsFirstAndSecondPay.t_of_pay i b (Or.inr h)

/-- A bidder who is neither the winner nor the runner-up pays zero. -/
theorem t_of_not_winner_not_runnerUp {i : Fin n} {b : Fin n → ℝ}
    (hw : ¬isWinner b i) (hr : ¬isRunnerUp b i) :
    M.t i b = 0 :=
  IsFirstAndSecondPay.t_of_lose i b (not_or.mpr ⟨hw, hr⟩)

end FirstAndSecondPay

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

/-! ### The two paying bidders

Everything here is `NoTies`-only: on a tied profile `isWinner` is unsatisfiable,
so there is no winner to name and the efficient allocation sums to `0`. -/

section Paying

variable {b : Fin n → ℝ}

/-- Some bidder bids weakly highest. This alone does *not* produce an `isWinner`:
on a tied profile a maximiser exists but no winner does. -/
theorem exists_forall_le [Nonempty (Fin n)] (f : Fin n → ℝ) : ∃ i, ∀ j, f j ≤ f i :=
  Finite.exists_max f

/-- Injectivity upgrades a maximiser to a winner. -/
theorem NoTies.isWinner_of_forall_le (hb : NoTies b) {i : Fin n} (h : ∀ j, b j ≤ b i) :
    isWinner b i :=
  fun j hj => (h j).lt_of_ne fun hEq => hj (hb hEq)

/-- **Existence of a winner.** `NoTies` is essential: for `b = fun _ => 1` with
`2 ≤ n` a maximiser exists but no bidder is a winner. -/
theorem NoTies.exists_isWinner [Nonempty (Fin n)] (hb : NoTies b) : ∃ i, isWinner b i := by
  obtain ⟨i, hi⟩ := exists_forall_le b
  exact ⟨i, hb.isWinner_of_forall_le hi⟩

theorem NoTies.existsUnique_isWinner [Nonempty (Fin n)] (hb : NoTies b) :
    ∃! i, isWinner b i := by
  obtain ⟨i, hi⟩ := hb.exists_isWinner
  exact ⟨i, hi, fun j hj => isWinner_unique hj hi⟩

/-- The winner of a tie-free profile. Noncomputable (choice); independent of the
proof `hb` by proof irrelevance. -/
noncomputable def NoTies.winner [Nonempty (Fin n)] (hb : NoTies b) : Fin n :=
  hb.exists_isWinner.choose

theorem NoTies.isWinner_winner [Nonempty (Fin n)] (hb : NoTies b) :
    isWinner b hb.winner :=
  hb.exists_isWinner.choose_spec

theorem NoTies.eq_winner [Nonempty (Fin n)] (hb : NoTies b) {i : Fin n}
    (hi : isWinner b i) : i = hb.winner :=
  isWinner_unique hi hb.isWinner_winner

theorem NoTies.isWinner_iff_eq_winner [Nonempty (Fin n)] (hb : NoTies b) {i : Fin n} :
    isWinner b i ↔ i = hb.winner :=
  ⟨hb.eq_winner, fun h => h ▸ hb.isWinner_winner⟩

theorem NoTies.le_winner [Nonempty (Fin n)] (hb : NoTies b) (j : Fin n) :
    b j ≤ b hb.winner :=
  hb.isWinner_winner.le j

/-- **Existence of a runner-up**, needing two bidders: maximise over the
complement of the winner. -/
theorem NoTies.exists_isRunnerUp [Nontrivial (Fin n)] (hb : NoTies b) :
    ∃ i, isRunnerUp b i := by
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
    ∃! i, isRunnerUp b i := by
  obtain ⟨i, hi⟩ := hb.exists_isRunnerUp
  exact ⟨i, hi, fun j hj => hb.isRunnerUp_unique hj hi⟩

/-- The runner-up of a tie-free profile with at least two bidders. -/
noncomputable def NoTies.runnerUp [Nontrivial (Fin n)] (hb : NoTies b) : Fin n :=
  hb.exists_isRunnerUp.choose

theorem NoTies.isRunnerUp_runnerUp [Nontrivial (Fin n)] (hb : NoTies b) :
    isRunnerUp b hb.runnerUp :=
  hb.exists_isRunnerUp.choose_spec

theorem NoTies.eq_runnerUp [Nontrivial (Fin n)] (hb : NoTies b) {i : Fin n}
    (hi : isRunnerUp b i) : i = hb.runnerUp :=
  hb.isRunnerUp_unique hi hb.isRunnerUp_runnerUp

theorem NoTies.winner_ne_runnerUp [Nontrivial (Fin n)] (hb : NoTies b) :
    hb.winner ≠ hb.runnerUp := by
  intro h
  refine not_isRunnerUp_of_isWinner hb.isWinner_winner ?_
  rw [h]; exact hb.isRunnerUp_runnerUp

/-- **The "top two" reading of `isRunnerUp`.** Under no ties, being a runner-up is
exactly being the strict maximiser among the non-winners. This is what makes
`IsFirstAndSecondPay.t_eq` legible as an auction rule. -/
theorem NoTies.isRunnerUp_iff [Nontrivial (Fin n)] (hb : NoTies b) {i : Fin n} :
    isRunnerUp b i ↔ i ≠ hb.winner ∧ ∀ j ≠ i, j ≠ hb.winner → b j < b i := by
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

/-- On a tie-free profile the object is allocated exactly once. False without
`NoTies`: at a tie the efficient indicator is identically `0`. -/
theorem NoTies.sum_x_eq_one (M : Mechanism n) [IsEfficient M] [Nonempty (Fin n)]
    (hb : NoTies b) : ∑ j, M.x j b = 1 := by
  rw [Finset.sum_eq_single_of_mem hb.winner (Finset.mem_univ _) fun j _ hj =>
    x_eq_zero_of_not_isWinner M fun hjw => hj (hb.eq_winner hjw)]
  exact x_eq_one_of_isWinner M hb.isWinner_winner

/-- **Revenue.** On a tie-free profile the seller collects the top two bids. -/
theorem NoTies.sum_t_eq (M : Mechanism n) [IsFirstAndSecondPay M] [Nontrivial (Fin n)]
    (hb : NoTies b) : ∑ j, M.t j b = b hb.winner + b hb.runnerUp := by
  classical
  have hne := hb.winner_ne_runnerUp
  have h₁ : ∑ j, M.t j b
      = M.t hb.winner b + ∑ j ∈ Finset.univ.erase hb.winner, M.t j b :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ _)).symm
  have h₂ : ∑ j ∈ Finset.univ.erase hb.winner, M.t j b
      = M.t hb.runnerUp b
        + ∑ j ∈ (Finset.univ.erase hb.winner).erase hb.runnerUp, M.t j b :=
    (Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩)).symm
  have h₃ : ∑ j ∈ (Finset.univ.erase hb.winner).erase hb.runnerUp, M.t j b = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    obtain ⟨hjr, hj'⟩ := Finset.mem_erase.mp hj
    obtain ⟨hjw, -⟩ := Finset.mem_erase.mp hj'
    exact t_of_not_winner_not_runnerUp M (fun hw => hjw (hb.eq_winner hw))
      (fun hr => hjr (hb.eq_runnerUp hr))
  rw [h₁, h₂, h₃, add_zero, t_of_isWinner M hb.isWinner_winner,
    t_of_isRunnerUp M hb.isRunnerUp_runnerUp]

end Paying

/-! ### The canonical example

Nothing above is vacuous. `noncomputable` because `Set.indicator` and the order on
`ℝ` are classical — exactly why the class fields avoid `ite`. -/

open scoped Classical in
noncomputable def firstAndSecondPay (n : ℕ) : Mechanism n where
  x i := {f : Fin n → ℝ | ∀ j ≠ i, f j < f i}.indicator 1
  x_measurable i := measurable_one.indicator (measurableSet_isWinner i)
  t i b := if isWinner b i ∨ isRunnerUp b i then b i else 0

open scoped Classical in
instance : IsFirstAndSecondPay (firstAndSecondPay n) where
  x_efficient _ := rfl
  t_of_pay _ _ h := if_pos h
  t_of_lose _ _ h := if_neg h

/-- The runner-up receives nothing and pays their own bid. This single fact is
the whole obstruction to incentive compatibility. -/
theorem x_eq_zero_and_t_eq_of_isRunnerUp (M : Mechanism n) [IsFirstAndSecondPay M]
    {i : Fin n} {b : Fin n → ℝ} (h : isRunnerUp b i) :
    M.x i b = 0 ∧ M.t i b = b i :=
  ⟨x_eq_zero_of_not_isWinner M (not_isWinner_of_isRunnerUp h), t_of_isRunnerUp M h⟩

section TwoBidders

variable {v : ℝ}

/-- With two bidders the low bidder is the runner-up. -/
theorem isRunnerUp_one_of_lt_one (hv : v < 1) : isRunnerUp ![(1 : ℝ), v] 1 := by
  have e0 : (![(1 : ℝ), v] : Fin 2 → ℝ) 0 = 1 := by simp
  have e1 : (![(1 : ℝ), v] : Fin 2 → ℝ) 1 = v := by simp
  have key : ∀ m : Fin 2, ![(1 : ℝ), v] 1 < ![(1 : ℝ), v] m → m = 0 := by
    rw [Fin.forall_fin_two]
    exact ⟨fun _ => rfl, fun hm => absurd hm (by simp)⟩
  exact ⟨⟨0, by rw [e0, e1]; exact hv⟩, fun j k hj hk => by rw [key j hj, key k hk]⟩

/-- **First-and-second-pay is not incentive compatible.** Against a bid of `1`,
a bidder of value `v ∈ (0,1)` is the runner-up: they win nothing and pay their
own bid. Shading to `0` keeps them a runner-up, so they still win nothing — but
now pay nothing, strictly improving their quasi-linear payoff from `-v` to `0`.

The payoff `v * M.x i b - M.t i b` is spelled out because I have not seen
`Auctionlib`'s utility definition; see the note below. -/
theorem lt_payoff_of_shade (M : Mechanism 2) [IsFirstAndSecondPay M]
    (hv0 : 0 < v) (hv1 : v < 1) :
    v * M.x 1 ![1, v] - M.t 1 ![1, v] < v * M.x 1 ![1, 0] - M.t 1 ![1, 0] := by
  obtain ⟨hx, ht⟩ := x_eq_zero_and_t_eq_of_isRunnerUp M (isRunnerUp_one_of_lt_one hv1)
  obtain ⟨hx0, ht0⟩ :=
    x_eq_zero_and_t_eq_of_isRunnerUp M (isRunnerUp_one_of_lt_one (v := 0) one_pos)
  have e1 : (![(1 : ℝ), v] : Fin 2 → ℝ) 1 = v := by simp
  have e0 : (![(1 : ℝ), (0 : ℝ)] : Fin 2 → ℝ) 1 = 0 := by simp
  rw [hx, ht, hx0, ht0, e1, e0]
  linarith

/-- **First-and-second-pay is not individually rational.** The same profile gives
the runner-up payoff `-v < 0`, so no normalization of the outside option at zero
can be met. -/
theorem payoff_neg (M : Mechanism 2) [IsFirstAndSecondPay M]
    (hv0 : 0 < v) (hv1 : v < 1) :
    v * M.x 1 ![1, v] - M.t 1 ![1, v] < 0 := by
  obtain ⟨hx, ht⟩ := x_eq_zero_and_t_eq_of_isRunnerUp M (isRunnerUp_one_of_lt_one hv1)
  have e1 : (![(1 : ℝ), v] : Fin 2 → ℝ) 1 = v := by simp
  rw [hx, ht, e1]
  linarith

end TwoBidders

end Mechanism

end
