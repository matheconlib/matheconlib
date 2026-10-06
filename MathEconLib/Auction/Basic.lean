/-
Copyright (c) 2026 Ruiz Chen, Scott Duke Kominers, Daniel Lyng, Jujian Zhang. All rights reserved.
Released under license as described in the file LICENSE.
Authors: Ruiz Chen, Scott Duke Kominers, Daniel Lyng, Jujian Zhang
-/
module

public import MathEconLib.BidderProblem.TypeDeviationIC
public import MathEconLib.Mechanism.Auctions.Allocation
public import Mathlib.Probability.Notation

/-!
# Auctions with random bidder values

An auction combines rules for allocating goods and making transfers with a probability distribution
over bidder values. Bidders submit real bids, and the rules return an allocation vector and signed
transfers, with positive transfers paid to bidders. Interim allocation and payment average over
opponents' bids, either under a common strategy or truthful reporting.

Allocation rules and bidder values are measurable. Under a measurable strategy, allocations in
`[0, 1]` are integrable. The interim definitions also allow arbitrary strategies: their Bochner
integrals are zero when the integrands are not integrable. Payment integrability is a separate
condition and does not follow from bounded allocations.

Individual rationality and Bayesian incentive compatibility describe bidders' incentives. When each
allocation coordinate lies in `[0, 1]`, incentive compatibility determines interim payments from
the allocation rule and the utility of the lowest type, yielding payment equivalence across
auctions.

## Main definitions

* `Auction`: auction rules, random bidder values, and stated type bounds.
* `Auction.q_strat`, `Auction.p_strat`: interim allocation and payment under opponents' strategy.
* `Auction.q`, `Auction.p`, `Auction.U`: interim quantities under truthful reporting.
* `Auction.ExPostIR`, `Auction.InterimIR`, `Auction.ExAnteIR`: individual rationality conditions.
* `Auction.BIC`: Bayesian incentive compatibility.
* `Auction.toBidderProblem`: the interim decision problem faced by one bidder.

## Main statements

* `Auction.q_strat_range`: allocation coordinates in `[0, 1]` give interim allocation in `[0, 1]`.
* `Auction.payment_formula`: incentive compatibility determines interim payment from allocation and
  the utility of the lowest type.
* `Auction.payment_equivalence`: equal interim allocations and lowest-type utilities imply equal
  interim payments when type bounds agree.

## Tags

auctions, bayesian incentive compatibility, individual rationality, payment equivalence
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open MathEconLib.Mechanism.Auctions

/-- An auction with `n` bidders, indexed by `Fin n`, on the state space `Ω` with probability
measure `ℙ`. Each bidder `i` has a real-valued random value `θ i` and submits a real bid.

The rules assign an allocation vector and signed transfers to each bid profile. Positive transfers
are paid to bidders, so a bidder's payment is the negative of their transfer. The endpoints
`θmin i` and `θmax i` specify the stated type interval; containment of realized values in that
interval and bounds in `[0, 1]` on each allocation coordinate are separate conditions. -/
structure Auction (Ω : Type) [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (n : ℕ) where
  /-- Allocation and signed-transfer rules for real bid profiles. -/
  rules : MathEconLib.Mechanism (Fin n) (fun _ => ℝ) (Fin n → ℝ)
  /-- Each bidder's allocation is a measurable function of the bid profile. -/
  outcome_measurable : ∀ i, Measurable (fun bids => rules.outcome bids i)
  /-- Lower endpoint of each bidder's stated type interval. -/
  θmin : Fin n → ℝ
  /-- Upper endpoint of each bidder's stated type interval. -/
  θmax : Fin n → ℝ
  /-- Each bidder's real-valued random value as a function of the state. -/
  θ : Fin n → Ω → ℝ
  /-- Each bidder's value is measurable on the state space. -/
  θ_measurable : ∀ i, Measurable (θ i)

namespace Auction

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} (A : Auction Ω n)

/-- Type interval for bidder `i`. -/
abbrev interval (i : Fin n) : Set ℝ := Icc (A.θmin i) (A.θmax i)

/-! ### Strategy-dependent interim quantities

When opponents play strategy `σ` instead of reporting truthfully, the interim quantities take
`σ(θⱼ)` as opponent bids rather than `θⱼ`. The standard interim quantities `q`, `p` are the
`σ = id` special case. -/

/-- Interim allocation when opponents play strategy `σ`: `q_strat(σ, i, b) = 𝔼[xᵢ(b, σ(θ₋ᵢ))]`. No
measurability of `σ` is assumed. This is a totalized Bochner integral, equal to zero if the
allocation integrand is not integrable. Measurable strategies and allocations in `[0, 1]` ensure
integrability. -/
noncomputable def q_strat (σ : ℝ → ℝ) (i : Fin n) (b : ℝ) : ℝ :=
  𝔼[fun ω => A.rules.outcome (Function.update (fun j => σ (A.θ j ω)) i b) i]

/-- Expected payment by bidder `i` bidding `b` when opponents play strategy `σ`:
`p_strat(σ, i, b) = 𝔼[tᵢ(b, σ(θ₋ᵢ))]`. Payment is the negative of the signed transfer. No
measurability of `σ` or integrability of payments is assumed. This totalized Bochner integral
equals zero if the payment integrand is not integrable. Payment integrability requires separate
hypotheses, even when the strategy is measurable and allocations are bounded. -/
noncomputable def p_strat (σ : ℝ → ℝ) (i : Fin n) (b : ℝ) : ℝ :=
  𝔼[fun ω => A.rules.payment i <| Function.update (fun j => σ (A.θ j ω)) i b]

/-- A bidder's allocation is measurable in the state when opponents use a measurable strategy. -/
lemma measurable_allocation_strat {σ : ℝ → ℝ} (hσ : Measurable σ) (i : Fin n) (b : ℝ) :
    Measurable (fun ω => A.rules.outcome (Function.update (fun j => σ (A.θ j ω)) i b) i) :=
  (A.outcome_measurable i).comp <| measurable_update_left.comp <|
    measurable_pi_lambda _ fun j => hσ.comp (A.θ_measurable j)

/-- Allocations in `[0, 1]` are integrable under measurable opponents' strategies. -/
lemma integrable_allocation_strat (halloc : IsUnitIntervalAllocation A.rules (fun o i => o i))
    {σ : ℝ → ℝ} (hσ : Measurable σ) (i : Fin n) (b : ℝ) :
    Integrable (fun ω => A.rules.outcome (Function.update (fun j => σ (A.θ j ω)) i b) i) := by
  refine (integrable_const (1 : ℝ)).mono'
    (A.measurable_allocation_strat hσ i b).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (halloc i _).1]
  exact (halloc i _).2

/-! ### Interim quantities (truthful reporting) -/

/-- Interim allocation: `q(i, s) = q_strat(id, i, s) = 𝔼[xᵢ(s, θ₋ᵢ)]`. -/
noncomputable def q (i : Fin n) (s : ℝ) : ℝ := A.q_strat id i s

/-- Interim payment: `p(i, s) = p_strat(id, i, s) = 𝔼[tᵢ(s, θ₋ᵢ)]`. -/
noncomputable def p (i : Fin n) (s : ℝ) : ℝ := A.p_strat id i s

/-- Interim utility: `U(i, s) = s · q(i, s) - p(i, s)`. -/
noncomputable def U (i : Fin n) (s : ℝ) : ℝ := s * A.q i s - A.p i s

/-- A bidder's allocation is measurable in the state when opponents report truthfully. -/
lemma measurable_allocation (i : Fin n) (b : ℝ) :
    Measurable (fun ω => A.rules.outcome (Function.update (fun j => A.θ j ω) i b) i) :=
  A.measurable_allocation_strat measurable_id i b

/-- Allocations in `[0, 1]` are integrable when opponents report truthfully. -/
lemma integrable_allocation (halloc : IsUnitIntervalAllocation A.rules (fun o i => o i))
    (i : Fin n) (b : ℝ) :
    Integrable (fun ω => A.rules.outcome (Function.update (fun j => A.θ j ω) i b) i) :=
  A.integrable_allocation_strat halloc measurable_id i b

/-- The standard interim allocation is `q_strat` with `σ = id`. -/
lemma q_eq_q_strat_id (i : Fin n) (s : ℝ) : A.q i s = A.q_strat id i s := rfl

/-- The standard interim payment is `p_strat` with `σ = id`. -/
lemma p_eq_p_strat_id (i : Fin n) (s : ℝ) : A.p i s = A.p_strat id i s := rfl

/-- Interim allocation under any opponents' strategy takes values in `[0, 1]` when each allocation
coordinate lies in `[0, 1]`. -/
lemma q_strat_range (halloc : IsUnitIntervalAllocation A.rules (fun o i => o i))
    (σ : ℝ → ℝ) (i : Fin n) (b : ℝ) : A.q_strat σ i b ∈ Icc 0 1 := by
  simp only [q_strat, mem_Icc]
  refine ⟨integral_nonneg fun ω => (halloc i _).1, ?_⟩
  calc 𝔼[fun ω => A.rules.outcome (Function.update (fun j => σ (A.θ j ω)) i b) i]
    _ ≤ ∫ _, (1 : ℝ) ∂ℙ :=
      integral_mono_of_nonneg (ae_of_all _ fun ω => (halloc i _).1)
        (integrable_const 1) (ae_of_all _ fun ω => (halloc i _).2)
    _ = 1 := by rw [integral_const]; simp [Measure.real, measure_univ]

/-- Interim allocation takes values in `[0, 1]` when each allocation coordinate lies in `[0, 1]`. -/
lemma q_range (halloc : IsUnitIntervalAllocation A.rules (fun o i => o i))
    (i : Fin n) (s : ℝ) :
    A.q i s ∈ Icc 0 1 :=
  A.q_strat_range halloc id i s

/-! ### Individual rationality -/

/-- Ex-post individual rationality: every bidder gets nonnegative utility for every type
realization. -/
def ExPostIR : Prop :=
  ∀ i, ∀ θ : Fin n → ℝ, (∀ j, θ j ∈ A.interval j) →
    0 ≤ θ i * A.rules.outcome θ i + A.rules.transfer i θ

/-- Interim individual rationality: every bidder gets nonnegative expected utility for every
type. -/
def InterimIR : Prop :=
  ∀ i, ∀ s ∈ A.interval i, 0 ≤ A.U i s

/-- Ex-ante individual rationality: every bidder gets nonnegative ex-ante expected utility. -/
def ExAnteIR : Prop :=
  ∀ i, 0 ≤ 𝔼[fun ω => A.θ i ω * A.rules.outcome (A.θ · ω) i +
    A.rules.transfer i (A.θ · ω)]

/-! ### BIC -/

/-- Bayesian incentive compatibility: truthful reporting maximizes each bidder's interim utility. -/
class BIC : Prop where
  bic : ∀ i, ∀ s ∈ A.interval i, ∀ s' ∈ A.interval i,
    s * A.q i s' - A.p i s' ≤ A.U i s

/-! ### Bidder problems -/

/-- The interim decision problem of bidder `i` when opponents use the common strategy `σ`. A bid
`b` yields expected allocation `A.q_strat σ i b` and expected payment `A.p_strat σ i b`. The
bidder's type interval has endpoints `A.θmin i` and `A.θmax i`, and their prescribed strategy is
also `σ`. Truthful reporting corresponds to `σ = id`.

The strategy need not be measurable. Both interim quantities are totalized Bochner integrals, equal
to zero when their respective integrands are not integrable. A measurable strategy ensures
allocation integrability under `halloc`; payment integrability is a separate condition. -/
noncomputable def toBidderProblem (halloc : IsUnitIntervalAllocation A.rules (fun o i => o i))
    (σ : ℝ → ℝ) (i : Fin n) : BidderProblem where
  lowestType := A.θmin i
  highestType := A.θmax i
  winProb := A.q_strat σ i
  winProb_range := A.q_strat_range halloc σ i
  cost := A.p_strat σ i
  strategy := σ

variable (halloc : IsUnitIntervalAllocation A.rules (fun o i => o i)) in
/-- The bidder problem's allocation at a bid equals the auction's interim allocation. -/
@[simp] lemma toBidderProblem_winProb
    (σ : ℝ → ℝ) (i : Fin n) (b : ℝ) :
    (A.toBidderProblem halloc σ i).winProb b = A.q_strat σ i b := rfl

variable (halloc : IsUnitIntervalAllocation A.rules (fun o i => o i)) in
/-- The bidder problem's cost at a bid equals the auction's interim payment. -/
@[simp] lemma toBidderProblem_cost
    (σ : ℝ → ℝ) (i : Fin n) (b : ℝ) :
    (A.toBidderProblem halloc σ i).cost b = A.p_strat σ i b := rfl

variable (halloc : IsUnitIntervalAllocation A.rules (fun o i => o i)) in
/-- The bidder problem prescribes the same strategy `σ` used by opponents. -/
@[simp] lemma toBidderProblem_strategy
    (σ : ℝ → ℝ) (i : Fin n) (v : ℝ) :
    (A.toBidderProblem halloc σ i).strategy v = σ v := rfl

variable (halloc : IsUnitIntervalAllocation A.rules (fun o i => o i)) in
/-- `BidderProblem.q` equals the interim allocation `q` (direct mechanism). -/
@[simp] lemma toBidderProblem_q (i : Fin n) (v : ℝ) :
    (A.toBidderProblem halloc id i).q v = A.q i v := rfl

variable (halloc : IsUnitIntervalAllocation A.rules (fun o i => o i)) in
/-- `BidderProblem.U` equals the interim utility `U` (direct mechanism). -/
@[simp] lemma toBidderProblem_U (i : Fin n) (v : ℝ) :
    (A.toBidderProblem halloc id i).U v = A.U i v := rfl

/-! ### Incentive compatibility for bidder problems -/

/-- BIC implies `HasTypeDeviationIC` on the bidder problem for each bidder. -/
instance hasTypeDeviationIC_of_bic
    (halloc : IsUnitIntervalAllocation A.rules (fun o i => o i)) [hbic : A.BIC] (i : Fin n) :
    BidderProblem.HasTypeDeviationIC (A.toBidderProblem halloc id i) where
  typeDeviationIC v hv v' hv' := by
    simp only [BidderProblem.payoff]
    exact hbic.bic i v hv v' hv'

/-! ### Consequences

Bayesian incentive compatibility implies the envelope formula for interim utility. Interim
payments therefore depend only on the allocation rule and the utility of the lowest type. -/

/-- Under BIC and allocation coordinate bounds in `[0, 1]`, interim payment is determined by `q`
and the utility of the lowest type. -/
theorem payment_formula (halloc : IsUnitIntervalAllocation A.rules (fun o i => o i)) [A.BIC]
    (i : Fin n) {s : ℝ} (hs : s ∈ A.interval i) :
    A.p i s = s * A.q i s - A.U i (A.θmin i) -
      ∫ ψ in A.θmin i..s, A.q i ψ :=
  (A.toBidderProblem halloc id i).payment_identity s hs

/-- **General Payment Equivalence.**

Two BIC auctions with allocation coordinates in `[0, 1]`, the same interim allocation `q`, the same
type bounds, and the same base utility `U(θmin)` have the same interim payment for every type in
their common type interval.

No efficiency, symmetry, or distributional assumptions needed. The two auctions may live on
different probability spaces. -/
theorem payment_equivalence
    {Ω₂ : Type} [MeasureSpace Ω₂] [IsProbabilityMeasure (ℙ : Measure Ω₂)]
    (A₂ : Auction Ω₂ n)
    (halloc : IsUnitIntervalAllocation A.rules (fun o i => o i))
    (halloc₂ : IsUnitIntervalAllocation A₂.rules (fun o i => o i))
    [A.BIC] [A₂.BIC]
    (i j : Fin n)
    (hθmin : A.θmin i = A₂.θmin j)
    (hθmax : A.θmax i = A₂.θmax j)
    (hq : A.q i = A₂.q j)
    (hU : A.U i (A.θmin i) = A₂.U j (A₂.θmin j))
    {s : ℝ} (hs₁ : s ∈ A.interval i) :
    A.p i s = A₂.p j s :=
  (A.toBidderProblem halloc id i).payment_unique (A₂.toBidderProblem halloc₂ id j)
    hθmin hθmax hq hU s hs₁

end Auction

end
