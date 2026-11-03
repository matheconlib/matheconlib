/-
Copyright (c) 2026 Ruiz Chen, Scott Duke Kominers, Daniel Lyng, Jujian Zhang,
Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiz Chen, Scott Duke Kominers, Daniel Lyng, Jujian Zhang, Bo Cowgill
-/
module

public import MathEconLib.BidderProblem.TypeDeviationIC
public import MathEconLib.Mechanism.Auctions.Allocation
public import MathEconLib.Mechanism.Core.BayesianIC
public import Mathlib.Probability.Notation
public import Mathlib.Probability.Independence.Basic

/-!
# Auctions with random bidder values

An auction combines rules for allocating goods and making transfers with a probability distribution
over bidder values. Bidders submit real bids, and the rules return an allocation vector and signed
transfers, with positive transfers paid to bidders. The carrier allows correlated values. The
quantities called interim allocation and payment below average over the unconditional law of
opponents' bids, either under a common strategy or truthful reporting. They represent a bidder's
interim beliefs under independent types; they do not condition on the bidder's own value.

Allocation rules and bidder values are measurable. Under a measurable strategy, allocations in
`[0, 1]` are integrable. The interim definitions also allow arbitrary strategies: their Bochner
integrals are zero when the integrands are not integrable. Payment integrability is a separate
condition and does not follow from bounded allocations.

`BIC` and `InterimIR` use selected true-type conditional beliefs and allow correlation. `IPV.BIC`
specializes the same incentive predicate to constant opponent beliefs under independent types.
In that specialization, allocation coordinates in `[0, 1]` and incentive compatibility determine
interim payments from allocations and lowest-type utility, yielding payment equivalence.

## Main definitions

* `Auction`: auction rules, random bidder values, and stated type bounds.
* `Auction.q_strat`, `Auction.p_strat`: interim allocation and payment under opponents' strategy.
* `Auction.q`, `Auction.p`, `Auction.U`: interim quantities under truthful reporting.
* `Auction.ExPostIR`, `Auction.InterimIR`, `Auction.ExAnteIR`: individual rationality conditions.
* `Auction.MarginalIR`: the unconditional participation inequality.
* `Auction.BIC`: Bayesian incentive compatibility.
* `Auction.IsIPV`, `Auction.IPV.BIC`: independent private values and the BIC specialization.
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

namespace MathEconLib

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open MathEconLib.Mechanism.Auctions
open MathEconLib.GameTheory.BayesianPrior

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

/-- Types are mutually independent. This is the independence assumption needed to interpret the
unconditional opponent averages as interim quantities under constant product beliefs. -/
class HasIndependentTypes : Prop where
  θ_indep : iIndepFun A.θ ℙ

/-- In this scalar auction carrier values are already private and linear. The minimal IPV
restriction is therefore independence alone; symmetry and density are separate assumptions. -/
abbrev IsIPV : Prop := A.HasIndependentTypes

/-- The joint law of the actual bidder values, allowing correlation. -/
noncomputable def typeLaw : Measure (Fin n → ℝ) := Measure.map (fun ω i ↦ A.θ i ω) ℙ

instance : IsProbabilityMeasure A.typeLaw := by
  unfold typeLaw
  infer_instance

/-- The scalar auction valuation environment; private values are constitutive of this carrier. -/
def valuationEnvironment (n : ℕ) :
    Mechanism.QuasilinearEnvironment (Fin n) (fun _ ↦ ℝ) (Fin n → ℝ) :=
  Mechanism.QuasilinearEnvironment.ofPrivate fun i s x ↦ s * x i

/-- Conditional utility keeps true type `s` fixed when the bidder reports `r`. -/
noncomputable abbrev conditionalUtility (B : ConditionalBeliefs A.typeLaw)
    (i : Fin n) (s r : ℝ) : ℝ :=
  Mechanism.DirectMechanism.Quasilinear.interimUtility
    (valuationEnvironment n) A.rules A.typeLaw B i s r

/-- Independence of each coordinate and its opponents under the joint value law. -/
theorem independentOfOpponents [A.IsIPV] : IsIndependentOfOpponents A.typeLaw := by
  classical
  have hcoords : iIndepFun (fun i (θ : Fin n → ℝ) ↦ θ i) A.typeLaw := by
    have hlaw := (iIndepFun_iff_map_fun_eq_pi_map
      (fun i ↦ (A.θ_measurable i).aemeasurable)).mp
      (HasIndependentTypes.θ_indep (A := A))
    change iIndepFun _ (Measure.map (fun ω i ↦ A.θ i ω) ℙ)
    rw [hlaw]
    exact iIndepFun_pi (fun _ ↦ measurable_id.aemeasurable)
  intro i
  let S : Finset (Fin n) := {i}
  let T : Finset (Fin n) := Finset.univ.erase i
  have h := hcoords.indepFun_finset S T (by simp [S, T])
    (fun j ↦ measurable_pi_apply j)
  let f : (S → ℝ) → ℝ := fun x ↦ x ⟨i, by simp [S]⟩
  let g : (T → ℝ) → OpponentProfile (fun _ : Fin n ↦ ℝ) i :=
    fun x j ↦ x ⟨j.val, by simp [T, j.property]⟩
  have hf : Measurable f := measurable_pi_apply _
  have hg : Measurable g := Measurable.of_eval fun _ ↦ measurable_pi_apply _
  change IndepFun (fun θ : Fin n → ℝ ↦ θ i)
    (fun θ (j : {j : Fin n // j ≠ i}) ↦ θ j.val) A.typeLaw
  simpa only [f, g, drop, Function.comp_def] using h.comp hf hg

/-- The constant opponent-belief version for an IPV auction, at every declared own type. -/
noncomputable def independentBeliefs [A.IsIPV] : ConditionalBeliefs A.typeLaw :=
  MathEconLib.GameTheory.BayesianPrior.independentBeliefs A.independentOfOpponents

/-- Constant independent beliefs equal the pushforward of the state-space opponent profile. -/
lemma independentBeliefs_opponents [A.IsIPV] (i : Fin n) (s : ℝ) :
    A.independentBeliefs.opponents i s =
      Measure.map (fun ω ↦ drop i (A.θ · ω)) ℙ := by
  change Measure.map (drop i) A.typeLaw = _
  exact Measure.map_map (measurable_drop i) (Measurable.of_eval A.θ_measurable)

/-- Type interval for bidder `i`. -/
abbrev interval (i : Fin n) : Set ℝ := Icc (A.θmin i) (A.θmax i)

/-! ### Strategy-dependent interim quantities

When opponents play strategy `σ` instead of reporting truthfully, the marginal quantities take
`σ(θⱼ)` as opponent bids rather than `θⱼ`. The standard interim quantities `q`, `p` are the
`σ = id` special case. Under independent types these are interim expectations; for correlated
types they remain unconditional averages and do not describe conditional incentives. -/

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
    Measurable.of_eval fun j => hσ.comp (A.θ_measurable j)

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

/-- Nonnegative marginal utility at every type. Under independent types, unit-interval allocation
bounds, and integrable conditional truthful utilities, this is interim IR with constant product
beliefs. Without the allocation bounds, integrability of net utility alone does not justify
splitting its expectation into allocation and payment integrals. For correlated types, `U` remains
unconditional and this predicate does not assert conditional individual rationality. -/
def MarginalIR : Prop :=
  ∀ i, ∀ s ∈ A.interval i, 0 ≤ A.U i s

/-- Conditional interim individual rationality, pointwise on the declared type intervals relative
to the selected belief version. Conditional truthful utilities must be integrable. -/
def InterimIR (B : ConditionalBeliefs A.typeLaw) : Prop :=
  (∀ i, ∀ s ∈ A.interval i,
    Integrable (fun θo ↦ (valuationEnvironment n).utility A.rules i
      (insert i s θo) (Function.update (insert i s θo) i s)) (B.opponents i s)) ∧
  ∀ i, ∀ s ∈ A.interval i, 0 ≤ A.conditionalUtility B i s s

/-- Ex-ante individual rationality with finite expected utility and outside utility zero.
Every bidder's realized truthful utility is integrable and has nonnegative expectation.
Integrability is required of net utility, without requiring the allocation and transfer terms
to be separately integrable. -/
def ExAnteIR : Prop :=
  (∀ i, Integrable (fun ω => A.θ i ω * A.rules.outcome (A.θ · ω) i +
    A.rules.transfer i (A.θ · ω)) ℙ) ∧
  ∀ i, 0 ≤ 𝔼[fun ω => A.θ i ω * A.rules.outcome (A.θ · ω) i +
    A.rules.transfer i (A.θ · ω)]

/-! ### BIC -/

/-- Quasilinear conditional BIC on the stated type/report intervals, relative to selected beliefs.
The prior may correlate values. At null types, pointwise constraints use the supplied version.
This specializes the quasilinear mechanism predicate to scalar private linear values. -/
abbrev BIC (B : ConditionalBeliefs A.typeLaw) : Prop :=
  Mechanism.DirectMechanism.Quasilinear.IsBICOn
    (valuationEnvironment n) A.rules A.typeLaw B A.interval

namespace IPV

/-- The IPV specialization of quasilinear BIC uses constant opponent beliefs. Analytic and null-type
requirements are inherited from quasilinear BIC; independence is an environment assumption.

This class is a compatibility adapter to the existing inferred chain
`IPV.BIC → BidderProblem.HasTypeDeviationIC → HasEnvelopeIC`. It stores only the supplied BIC
proof, never selected belief data, and does not ask typeclass search to establish BIC. General
mechanism and correlated-auction BIC remain ordinary predicates with explicit beliefs. -/
class BIC [A.IsIPV] : Prop where
  conditional_bic : A.BIC A.independentBeliefs

end IPV

/-- Under IPV, a finite conditional utility is the usual marginal allocation/payment expression.
The conditional integrability hypothesis prevents use of a totalized nonintegrable integral. -/
lemma conditionalUtility_eq_marginal [A.IsIPV]
    (halloc : IsUnitIntervalAllocation A.rules (fun o i ↦ o i))
    (i : Fin n) (s r : ℝ)
    (hi : Integrable (fun θo ↦ (valuationEnvironment n).utility A.rules i
      (insert i s θo) (Function.update (insert i s θo) i r))
      (A.independentBeliefs.opponents i s)) :
    A.conditionalUtility A.independentBeliefs i s r = s * A.q i r - A.p i r := by
  rw [A.independentBeliefs_opponents] at hi
  have hY := (measurable_drop i).comp (Measurable.of_eval A.θ_measurable)
  have hiω := (integrable_map_measure hi.aestronglyMeasurable hY.aemeasurable).mp hi
  have heq (ω : Ω) :
      (valuationEnvironment n).utility A.rules i
        (insert i s (drop i (A.θ · ω)))
        (Function.update (insert i s (drop i (A.θ · ω))) i r) =
      s * A.rules.outcome (Function.update (A.θ · ω) i r) i -
        A.rules.payment i (Function.update (A.θ · ω) i r) := by
    simp [insert_drop_eq_update, valuationEnvironment,
      Mechanism.QuasilinearEnvironment.ofPrivate]
  simp only [Function.comp_def, heq] at hiω
  have hx : Integrable (fun ω ↦
      s * A.rules.outcome (Function.update (A.θ · ω) i r) i) ℙ :=
    (A.integrable_allocation_strat halloc measurable_id i r).const_mul s
  have hp : Integrable (fun ω ↦ A.rules.payment i (Function.update (A.θ · ω) i r)) ℙ := by
    convert hx.sub hiω using 1
    funext ω
    dsimp
    ring
  rw [conditionalUtility, Mechanism.DirectMechanism.Quasilinear.interimUtility_eq_integral,
    A.independentBeliefs_opponents,
    integral_map (φ := fun ω ↦ drop i (A.θ · ω)) hY.aemeasurable hi.aestronglyMeasurable]
  simp only [heq]
  rw [integral_sub hx hp, integral_const_mul]
  rfl

/-- The familiar marginal report inequalities follow from the general conditional IPV predicate. -/
lemma IPV.BIC.marginal_ic [A.IsIPV] [h : IPV.BIC A]
    (halloc : IsUnitIntervalAllocation A.rules (fun o i ↦ o i))
    (i : Fin n) (s : ℝ) (hs : s ∈ A.interval i) (r : ℝ) (hr : r ∈ A.interval i) :
    s * A.q i r - A.p i r ≤ A.U i s := by
  have hb := h.conditional_bic
  simpa only [A.conditionalUtility_eq_marginal halloc i s r (hb.integrable i s hs r hr),
    A.conditionalUtility_eq_marginal halloc i s s (hb.integrable i s hs s hs), U] using
    hb.bic i s hs r hr

namespace IPV

/-- Marginal inequalities characterize the IPV specialization when all compared conditional
utilities are integrable. This is an equivalence for the selected constant-belief version,
including declared types of marginal probability zero. -/
theorem bic_iff_marginal [A.IsIPV]
    (halloc : IsUnitIntervalAllocation A.rules (fun o i ↦ o i))
    (hi : ∀ i, ∀ s ∈ A.interval i, ∀ r ∈ A.interval i,
      Integrable (fun θo ↦ (valuationEnvironment n).utility A.rules i
        (insert i s θo) (Function.update (insert i s θo) i r))
        (A.independentBeliefs.opponents i s)) :
    BIC A ↔ ∀ i, ∀ s ∈ A.interval i, ∀ r ∈ A.interval i,
      s * A.q i r - A.p i r ≤ A.U i s := by
  constructor
  · intro h
    let := h
    exact BIC.marginal_ic A halloc
  · intro h
    refine ⟨⟨hi, ?_⟩⟩
    intro i s hs r hr
    simpa only [A.conditionalUtility_eq_marginal halloc i s r (hi i s hs r hr),
      A.conditionalUtility_eq_marginal halloc i s s (hi i s hs s hs), U] using h i s hs r hr

end IPV

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

/-- IPV BIC implies `HasTypeDeviationIC` on the marginal bidder problem for each bidder. -/
instance hasTypeDeviationIC_of_bic
    (halloc : IsUnitIntervalAllocation A.rules (fun o i => o i))
    [A.IsIPV] [IPV.BIC A] (i : Fin n) :
    BidderProblem.HasTypeDeviationIC (A.toBidderProblem halloc id i) where
  typeDeviationIC v hv v' hv' := by
    simp only [BidderProblem.payoff]
    exact IPV.BIC.marginal_ic A halloc i v hv v' hv'

/-! ### Consequences

In the IPV specialization, Bayesian incentive compatibility implies the scalar envelope formula.
Marginal payments then depend only on allocations and the utility of the lowest type. -/

/-- Under IPV BIC and allocation coordinate bounds in `[0, 1]`, interim payment is determined by
`q` and the utility of the lowest type. -/
theorem payment_formula (halloc : IsUnitIntervalAllocation A.rules (fun o i => o i))
    [A.IsIPV] [IPV.BIC A]
    (i : Fin n) {s : ℝ} (hs : s ∈ A.interval i) :
    A.p i s = s * A.q i s - A.U i (A.θmin i) -
      ∫ ψ in A.θmin i..s, A.q i ψ :=
  (A.toBidderProblem halloc id i).payment_identity s hs

/-- **Payment equivalence under IPV.**

Two IPV BIC auctions with allocation coordinates in `[0, 1]`, the same marginal allocation `q`,
the same type bounds, and the same base utility `U(θmin)` have the same interim payment for every
type in their common type interval.

No efficiency or symmetry assumptions are needed. Independence is explicit in each auction's
environment, and BIC uses the constant-belief specialization. The probability spaces may differ. -/
theorem payment_equivalence
    {Ω₂ : Type} [MeasureSpace Ω₂] [IsProbabilityMeasure (ℙ : Measure Ω₂)]
    (A₂ : Auction Ω₂ n)
    (halloc : IsUnitIntervalAllocation A.rules (fun o i => o i))
    (halloc₂ : IsUnitIntervalAllocation A₂.rules (fun o i => o i))
    [A.IsIPV] [A₂.IsIPV] [IPV.BIC A] [IPV.BIC A₂]
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

end MathEconLib
