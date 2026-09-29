module

public import MathEconLib.Mechanism.Basic
public import MathEconLib.BidderProblem.TypeDeviationIC
public import Mathlib.Probability.Notation

/-! # Auction — Environment + Mechanism + Probability -/

namespace MathEconLib

@[expose] public section

open MeasureTheory ProbabilityTheory Set

/-- An `n`-bidder auction on probability space `(Ω, ℙ)`.

Combines a `Mechanism` (the rules) with the probabilistic environment:
type random variables `θ` and type bounds. -/
structure Auction (Ω : Type) [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (n : ℕ) where
  /-- The auction rules (allocation + payment) -/
  rules : Mechanism n
  /-- Minimum type for each bidder -/
  θmin : Fin n → ℝ
  /-- Maximum type for each bidder -/
  θmax : Fin n → ℝ
  /-- Type random variable for each bidder -/
  θ : Fin n → Ω → ℝ
  /-- Measurability of types -/
  θ_measurable : ∀ i, Measurable (θ i)

namespace Auction

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} (A : Auction Ω n)

/-- Type interval for bidder `i`. -/
abbrev interval (i : Fin n) : Set ℝ := Icc (A.θmin i) (A.θmax i)

/-! ### Strategy-dependent interim quantities

When opponents play strategy `σ` instead of reporting truthfully,
the interim quantities take `σ(θⱼ)` as opponent bids rather than `θⱼ`.
The standard interim quantities `q`, `p` are the `σ = id` special case. -/

/-- Interim allocation when opponents play strategy `σ`:
`q_strat(σ, i, b) = 𝔼[xᵢ(b, σ(θ₋ᵢ))]`. -/
noncomputable def q_strat (σ : ℝ → ℝ) (i : Fin n) (b : ℝ) : ℝ :=
  𝔼[fun ω => A.rules.x i <| Function.update (fun j => σ (A.θ j ω)) i b]

/-- Interim payment when opponents play strategy `σ`:
`p_strat(σ, i, b) = 𝔼[tᵢ(b, σ(θ₋ᵢ))]`. -/
noncomputable def p_strat (σ : ℝ → ℝ) (i : Fin n) (b : ℝ) : ℝ :=
  𝔼[fun ω => A.rules.t i <| Function.update (fun j => σ (A.θ j ω)) i b]

/-! ### Interim quantities (truthful reporting) -/

/-- Interim allocation: `q(i, s) = q_strat(id, i, s) = 𝔼[xᵢ(s, θ₋ᵢ)]`. -/
noncomputable def q (i : Fin n) (s : ℝ) : ℝ := A.q_strat id i s

/-- Interim payment: `p(i, s) = p_strat(id, i, s) = 𝔼[tᵢ(s, θ₋ᵢ)]`. -/
noncomputable def p (i : Fin n) (s : ℝ) : ℝ := A.p_strat id i s

/-- Interim utility: `U(i, s) = s · q(i, s) - p(i, s)`. -/
noncomputable def U (i : Fin n) (s : ℝ) : ℝ := s * A.q i s - A.p i s

/-- The standard interim allocation is `q_strat` with `σ = id`. -/
lemma q_eq_q_strat_id (i : Fin n) (s : ℝ) : A.q i s = A.q_strat id i s := rfl

/-- The standard interim payment is `p_strat` with `σ = id`. -/
lemma p_eq_p_strat_id (i : Fin n) (s : ℝ) : A.p i s = A.p_strat id i s := rfl

/-- `q_strat` takes values in `[0, 1]` when allocation is valid.
No measurability assumption on `σ`: if the integrand is not integrable,
the Bochner integral defaults to `0 ∈ [0, 1]`. -/
lemma q_strat_range [A.rules.HasValidAllocation]
    (σ : ℝ → ℝ) (i : Fin n) (b : ℝ) : A.q_strat σ i b ∈ Icc 0 1 := by
  simp only [q_strat, mem_Icc]
  have hx := Mechanism.HasValidAllocation.x_range (M := A.rules)
  refine ⟨integral_nonneg fun ω => (hx i _).1, ?_⟩
  calc 𝔼[fun ω => A.rules.x i (Function.update (fun j => σ (A.θ j ω)) i b)]
    _ ≤ ∫ _, (1 : ℝ) ∂ℙ :=
      integral_mono_of_nonneg (ae_of_all _ fun ω => (hx i _).1)
        (integrable_const 1) (ae_of_all _ fun ω => (hx i _).2)
    _ = 1 := by rw [integral_const]; simp [Measure.real, measure_univ]

/-- Interim allocation takes values in `[0, 1]`. -/
lemma q_range [A.rules.HasValidAllocation] (i : Fin n) (s : ℝ) :
    A.q i s ∈ Icc 0 1 :=
  A.q_strat_range id i s

/-! ### Individual rationality -/

/-- Ex-post individual rationality: every bidder gets non-negative utility
for every type realization. -/
def ExPostIR : Prop :=
  ∀ i, ∀ θ : Fin n → ℝ, (∀ j, θ j ∈ A.interval j) →
    0 ≤ θ i * A.rules.x i θ - A.rules.t i θ

/-- Interim individual rationality: every bidder gets non-negative
expected utility for every type. -/
def InterimIR : Prop :=
  ∀ i, ∀ s ∈ A.interval i, 0 ≤ A.U i s

/-- Ex-ante individual rationality: every bidder gets non-negative
ex-ante expected utility. -/
def ExAnteIR : Prop :=
  ∀ i, 0 ≤ 𝔼[fun ω => A.θ i ω * A.rules.x i (A.θ · ω) - A.rules.t i (A.θ · ω)]

/-! ### BIC -/

/-- Bayesian incentive compatibility: truthful reporting maximizes each
bidder's interim utility. -/
class BIC : Prop where
  bic : ∀ i, ∀ s ∈ A.interval i, ∀ s' ∈ A.interval i,
    s * A.q i s' - A.p i s' ≤ A.U i s

/-! ### Bridge: Auction → BidderProblem -/

/-- Construct the per-bidder interim view for bidder `i` when opponents
play strategy `σ`. `winProb = q_strat(σ, i, ·)`, `cost = p_strat(σ, i, ·)`,
`strategy = σ`. The direct mechanism is the `σ = id` case. -/
noncomputable def toBidderProblem [A.rules.HasValidAllocation]
    (σ : ℝ → ℝ) (i : Fin n) : BidderProblem where
  lowestType := A.θmin i
  highestType := A.θmax i
  winProb := A.q_strat σ i
  winProb_range := A.q_strat_range σ i
  cost := A.p_strat σ i
  strategy := σ

variable [A.rules.HasValidAllocation] in
@[simp] lemma toBidderProblem_winProb
    (σ : ℝ → ℝ) (i : Fin n) (b : ℝ) :
    (A.toBidderProblem σ i).winProb b = A.q_strat σ i b := rfl
variable [A.rules.HasValidAllocation] in
@[simp] lemma toBidderProblem_cost
    (σ : ℝ → ℝ) (i : Fin n) (b : ℝ) :
    (A.toBidderProblem σ i).cost b = A.p_strat σ i b := rfl
variable [A.rules.HasValidAllocation] in
@[simp] lemma toBidderProblem_strategy
    (σ : ℝ → ℝ) (i : Fin n) (v : ℝ) :
    (A.toBidderProblem σ i).strategy v = σ v := rfl

variable [A.rules.HasValidAllocation] in
/-- `BidderProblem.q` equals the interim allocation `q` (direct mechanism). -/
@[simp] lemma toBidderProblem_q (i : Fin n) (v : ℝ) :
    (A.toBidderProblem id i).q v = A.q i v := rfl

variable [A.rules.HasValidAllocation] in
/-- `BidderProblem.U` equals the interim utility `U` (direct mechanism). -/
@[simp] lemma toBidderProblem_U (i : Fin n) (v : ℝ) :
    (A.toBidderProblem id i).U v = A.U i v := rfl

/-! ### BIC → HasTypeDeviationIC -/

/-- BIC implies `HasTypeDeviationIC` on the bidder problem for each bidder. -/
instance hasTypeDeviationIC_of_bic
    [A.rules.HasValidAllocation] [hbic : A.BIC] (i : Fin n) :
    BidderProblem.HasTypeDeviationIC (A.toBidderProblem id i) where
  typeDeviationIC v hv v' hv' := by
    simp only [BidderProblem.payoff]
    exact hbic.bic i v hv v' hv'

/-! ### Consequences

Once `HasTypeDeviationIC` is established on the bidder problem, all results
from the `BidderProblem` framework are automatically available:

- **Envelope theorem**: `lipschitz`, `q_monotoneOn`, `aeDifferentiable`,
  `integral_rep` (via `HasTypeDeviationIC → HasEnvelopeIC`)

- **Myerson**: `payment_identity`, `payment_unique`
-/

/-- Payment formula: under BIC, interim payment is determined by `q`. -/
theorem payment_formula [A.rules.HasValidAllocation] [A.BIC]
    (i : Fin n) {s : ℝ} (hs : s ∈ A.interval i) :
    A.p i s = s * A.q i s - A.U i (A.θmin i) -
      ∫ ψ in A.θmin i..s, A.q i ψ :=
  (A.toBidderProblem id i).payment_identity s hs

/-- **General Payment Equivalence.**

Two BIC auctions with the same interim allocation `q`, same type bounds,
and same base utility `U(θmin)` have the same interim payment for every type.

No efficiency, symmetry, or distributional assumptions needed.
The two auctions may live on different probability spaces. -/
theorem payment_equivalence
    {Ω₂ : Type} [MeasureSpace Ω₂] [IsProbabilityMeasure (ℙ : Measure Ω₂)]
    (A₂ : Auction Ω₂ n)
    [A.rules.HasValidAllocation] [A₂.rules.HasValidAllocation]
    [A.BIC] [A₂.BIC]
    (i j : Fin n)
    (hθmin : A.θmin i = A₂.θmin j)
    (hθmax : A.θmax i = A₂.θmax j)
    (hq : A.q i = A₂.q j)
    (hU : A.U i (A.θmin i) = A₂.U j (A₂.θmin j))
    {s : ℝ} (hs₁ : s ∈ A.interval i) :
    A.p i s = A₂.p j s :=
  (A.toBidderProblem id i).payment_unique (A₂.toBidderProblem id j)
    hθmin hθmax hq hU s hs₁

end Auction

end

end MathEconLib
