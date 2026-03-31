module

public import Auctionlib.Mechanism.Basic
public import Auctionlib.ReducedForm.TypeDeviationIC
public import Mathlib.Probability.Notation

/-!
# Auction — Environment + Mechanism + Probability

An `Auction` combines:
- A `Mechanism n` (the rules: allocation + payment over bid vectors)
- A probability space `(Ω, ℙ)` with type random variables `θ`
- Type bounds `θmin`, `θmax`

Interim quantities (`q`, `p`, `U`) and incentive compatibility (`BIC`)
are defined on `Auction`.

The link to `ReducedForm` (the per-bidder analytic view used for the
envelope theorem) is via `Auction.toReducedForm`.
-/

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

/-! ### Interim quantities (computed from probabilistic data) -/

/-- Interim allocation: `q(i, s) = 𝔼[xᵢ(s, θ₋ᵢ)]`. -/
noncomputable def q (i : Fin n) (s : ℝ) : ℝ :=
  𝔼[fun ω => A.rules.x i <| Function.update (A.θ · ω) i s]

/-- Interim payment: `p(i, s) = 𝔼[tᵢ(s, θ₋ᵢ)]`. -/
noncomputable def p (i : Fin n) (s : ℝ) : ℝ :=
  𝔼[fun ω => A.rules.t i <| Function.update (A.θ · ω) i s]

/-- Interim utility: `U(i, s) = s · q(i, s) - p(i, s)`. -/
noncomputable def U (i : Fin n) (s : ℝ) : ℝ := s * A.q i s - A.p i s

/-! ### Strategy-dependent interim quantities

When opponents play strategy `σ` instead of reporting truthfully,
the interim quantities take `σ(θⱼ)` as opponent bids rather than `θⱼ`. -/

/-- Interim allocation when opponents play strategy `σ`:
`q_strat(σ, i, b) = 𝔼[xᵢ(b, σ(θ₋ᵢ))]`. -/
noncomputable def q_strat (σ : ℝ → ℝ) (i : Fin n) (b : ℝ) : ℝ :=
  𝔼[fun ω => A.rules.x i <| Function.update (fun j => σ (A.θ j ω)) i b]

/-- Interim payment when opponents play strategy `σ`:
`p_strat(σ, i, b) = 𝔼[tᵢ(b, σ(θ₋ᵢ))]`. -/
noncomputable def p_strat (σ : ℝ → ℝ) (i : Fin n) (b : ℝ) : ℝ :=
  𝔼[fun ω => A.rules.t i <| Function.update (fun j => σ (A.θ j ω)) i b]

/-- The standard interim allocation is `q_strat` with `σ = id`. -/
lemma q_eq_q_strat_id (i : Fin n) (s : ℝ) : A.q i s = A.q_strat id i s := rfl

/-- The standard interim payment is `p_strat` with `σ = id`. -/
lemma p_eq_p_strat_id (i : Fin n) (s : ℝ) : A.p i s = A.p_strat id i s := rfl

/-- `q_strat` takes values in `[0, 1]` when allocation is valid. -/
lemma q_strat_range (hx : A.rules.HasValidAllocation) {σ : ℝ → ℝ} (hσ : Measurable σ)
    (i : Fin n) (b : ℝ) : A.q_strat σ i b ∈ Icc 0 1 := by
  simp only [q_strat, mem_Icc]
  have hmeas : Measurable fun ω => A.rules.x i
      (Function.update (fun j => σ (A.θ j ω)) i b) :=
    (A.rules.x_measurable i).comp (measurable_pi_lambda _ fun j => by
      simp only [Function.update_apply]
      split_ifs
      · exact measurable_const
      · exact hσ.comp (A.θ_measurable j))
  have hint : Integrable (fun ω => A.rules.x i
      (Function.update (fun j => σ (A.θ j ω)) i b)) ℙ :=
    integrable_const (1 : ℝ) |>.mono hmeas.aestronglyMeasurable <|
      ae_of_all _ fun ω => by
        simpa [Real.norm_eq_abs, abs_of_nonneg (hx i _).1] using (hx i _).2
  refine ⟨integral_nonneg fun ω => (hx i _).1, ?_⟩
  calc 𝔼[fun ω => A.rules.x i (Function.update (fun j => σ (A.θ j ω)) i b)]
    _ ≤ ∫ _, (1 : ℝ) ∂ℙ :=
      integral_mono hint (integrable_const 1) fun ω => (hx i _).2
    _ = 1 := by rw [integral_const]; simp [Measure.real, measure_univ]

/-- Interim allocation takes values in `[0, 1]`.
Requires `x_range` on the mechanism's allocation rule. -/
lemma q_range (hx : A.rules.HasValidAllocation) (i : Fin n) (s : ℝ) :
    A.q i s ∈ Icc 0 1 := by
  simp only [q, mem_Icc]
  have hmeas : Measurable fun ω => A.rules.x i <| Function.update (A.θ · ω) i s :=
    (A.rules.x_measurable i).comp (measurable_pi_lambda _ fun j => by
      simp only [Function.update_apply]
      split_ifs
      · exact measurable_const
      · exact A.θ_measurable j)
  have hint : Integrable (fun ω => A.rules.x i <| Function.update (A.θ · ω) i s) ℙ :=
    integrable_const (1 : ℝ) |>.mono hmeas.aestronglyMeasurable <|
      ae_of_all _ fun ω => by
        simpa [Real.norm_eq_abs, abs_of_nonneg (hx i _).1] using (hx i _).2
  refine ⟨integral_nonneg fun ω => (hx i _).1, ?_⟩
  calc 𝔼[fun ω => A.rules.x i (Function.update (A.θ · ω) i s)]
    _ ≤ ∫ _, (1 : ℝ) ∂ℙ :=
      integral_mono hint (integrable_const 1) fun ω => (hx i _).2
    _ = 1 := by rw [integral_const]; simp [Measure.real, measure_univ]

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
def BIC : Prop :=
  ∀ i, ∀ s ∈ A.interval i, ∀ s' ∈ A.interval i,
    s * A.q i s' - A.p i s' ≤ A.U i s

/-! ### Bridge: Auction → ReducedForm -/

/-- Construct the reduced-form direct mechanism for bidder `i`.
In the direct mechanism, `strategy = id` (truthful), `winProb = q(i, ·)`,
`cost = p(i, ·)`. -/
noncomputable def toReducedForm (hx : A.rules.HasValidAllocation) (i : Fin n) :
    ReducedForm where
  lowestType := A.θmin i
  highestType := A.θmax i
  winProb := A.q i
  winProb_range s := A.q_range hx i s
  cost := A.p i
  strategy := id

@[simp] lemma toReducedForm_winProb (hx : A.rules.HasValidAllocation) (i : Fin n) :
    (A.toReducedForm hx i).winProb = A.q i := rfl
@[simp] lemma toReducedForm_cost (hx : A.rules.HasValidAllocation) (i : Fin n) :
    (A.toReducedForm hx i).cost = A.p i := rfl
@[simp] lemma toReducedForm_strategy (hx : A.rules.HasValidAllocation) (i : Fin n) :
    (A.toReducedForm hx i).strategy = id := rfl

/-- `ReducedForm.q` equals the interim allocation `q`. -/
@[simp] lemma toReducedForm_q (hx : A.rules.HasValidAllocation) (i : Fin n) (v : ℝ) :
    (A.toReducedForm hx i).q v = A.q i v := rfl

/-- `ReducedForm.U` equals the interim utility `U`. -/
@[simp] lemma toReducedForm_U (hx : A.rules.HasValidAllocation) (i : Fin n) (v : ℝ) :
    (A.toReducedForm hx i).U v = A.U i v := rfl

/-! ### BIC → HasTypeDeviationIC -/

/-- BIC implies `HasTypeDeviationIC` on the reduced form for each bidder. -/
theorem hasTypeDeviationIC_of_bic
    (hx : A.rules.HasValidAllocation) (hbic : A.BIC) (i : Fin n) :
    ReducedForm.HasTypeDeviationIC (A.toReducedForm hx i) where
  typeDeviationIC v hv v' hv' := by
    simp only [ReducedForm.payoff, toReducedForm, id]
    exact hbic i v hv v' hv'

/-! ### Consequences

Once `HasTypeDeviationIC` is established on the reduced form, all results
from the `ReducedForm` framework are automatically available:

- **Envelope theorem**: `lipschitz`, `q_monotoneOn`, `aeDifferentiable`,
  `integral_rep` (via `HasTypeDeviationIC → HasEnvelopeIC`)

- **Myerson**: `payment_identity`, `payment_unique`
-/

/-- Payment formula: under BIC, interim payment is determined by `q`. -/
theorem payment_formula (hx : A.rules.HasValidAllocation) (hbic : A.BIC)
    (i : Fin n) {s : ℝ} (hs : s ∈ A.interval i) :
    A.p i s = s * A.q i s - A.U i (A.θmin i) -
      ∫ ψ in A.θmin i..s, A.q i ψ := by
  have := A.hasTypeDeviationIC_of_bic hx hbic i
  exact (A.toReducedForm hx i).payment_identity s hs

/-- **General Payment Equivalence.**

Two BIC auctions with the same interim allocation `q`, same type bounds,
and same base utility `U(θmin)` have the same interim payment for every type.

No efficiency, symmetry, or distributional assumptions needed.
The two auctions may live on different probability spaces. -/
theorem payment_equivalence
    {Ω₂ : Type} [MeasureSpace Ω₂] [IsProbabilityMeasure (ℙ : Measure Ω₂)]
    (A₂ : Auction Ω₂ n)
    (hx₁ : A.rules.HasValidAllocation) (hx₂ : A₂.rules.HasValidAllocation)
    (hbic₁ : A.BIC) (hbic₂ : A₂.BIC)
    (i j : Fin n)
    (hθmin : A.θmin i = A₂.θmin j)
    (hθmax : A.θmax i = A₂.θmax j)
    (hq : A.q i = A₂.q j)
    (hU : A.U i (A.θmin i) = A₂.U j (A₂.θmin j))
    {s : ℝ} (hs₁ : s ∈ A.interval i) :
    A.p i s = A₂.p j s := by
  have h_td1 := A.hasTypeDeviationIC_of_bic hx₁ hbic₁ i
  have h_td2 := A₂.hasTypeDeviationIC_of_bic hx₂ hbic₂ j
  exact (A.toReducedForm hx₁ i).payment_unique (A₂.toReducedForm hx₂ j)
    hθmin hθmax hq hU s hs₁

end Auction

end
