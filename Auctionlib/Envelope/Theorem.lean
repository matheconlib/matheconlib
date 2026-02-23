module

public import Mathlib.Probability.Notation
public import Auctionlib.Envelope.Mathematics

/-!
# Envelope Theorem

This file specializes the analytic core from `Auctionlib.Envelope.Mathematics` to the
standard single-parameter Bayesian auction model.

## Setup

`EnvelopeSetup` encodes an `n`-bidder independent private values (IPV) auction over a probability
space `(Ω, ℙ)`:
- type intervals `[θmin i, θmax i]` for each bidder `i`,
- allocation rule `xᵢ : (Fin n → ℝ) → [0, 1]`,
- payment rule `tᵢ : (Fin n → ℝ) → ℝ`.

Both the probability space `Ω` and the number of bidders `n` are *parameters* of the
structure rather than fields, so Lean's type class system handles instances automatically.

The derived quantities are:
- `q i s = 𝔼[xᵢ(s, θ₋ᵢ)]`: marginal allocation (probability of winning),
- `U i s = s * q i s - p i s`: interim utility.

## Incentive compatibility

- `IncentiveCompatible` (BIC): truthful reporting maximizes interim expected utility.

## Individual rationality

- `ExPostIR`: non-negative utility for every type realization.
- `InterimIR`: non-negative interim expected utility for every type.
- `ExAnteIR`: non-negative ex-ante expected utility.

## Main result

- `envelope_theorem`: BIC implies the Envelope Theorem (Lipschitz, a.e. derivative, integral rep).

-/


@[expose] public section

section envelope

open MeasureTheory ProbabilityTheory

/--
The setup of the envelope theorem.

`Ω` is the underlying probability space and `n` is the number of bidders;
both are parameters so that type-class instances are inherited automatically.
-/
structure EnvelopeSetup (Ω : Type)
    [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] (n : ℕ) where
  /-- minimum value of valuation -/
  θmin : Fin n → ℝ
  /-- maximum value of valuation -/
  θmax : Fin n → ℝ

  /-- random variable: θᵢ stands for the valuation of i-th bidder -/
  θ : Fin n → Ω → ℝ
  θ_measurable i : Measurable <| θ i

  /-- random variable: i-th bidder won-/
  x : Fin n → (Fin n → ℝ) → ℝ
  x_measure i : Measurable <| x i
  x_range i w : x i w ∈ Set.Icc 0 1

  /-- random variable: amount of money i-th bidder pay -/
  t : Fin n → (Fin n → ℝ) → ℝ


namespace EnvelopeSetup

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {n : ℕ}
variable (ℰ : EnvelopeSetup Ω n)

/-- the range of valuation -/
abbrev interval (i : Fin n) : Set ℝ := Set.Icc (ℰ.θmin i) (ℰ.θmax i)

/-- Shorthand for `𝔼_{θ₋ᵢ}[xᵢ(s, θ₋ᵢ)]` -/
noncomputable def q : Fin n → ℝ → ℝ := fun i s =>
  𝔼[fun ω => ℰ.x i <| Function.update (ℰ.θ · ω) i s]

/-- Shorthand for `𝔼_{θ₋ᵢ}[tᵢ(s, θ₋ᵢ)]` -/
noncomputable def p : Fin n → ℝ → ℝ := fun i s =>
  𝔼[fun ω => ℰ.t i <| Function.update (ℰ.θ · ω) i s]

lemma q_range (i) (s) : ℰ.q i s ∈ Set.Icc 0 1 := by
  simp only [q, Set.mem_Icc]
  have hmeas : Measurable fun ω => ℰ.x i <| Function.update (ℰ.θ · ω) i s :=
    (ℰ.x_measure i).comp (measurable_pi_lambda _ fun j => by
      simp only [Function.update_apply]
      split_ifs
      · exact measurable_const
      · exact ℰ.θ_measurable j)
  have hint : Integrable (fun ω => ℰ.x i <| Function.update (ℰ.θ · ω) i s) ℙ :=
    integrable_const (1 : ℝ) |>.mono hmeas.aestronglyMeasurable <|
      ae_of_all _ fun ω => by
        simpa [Real.norm_eq_abs, abs_of_nonneg (ℰ.x_range i _).1] using (ℰ.x_range i _).2
  refine ⟨integral_nonneg fun ω => ℰ.x_range i _ |>.1, ?_⟩
  calc 𝔼[fun ω => ℰ.x i (Function.update (ℰ.θ · ω) i s)]
    _ ≤ ∫ _, (1 : ℝ) ∂ℙ := integral_mono hint (integrable_const 1) fun ω => (ℰ.x_range i _).2
    _ = 1 := by
        rw [integral_const]
        simp [Measure.real, measure_univ]

/-- Interim utility function -/
noncomputable def U : Fin n → ℝ → ℝ := fun i s => s * ℰ.q i s - ℰ.p i s

/-- Bayesian incentive compatibility: truthful reporting maximizes each bidder's
    interim utility. Bidder `i` with true type `s` cannot gain by misreporting `s'`. -/
def IncentiveCompatible : Prop :=
  ∀ i, ∀ s ∈ ℰ.interval i, ∀ s' ∈ ℰ.interval i, s * ℰ.q i s' - ℰ.p i s' ≤ ℰ.U i s

/-- Ex-post individual rationality: every bidder gets non-negative utility
    for every type realization. -/
def ExPostIR : Prop :=
  ∀ i, ∀ θ : Fin n → ℝ, (∀ j, θ j ∈ ℰ.interval j) →
    0 ≤ θ i * ℰ.x i θ - ℰ.t i θ

/-- Interim individual rationality: every bidder gets non-negative
    expected utility for every type. -/
def InterimIR : Prop :=
  ∀ i, ∀ s ∈ ℰ.interval i, 0 ≤ ℰ.U i s

/-- Ex-ante individual rationality: every bidder gets non-negative
    ex-ante expected utility. -/
def ExAnteIR : Prop :=
  ∀ i, 0 ≤ 𝔼[fun ω => ℰ.θ i ω * ℰ.x i (ℰ.θ · ω) - ℰ.t i (ℰ.θ · ω)]

/--
The statement of the envelope theorem:
- `Uᵢ` is 1-lipschitz
- `Uᵢ` is almost everywhere differentiable with derivative `qᵢ`
- `Uᵢ` is equal to `Uᵢ θmin + ∫ ψ in θmin..s, qᵢ ψ`
-/
structure Theorem : Prop where
  /-- Note: Lipschitz condition is stronger than absolute continuity, see the following lemma
  `LipschitzOnWith.absolutelyContinuousOnInterval`
  -/
  lipschitzOnWith i : LipschitzOnWith 1 (ℰ.U i) (ℰ.interval i)
  aeDifferentiable i : ∀ᵐ s ∂volume.restrict (ℰ.interval i), HasDerivAt (ℰ.U i) (ℰ.q i s) s
  U_eq i : ∀ s ∈ ℰ.interval i, ℰ.U i s = ℰ.U i (ℰ.θmin i) + ∫ ψ in ℰ.θmin i..s, ℰ.q i ψ

/-- Given a proof of incentive compatibility, construct the analytic core for agent `i` from the
full probabilistic setup. -/
@[simps]
noncomputable def toEnvelopeSetUpMathsCore (i : Fin n) (ic : ℰ.IncentiveCompatible) :
    EnvelopeSetUpMathsCore where
  a := ℰ.θmin i
  b := ℰ.θmax i
  q := ℰ.q i
  q_range s _ := ℰ.q_range i s
  U := ℰ.U i
  ic s hs s' hs' := by
    have hUs' : ℰ.U i s' = s' * ℰ.q i s' - ℰ.p i s' := rfl
    have expand : (s - s') * ℰ.q i s' = s * ℰ.q i s' - s' * ℰ.q i s' := by ring
    linarith [ic i s hs s' hs', hUs', expand]

end EnvelopeSetup

end envelope

section proof

open MeasureTheory ProbabilityTheory

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {n : ℕ}

theorem envelope_theorem (ℰ : EnvelopeSetup Ω n) : ℰ.IncentiveCompatible ≤ ℰ.Theorem := fun ic =>
  { lipschitzOnWith i :=  ℰ.toEnvelopeSetUpMathsCore i ic |>.lipschitz
    aeDifferentiable i := ℰ.toEnvelopeSetUpMathsCore i ic |>.aeDifferentiable
    U_eq i := ℰ.toEnvelopeSetUpMathsCore i ic |>.integral_rep }

end proof

section payment_equivalence

open MeasureTheory ProbabilityTheory

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {n : ℕ}

namespace EnvelopeSetup

/-- General payment formula from the Envelope Theorem.

Under IC alone, the interim expected payment is uniquely determined (up to the
constant `U(θmin)`) by the interim allocation rule `q`:

  `p(s) = s · q(s) - U(θmin) - ∫_{θmin}^s q(ψ) dψ`

No efficiency, symmetry, independence, or atomless assumptions are needed. -/
lemma payment_formula (ℰ : EnvelopeSetup Ω n) (ic : ℰ.IncentiveCompatible)
    (i : Fin n) {s : ℝ} (hs : s ∈ ℰ.interval i) :
    ℰ.p i s = s * ℰ.q i s - ℰ.U i (ℰ.θmin i) - ∫ ψ in ℰ.θmin i..s, ℰ.q i ψ := by
  have hpU : ℰ.p i s = s * ℰ.q i s - ℰ.U i s := by
    linarith [show ℰ.U i s = s * ℰ.q i s - ℰ.p i s from rfl]
  linarith [envelope_theorem ℰ ic |>.U_eq i s hs]

/-- **General Payment Equivalence.**

Any two IC mechanisms with the same interim allocation rule `q`, the same lower
bound of the type space `θmin`, and the same utility at the lowest type `U(θmin)`
must have the same interim expected payment `p` for every type.

This is the most general form of the Revenue Equivalence / Payment Equivalence
result. No efficiency, symmetry, independence, or atomless assumptions are needed.
The two mechanisms may live on different probability spaces `Ω₁`, `Ω₂`. -/
theorem payment_equivalence
    {Ω₁ : Type} [MeasureSpace Ω₁] [IsProbabilityMeasure (ℙ : Measure Ω₁)]
    {Ω₂ : Type} [MeasureSpace Ω₂] [IsProbabilityMeasure (ℙ : Measure Ω₂)]
    {n : ℕ}
    (ℰ₁ : EnvelopeSetup Ω₁ n) (ℰ₂ : EnvelopeSetup Ω₂ n)
    (ic₁ : ℰ₁.IncentiveCompatible) (ic₂ : ℰ₂.IncentiveCompatible)
    (i j : Fin n)
    (hθmin : ℰ₁.θmin i = ℰ₂.θmin j)
    (hq : ℰ₁.q i = ℰ₂.q j)
    (hU : ℰ₁.U i (ℰ₁.θmin i) = ℰ₂.U j (ℰ₂.θmin j))
    {s : ℝ} (hs₁ : s ∈ ℰ₁.interval i) (hs₂ : s ∈ ℰ₂.interval j) :
    ℰ₁.p i s = ℰ₂.p j s := by
  simp_rw [ℰ₁.payment_formula ic₁ i hs₁, ℰ₂.payment_formula ic₂ j hs₂, hU, hθmin, hq]

end EnvelopeSetup

end payment_equivalence

end
