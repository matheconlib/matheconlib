module

public import Mathlib.Probability.Notation
public import Auctionlib.Envelope.Mathematics

/-!
# Envelope Theorem

This file specializes the analytic core from `Auctionlib.Envelope.Mathematics` to the
standard single-parameter Bayesian auction model.

## Setup

`EnvelopSetup` encodes an `n`-bidder independent private values (IPV) auction over a probability
space `(Ω, ℙ)`:
- type intervals `[θmin i, θmax i]` for each bidder `i`,
- allocation rule `xᵢ : (Fin n → ℝ) → [0, 1]`,
- payment rule `tᵢ : (Fin n → ℝ) → ℝ`.

Both the probability space `Ω` and the number of bidders `n` are *parameters* of the
structure rather than fields, so Lean's type class system handles instances automatically.

The derived quantities are:
- `q i s = 𝔼[xᵢ(s, θ₋ᵢ)]`: marginal allocation (probability of winning),
- `U i s = s * q i s - p i s`: interim utility.

## Main result

`envelop_theorem`: Bayesian incentive compatibility (`IncentiveCompatible`) implies
`EnvelopSetup.Theorem`, which states for each bidder `i`:
1. `U i` is 1-Lipschitz on `[θmin i, θmax i]`,
2. `HasDerivAt (U i) (q i s) s` for a.e. `s`,
3. `U i s = U i (θmin i) + ∫ ψ in θmin i..s, q i ψ`.

-/


@[expose] public section

section envelop

open MeasureTheory ProbabilityTheory

/--
The setup of the envelope theorem.

`Ω` is the underlying probability space and `n` is the number of bidders;
both are parameters so that type-class instances are inherited automatically.
-/
structure EnvelopSetup (Ω : Type)
    [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] (n : ℕ) where
  /-- minimum value of valuation -/
  θmin : Fin n → ℝ
  /-- maximum value of valuation -/
  θmax : Fin n → ℝ
  -- Since the inequality is not needed in the maths argument, we don't need it here
  -- θmin_le_θmax i : θmin i < θmax i

  /-- random variable: θᵢ stands for the valuation of i-th bidder -/
  θ : Fin n → Ω → ℝ
  θ_measurable i : Measurable <| θ i
  -- The assumption that θ takes value in `[θmin, θmax]` seems not be used as well
  -- θ_in i : ∀ ω, θ i ω ∈ Set.Icc (θmin i) (θmax i)

  /-- random variable: i-th bidder won-/
  x : Fin n → (Fin n → ℝ) → ℝ
  x_measure i : Measurable <| x i
  x_range i w : x i w ∈ Set.Icc 0 1

  /-- random variable: amount of money i-th bidder pay -/
  t : Fin n → (Fin n → ℝ) → ℝ

  -- the assumptions on measurability and integrability of `t` is not used
  -- t_measurable i : Measurable <| t i
  -- t_integrable i s : s ∈ Set.Icc (θmin i) (θmax i) →
  --   Integrable (fun ω => t i <| Function.update (θ · ω) i s) ℙ


namespace EnvelopSetup

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {n : ℕ}
variable (ℰ : EnvelopSetup Ω n)

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
noncomputable def toEnvelopSetUpMathsCore (i : Fin n) (ic : ℰ.IncentiveCompatible) :
    EnvelopSetUpMathsCore where
  a := ℰ.θmin i
  b := ℰ.θmax i
  q := ℰ.q i
  q_range s _ := ℰ.q_range i s
  U := ℰ.U i
  ic s hs s' hs' := by
    have hUs' : ℰ.U i s' = s' * ℰ.q i s' - ℰ.p i s' := rfl
    have expand : (s - s') * ℰ.q i s' = s * ℰ.q i s' - s' * ℰ.q i s' := by ring
    linarith [ic i s hs s' hs', hUs', expand]

end EnvelopSetup

end envelop

section proof

open MeasureTheory ProbabilityTheory

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {n : ℕ}

theorem envelop_theorem (ℰ : EnvelopSetup Ω n) : ℰ.IncentiveCompatible ≤ ℰ.Theorem := fun ic =>
  { lipschitzOnWith i :=  ℰ.toEnvelopSetUpMathsCore i ic |>.lipschitz
    aeDifferentiable i := ℰ.toEnvelopSetUpMathsCore i ic |>.aeDifferentiable
    U_eq i := ℰ.toEnvelopSetUpMathsCore i ic |>.integral_rep }

end proof

end
