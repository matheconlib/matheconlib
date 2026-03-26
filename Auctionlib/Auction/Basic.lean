module

public import Auctionlib.Mechanism.UniversalIC
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Density
public import Mathlib.Probability.Notation

/-!
# Auction

`Auction` is the probabilistic layer: an `n`-bidder auction on `(Ω, ℙ)` with
type random variables, allocation rule, and payment rule. It consumes a
`Mechanism` — the reduced-form mechanism seen by bidders.

## Predicates

- `IsReducedForm A i` — the mechanism matches the interim expectations for
  bidder `i` (winProb = q, cost = p, strategy = id)

## Main results

- `hasTypeDeviationIC_of_bic`: BIC + IsReducedForm → `HasTypeDeviationIC`

Once `HasTypeDeviationIC` is established, all `Mechanism` results
(envelope theorem, Myerson, payment equivalence) follow automatically.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

/-- An `n`-bidder auction on probability space `(Ω, ℙ)`.

Consumes a `Mechanism` (the reduced-form mechanism) and adds the probabilistic
model: type random variables `θ`, allocation rule `x`, payment rule `t`. -/
structure Auction (Ω : Type) [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (n : ℕ) where
  /-- The reduced-form mechanism -/
  mechanism : Mechanism
  /-- Type random variable for each bidder -/
  θ : Fin n → Ω → ℝ
  /-- Measurability of types -/
  θ_measurable : ∀ i, Measurable (θ i)
  /-- Allocation rule: probability bidder `i` wins given reported types -/
  x : Fin n → (Fin n → ℝ) → ℝ
  /-- Measurability of allocation -/
  x_measurable : ∀ i, Measurable (x i)
  /-- Allocation takes values in `[0, 1]` -/
  x_range : ∀ i w, x i w ∈ Icc 0 1
  /-- Payment rule: payment of bidder `i` given reported types -/
  t : Fin n → (Fin n → ℝ) → ℝ

namespace Auction

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} (A : Auction Ω n)

/-! ### Interim quantities (computed from probabilistic data) -/

/-- Interim allocation: `q(i, s) = 𝔼[xᵢ(s, θ₋ᵢ)]`. -/
noncomputable def q (i : Fin n) (s : ℝ) : ℝ :=
  𝔼[fun ω => A.x i <| Function.update (A.θ · ω) i s]

/-- Interim payment: `p(i, s) = 𝔼[tᵢ(s, θ₋ᵢ)]`. -/
noncomputable def p (i : Fin n) (s : ℝ) : ℝ :=
  𝔼[fun ω => A.t i <| Function.update (A.θ · ω) i s]

/-- Interim utility: `U(i, s) = s · q(i, s) - p(i, s)`. -/
noncomputable def U (i : Fin n) (s : ℝ) : ℝ := s * A.q i s - A.p i s

/-- Interim allocation takes values in `[0, 1]`. -/
lemma q_range (i : Fin n) (s : ℝ) : A.q i s ∈ Icc 0 1 := by
  simp only [q, mem_Icc]
  have hmeas : Measurable fun ω => A.x i <| Function.update (A.θ · ω) i s :=
    (A.x_measurable i).comp (measurable_pi_lambda _ fun j => by
      simp only [Function.update_apply]
      split_ifs
      · exact measurable_const
      · exact A.θ_measurable j)
  have hint : Integrable (fun ω => A.x i <| Function.update (A.θ · ω) i s) ℙ :=
    integrable_const (1 : ℝ) |>.mono hmeas.aestronglyMeasurable <|
      ae_of_all _ fun ω => by
        simpa [Real.norm_eq_abs, abs_of_nonneg (A.x_range i _).1] using (A.x_range i _).2
  refine ⟨integral_nonneg fun ω => A.x_range i _ |>.1, ?_⟩
  calc 𝔼[fun ω => A.x i (Function.update (A.θ · ω) i s)]
    _ ≤ ∫ _, (1 : ℝ) ∂ℙ :=
      integral_mono hint (integrable_const 1) fun ω => (A.x_range i _).2
    _ = 1 := by rw [integral_const]; simp [Measure.real, measure_univ]

/-! ### BIC -/

/-- Bayesian incentive compatibility: truthful reporting maximizes each
bidder's interim utility. -/
def BIC : Prop :=
  ∀ i, ∀ s ∈ A.mechanism.typeInterval,
    ∀ s' ∈ A.mechanism.typeInterval,
    s * A.q i s' - A.p i s' ≤ A.U i s

/-! ### Reduced-form predicate -/

/-- The mechanism is the **reduced-form direct mechanism** for bidder `i`:
`winProb = q(i, ·)`, `cost = p(i, ·)`, `strategy = id`. -/
class IsReducedForm (A : Auction Ω n) (i : Fin n) : Prop where
  winProb_eq : A.mechanism.winProb = A.q i
  cost_eq : A.mechanism.cost = A.p i
  strategy_eq : A.mechanism.strategy = id

/-! ### BIC → HasTypeDeviationIC -/

/-- BIC + IsReducedForm implies `HasTypeDeviationIC` on the mechanism. -/
theorem hasTypeDeviationIC_of_bic (i : Fin n) [IsReducedForm A i]
    (hbic : A.BIC) :
    Mechanism.HasTypeDeviationIC A.mechanism where
  typeDeviationIC v hv v' hv' := by
    show v * A.mechanism.winProb (A.mechanism.strategy v') -
      A.mechanism.cost (A.mechanism.strategy v') ≤
      v * A.mechanism.winProb (A.mechanism.strategy v) -
      A.mechanism.cost (A.mechanism.strategy v)
    rw [IsReducedForm.winProb_eq (i := i),
        IsReducedForm.cost_eq (i := i),
        IsReducedForm.strategy_eq (i := i)]
    simp only [id]
    exact hbic i v hv v' hv'

/-! ### Constructing a reduced-form Auction -/

/-- Construct an `Auction` whose mechanism is the reduced-form direct mechanism
for bidder `i`. This is the canonical way to create an `Auction` from raw
probabilistic data. -/
noncomputable def mkReduced
    (θ : Fin n → Ω → ℝ) (θ_measurable : ∀ i, Measurable (θ i))
    (x : Fin n → (Fin n → ℝ) → ℝ) (x_measurable : ∀ i, Measurable (x i))
    (x_range : ∀ i w, x i w ∈ Icc 0 1)
    (t : Fin n → (Fin n → ℝ) → ℝ)
    (θmin θmax : Fin n → ℝ) (i : Fin n) :
    Auction Ω n :=
  let A_temp : Auction Ω n := {
    mechanism := {
      lowestType := θmin i
      highestType := θmax i
      winProb := fun s => 𝔼[fun ω => x i <| Function.update (θ · ω) i s]
      winProb_range := by
        intro s; simp only [mem_Icc]
        have hmeas : Measurable fun ω => x i <| Function.update (θ · ω) i s :=
          (x_measurable i).comp (measurable_pi_lambda _ fun j => by
            simp only [Function.update_apply]
            split_ifs
            · exact measurable_const
            · exact θ_measurable j)
        have hint : Integrable (fun ω => x i <| Function.update (θ · ω) i s) ℙ :=
          integrable_const (1 : ℝ) |>.mono hmeas.aestronglyMeasurable <|
            ae_of_all _ fun ω => by
              simpa [Real.norm_eq_abs, abs_of_nonneg (x_range i _).1] using (x_range i _).2
        exact ⟨integral_nonneg fun ω => x_range i _ |>.1,
          calc 𝔼[fun ω => x i (Function.update (θ · ω) i s)]
            _ ≤ ∫ _, (1 : ℝ) ∂ℙ :=
              integral_mono hint (integrable_const 1) fun ω => (x_range i _).2
            _ = 1 := by rw [integral_const]; simp [Measure.real, measure_univ]⟩
      cost := fun s => 𝔼[fun ω => t i <| Function.update (θ · ω) i s]
      strategy := id
    }
    θ := θ
    θ_measurable := θ_measurable
    x := x
    x_measurable := x_measurable
    x_range := x_range
    t := t
  }
  A_temp

/-- The mechanism constructed by `mkReduced` satisfies `IsReducedForm`. -/
instance mkReduced_isReducedForm
    (θ : Fin n → Ω → ℝ) (θ_measurable : ∀ i, Measurable (θ i))
    (x : Fin n → (Fin n → ℝ) → ℝ) (x_measurable : ∀ i, Measurable (x i))
    (x_range : ∀ i w, x i w ∈ Icc 0 1)
    (t : Fin n → (Fin n → ℝ) → ℝ)
    (θmin θmax : Fin n → ℝ) (i : Fin n) :
    (mkReduced θ θ_measurable x x_measurable x_range t θmin θmax i).IsReducedForm i where
  winProb_eq := rfl
  cost_eq := rfl
  strategy_eq := rfl

end Auction

end
