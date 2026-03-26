module

public import Auctionlib.Mechanism.Basic
public import Auctionlib.ReducedForm.UniversalIC
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Density
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

/-! ### BIC -/

/-- Bayesian incentive compatibility: truthful reporting maximizes each
bidder's interim utility. -/
def BIC : Prop :=
  ∀ i, ∀ s ∈ A.interval i, ∀ s' ∈ A.interval i,
    s * A.q i s' - A.p i s' ≤ A.U i s

end Auction

end
