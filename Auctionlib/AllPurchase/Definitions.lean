module

public import Auctionlib.RevenueEquivalence.Theorem

/-!
# All-Purchase Auction — Foundational Definitions

This file defines the foundational structures for the All-Purchase Auction (Chapter 6),
following the project's mathematics/economics split.

## Mathematical core

`AllPurchaseCore` captures the pure analytic content of the all-purchase auction equilibrium
without probability:
- An interval `[a, b]` (type space),
- A winning probability function `G : ℝ → ℝ` (abstract, values in `[0, 1]`),
- A net expenditure function `C : ℝ → ℝ`,
- An equilibrium strategy `β : ℝ → ℝ`,
- An IC inequality stating no type benefits from mimicking another.

The key observation is that the interim payoff `U(v, b) = v · G(b) - C(b)` has increasing
differences in `(v, b)`, so the IC takes the same form as `EnvelopeSetUpMathsCore.ic`.
The coercion `AllPurchaseCore.toEnvelopeSetUpMathsCore` makes the envelope theorem
directly applicable.

## Economic structure

`AllPurchaseSetup` extends `RevenueEquivalenceSetup` with:
- A posted unit price `p_price > 0`,
- A scarcity function `φ` (continuous, strictly decreasing).

## Derived definitions

- `AllPurchaseSetup.IsSymmetricBNE`: symmetric BNE as an IC inequality.
- `AllPurchaseSetup.allPayBid`: the standard all-pay bid function.
-/

@[expose] public section

section allPurchaseCore

/-- The mathematical core of the All-Purchase Auction.

Captures the analytic content without probability, analogous to `EnvelopeSetUpMathsCore`.
A bidder with type `v ∈ [a, b]` uses strategy `β`, wins with probability `G(β(v))`,
and pays net expenditure `C(β(v))`. The interim payoff is `U(v, b) = v · G(b) - C(b)`.

The IC inequality ensures no type benefits from mimicking another type's strategy.
This feeds directly into `EnvelopeSetUpMathsCore` via `toEnvelopeSetUpMathsCore`,
with `q := G ∘ β`. -/
structure AllPurchaseCore where
  /-- lower bound of type space -/
  a : ℝ
  /-- upper bound of type space -/
  b : ℝ
  /-- winning probability function -/
  G : ℝ → ℝ
  /-- `G` takes values in `[0, 1]` -/
  G_range : ∀ x, G x ∈ Set.Icc 0 1
  /-- net expenditure function -/
  C : ℝ → ℝ
  /-- equilibrium strategy -/
  β : ℝ → ℝ
  /-- incentive compatibility: for all types `v, v' ∈ [a, b]`,
      type `v` weakly prefers bidding `β(v)` to mimicking `β(v')`. -/
  ic : ∀ v ∈ Set.Icc a b, ∀ v' ∈ Set.Icc a b,
    v * G (β v') - C (β v') ≤ v * G (β v) - C (β v)

namespace AllPurchaseCore

variable (ε : AllPurchaseCore)

/-- Marginal allocation: `q(v) = G(β(v))`, the winning probability for type `v`
in equilibrium. In a strictly increasing equilibrium, `q(v) = F(v)^{n-1}`. -/
def q : ℝ → ℝ := ε.G ∘ ε.β

lemma q_range (v : ℝ) : ε.q v ∈ Set.Icc 0 1 := ε.G_range (ε.β v)

/-- Equilibrium utility: `U(v) = v · q(v) - C(β(v))`. -/
def U (v : ℝ) : ℝ := v * ε.q v - ε.C (ε.β v)

/-- Interim payoff for type `v` choosing bid `b`:
`interimPayoff v b = v · G(b) - C(b)`. -/
def interimPayoff (v b : ℝ) : ℝ := v * ε.G b - ε.C b

lemma U_eq_interimPayoff (v : ℝ) : ε.U v = ε.interimPayoff v (ε.β v) := by
  simp [U, interimPayoff, q, Function.comp]

/-- Coercion to `EnvelopeSetUpMathsCore`: the all-purchase auction IC has the
same analytic form as the envelope theorem IC, with `q := G ∘ β`. -/
@[simps]
def toEnvelopeSetUpMathsCore : EnvelopeSetUpMathsCore where
  a := ε.a
  b := ε.b
  q := ε.q
  q_range _ _ := ε.q_range _
  U := ε.U
  ic v hv v' hv' := by
    show (v - v') * ε.G (ε.β v') ≤
      (v * ε.G (ε.β v) - ε.C (ε.β v)) - (v' * ε.G (ε.β v') - ε.C (ε.β v'))
    nlinarith [ε.ic v hv v' hv']

end AllPurchaseCore

end allPurchaseCore

section allPurchaseSetup

open MeasureTheory ProbabilityTheory

/-- The economic setup for the All-Purchase Auction (Chapter 6).

Extends `RevenueEquivalenceSetup` with the all-purchase-specific parameters:
a posted unit price and a scarcity function governing per-unit edition value. -/
structure AllPurchaseSetup (Ω : Type)
    [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (n : ℕ) [n.AtLeastTwo] extends RevenueEquivalenceSetup Ω n where
  /-- posted unit price -/
  p_price : ℝ
  /-- posted price is positive -/
  p_price_pos : 0 < p_price
  /-- scarcity function: per-unit edition value as a function of aggregate quantity -/
  φ : ℝ → ℝ
  /-- scarcity function is continuous -/
  φ_continuous : Continuous φ
  /-- scarcity function is strictly decreasing -/
  φ_strictAnti : StrictAnti φ

namespace AllPurchaseSetup

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} [n.AtLeastTwo]
variable (ε : AllPurchaseSetup Ω n)

/-- The common type interval `[lowestType, highestType]`. -/
abbrev typeInterval : Set ℝ := Set.Icc ε.lowestType ε.highestType

/-- Symmetric Bayesian Nash Equilibrium expressed as an IC inequality.

All bidders use strategy `β`. Given winning probability `G` and net expenditure `C`
(both derived from the environment and opponents' common strategy), type `v`
weakly prefers bidding `β(v)` to mimicking any other type `v'`. -/
def IsSymmetricBNE (β : ℝ → ℝ) (G : ℝ → ℝ) (C : ℝ → ℝ) : Prop :=
  ∀ v ∈ ε.typeInterval, ∀ v' ∈ ε.typeInterval,
    v * G (β v') - C (β v') ≤ v * G (β v) - C (β v)

/-- Construct an `AllPurchaseCore` from a symmetric BNE, bridging the economic
and mathematical layers. -/
noncomputable def toAllPurchaseCore (β : ℝ → ℝ) (G : ℝ → ℝ) (C : ℝ → ℝ)
    (G_range : ∀ x, G x ∈ Set.Icc 0 1)
    (hbne : ε.IsSymmetricBNE β G C) : AllPurchaseCore where
  a := ε.lowestType
  b := ε.highestType
  G := G
  G_range := G_range
  C := C
  β := β
  ic := hbne

/-- The standard all-pay bid function:
`b^{AP}(v) = v · F(v)^{n-1} - ∫_{lowestType}^{v} F(t)^{n-1} dt`.

This is the symmetric equilibrium bid in a standard all-pay auction with CDF `F`.
By the net-payment identity (Proposition 6.4), the net expenditure in the all-purchase
auction satisfies `C(β(v)) = allPayBid(v) - U(0)`. -/
noncomputable def allPayBid (v : ℝ) : ℝ :=
  v * ε.commonCDF v ^ (n - 1) - ∫ t in ε.lowestType..v, ε.commonCDF t ^ (n - 1)

@[simp]
lemma allPayBid_lowestType : ε.allPayBid ε.lowestType = 0 := by
  have hn : n - 1 ≠ 0 := by have := Nat.AtLeastTwo.prop (n := n); omega
  simp [allPayBid, zero_pow hn]

end AllPurchaseSetup

end allPurchaseSetup

end
