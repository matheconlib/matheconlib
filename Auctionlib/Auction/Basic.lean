module

public import Auctionlib.Mechanism.UniversalIC
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Density

/-!
# Auction

`Auction` captures an auction with `n` bidders drawing types from a common
distribution `typeDist`.  It consumes a `Mechanism` — the interim mechanism
induced by equilibrium play.

The CDF is `ProbabilityTheory.cdf typeDist` from Mathlib, giving us
monotonicity, range in `[0, 1]`, and limits at ±∞ for free.

Mechanism properties (`HasMonotoneStrategy`, `HasContinuousCost`, etc.) and
auction-specific structure (order-statistic characterization, density) are
expressed via typeclasses, keeping the base type minimal.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory

/-- An auction with `n` bidders and common type distribution `typeDist`.

Consumes a `Mechanism` (the interim mechanism induced by equilibrium play)
and adds the distributional structure. -/
structure Auction where
  /-- The interim mechanism induced by this auction's equilibrium -/
  mechanism : Mechanism
  /-- number of bidders -/
  n : ℕ
  /-- common type distribution -/
  typeDist : Measure ℝ
  /-- type distribution is a probability measure -/
  typeDist_prob : IsProbabilityMeasure typeDist

namespace Auction

variable (A : Auction)

instance : IsProbabilityMeasure A.typeDist := A.typeDist_prob

/-- The common CDF, derived from the type distribution via Mathlib. -/
noncomputable abbrev F : ℝ → ℝ := cdf A.typeDist

/-- The type interval from the underlying mechanism. -/
abbrev typeInterval : Set ℝ := A.mechanism.typeInterval

/-! ### Auction-specific typeclasses -/

/-- Winning probability characterized via order statistics:
`winProb(b) = F(v₀)^(n-1)` where `v₀` is the threshold type.

This holds in symmetric monotone-strategy equilibria of IPV auctions. -/
class HasOrderStatWinProb (A : Auction) : Prop where
  winProb_eq : ∀ b, ∃ v₀ ∈ A.mechanism.typeInterval,
    (∀ v ∈ A.mechanism.typeInterval, v < v₀ → A.mechanism.strategy v < b) ∧
    (∀ v ∈ A.mechanism.typeInterval, A.mechanism.strategy v < b → v ≤ v₀) ∧
    A.mechanism.winProb b = A.F v₀ ^ (A.n - 1)

/-- The type distribution has a continuous density that is strictly positive
on the interior of the type interval.  This is the key condition enabling
strict monotonicity of the equilibrium strategy. -/
class HasPosDensity (A : Auction) where
  /-- density function -/
  f : ℝ → ℝ
  /-- CDF equals integral of density on the type interval -/
  F_eq_integral : ∀ v ∈ A.typeInterval,
    A.F v = ∫ t in A.mechanism.lowestType..v, f t
  /-- density is continuous on the type interval -/
  f_continuous : ContinuousOn f A.typeInterval
  /-- density is strictly positive on the interior -/
  f_pos : ∀ v ∈ Ioo A.mechanism.lowestType A.mechanism.highestType, 0 < f v

end Auction

end
