module

public import MathEconLib.Auction.AllPurchase.Basic
public import MathEconLib.Auction.IdenticalTypes
public import MathEconLib.ForMathlib.FinsetUpdate
public import MathEconLib.Mechanism.Auctions.AllPurchase.Spec

/-!
# Linear scarcity in all-purchase auctions

With scarcity `φ(B) = φ̄ − αB`, a bidder's expected net cost of purchasing `b` editions is
`αb² + Kb`. The coefficient `K` depends on the posted price and opponents' expected purchases under
their strategy. Boundary and interior regimes specify the lowest type's utility.

## Main definitions

* `QuadraticCostProblem` and `LinearCostProblem`: bidder problems with quadratic or linear net cost.
* `BidderProblem.IsBoundaryRegime` and `InteriorRegimeProblem`: conditions on the lowest type's
  utility, with negative marginal net cost at zero purchases in the interior regime.
* `Auction.allPurchaseNetCost`: gross purchase expenditure minus expected edition value.
* `LinearScarcityAuction`: an all-purchase auction with linear scarcity.
* `LinearScarcityAuction.toQuadraticCostProblem`: a bidder's interim winning probability and
  quadratic net cost against opponents using a given strategy.

## Main statements

* `LinearScarcityAuction.expected_scarcity_linear`: expected per-edition value depends on the
  bidder's own purchase and opponents' mean purchases.
* `LinearScarcityAuction.p_strat_eq_quadratic`: interim net payment has the form `αb² + Kb`.

## Tags

all-purchase auctions, linear scarcity, quadratic cost, interim utility
-/

namespace MathEconLib

@[expose] public section

/-! ## BidderProblem-level structures -/

/-- A bidder problem with quadratic net cost `cost(b) = α · b² + K · b`, where `α > 0`. For an
all-purchase auction with linear scarcity `φ(B) = φ̄ − αB`, the coefficient is
`K = p − φ̄ + α(n−1)μ`, where `μ` is opponents' mean purchase under their common strategy. -/
structure QuadraticCostProblem extends BidderProblem where
  /-- Quadratic cost coefficient; the magnitude of the negative scarcity slope. -/
  α_coeff : ℝ
  /-- Marginal net cost at zero purchases. -/
  K_param : ℝ
  /-- dilution intensity is positive -/
  α_pos : 0 < α_coeff
  /-- the cost function equals the quadratic form -/
  cost_eq : ∀ b, toBidderProblem.cost b = α_coeff * b ^ 2 + K_param * b

/-- A bidder problem where cost is linear: `cost(b) = p_net · b`. This arises from constant
scarcity `φ(B) = u₀` in the all-purchase auction. -/
structure LinearCostProblem extends BidderProblem where
  /-- net cost per unit: `p − u₀` -/
  p_net : ℝ
  /-- net cost per unit is positive (no-arbitrage) -/
  p_net_pos : 0 < p_net
  /-- the cost function equals the linear form -/
  cost_eq : ∀ b, toBidderProblem.cost b = p_net * b

namespace BidderProblem

/-- A bidder problem in the boundary regime, with zero utility for the lowest type. -/
class IsBoundaryRegime (B : BidderProblem) : Prop where
  /-- The lowest type's utility is zero. -/
  U_lowestType_zero : B.U B.lowestType = 0

end BidderProblem

/-- A bidder problem in the interior regime: net cost is `αb² + Kb`, with `α > 0` and `K < 0`, and
the lowest type's utility is `K²/(4α)`. -/
structure InteriorRegimeProblem extends QuadraticCostProblem where
  /-- Marginal net cost at zero purchases is negative. -/
  K_neg : K_param < 0
  /-- The lowest type's utility equals the gain from minimizing quadratic net cost. -/
  U_lowestType_eq : toBidderProblem.U toBidderProblem.lowestType = K_param ^ 2 / (4 * α_coeff)

/-! ## Auction-level definitions -/

open MeasureTheory ProbabilityTheory Set Finset
open MathEconLib.Mechanism.Auctions

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} [NeZero n] [n.AtLeastTwo]

namespace Auction

variable (A : Auction Ω n) (spec : AllPurchaseSpec A.rules (fun o i => o i))

/-- Expected net cost for bidder `i` in auction `A`, using the posted unit price and scarcity
schedule supplied by `spec`. The bidder purchases `b` editions and opponents purchase according to
`β`. Net cost is gross expenditure `spec.price * b` minus the expected value of the purchased
editions, whose per-edition value depends on total purchases. -/
noncomputable def allPurchaseNetCost
    (β : ℝ → ℝ) (i : Fin n) (b : ℝ) : ℝ :=
  spec.price * b - b *
    𝔼[fun ω => spec.φ <| b + ∑ j ∈ univ.erase i, β (A.θ j ω)]

end Auction

/-! ## LinearScarcityAuction -/

/-- An all-purchase auction with `n` bidders and linear scarcity `φ(B) = φ̄ − α · B` at total
purchases `B`. The probability space `(Ω, ℙ)` describes states, and the type random variables
`θ i : Ω → ℝ` determine the bidders' joint type distribution. The all-purchase specification
supplies the posted price and scarcity schedule; `φ̄ > 0` is the schedule's intercept and `α > 0`
is the magnitude of its negative slope. -/
structure LinearScarcityAuction (Ω : Type) [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (n : ℕ)
    extends Auction Ω n where
  /-- Posted unit price, scarcity schedule, and the all-purchase allocation and payment rules. -/
  spec : AllPurchaseSpec toAuction.rules (fun o i => o i)
  /-- Per-edition value at zero total purchases. -/
  φ_bar : ℝ
  /-- Magnitude of the negative scarcity slope: the decline in per-edition value per purchase. -/
  α_coeff : ℝ
  /-- dilution intensity is positive -/
  α_pos : 0 < α_coeff
  /-- intercept is positive -/
  φ_bar_pos : 0 < φ_bar
  /-- the scarcity function is linear -/
  scarcity_is_linear : spec.φ = fun b => φ_bar - α_coeff * b

namespace LinearScarcityAuction

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} [NeZero n] [n.AtLeastTwo]
variable (A : LinearScarcityAuction Ω n) [A.HasIdenticalTypes]

/-- Mean purchase of bidder `0` under strategy `β`: `μ = 𝔼[β(θ₀)]`. For measurable `β`, identical
type distributions give each bidder the same mean purchase under this common strategy. -/
noncomputable def meanPurchase (β : ℝ → ℝ) : ℝ :=
  𝔼[fun ω => β (A.θ 0 ω)]

/-- Marginal net cost at zero purchases against opponents using strategy `β`:
`K = p − φ̄ + α(n−1)μ`, where `μ = 𝔼[β(θ₀)]` is mean purchase under `β`. -/
noncomputable def K_linear (β : ℝ → ℝ) : ℝ :=
  A.spec.price - A.φ_bar + A.α_coeff * (↑n - 1) * A.meanPurchase β

/-! ## Expected scarcity and net cost -/

omit [n.AtLeastTwo] in
/-- Expected per-edition value when bidder `i` purchases `b` and opponents use strategy `β`:
`𝔼[φ(b + B₋ᵢ)] = φ̄ − α·(b + (n−1)·μ)`. Here `μ = 𝔼[β(θ₀)]` is mean purchase under `β`; the
strategy is measurable and each bidder's purchase is integrable. -/
theorem expected_scarcity_linear
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (hβ_int : ∀ j, Integrable (fun ω => β (A.θ j ω)) ℙ)
    (i : Fin n) (b : ℝ) :
    𝔼[fun ω => A.spec.φ <|
      b + ∑ j ∈ univ.erase i, β (A.θ j ω)] =
      A.φ_bar - A.α_coeff * (b + (↑(n - 1) : ℝ) * A.meanPurchase β) := by
  have hφ : ∀ ω, (A.spec.φ <|
      b + ∑ j ∈ univ.erase i, β (A.θ j ω)) =
      (A.φ_bar - A.α_coeff * b) +
        (-A.α_coeff) * (∑ j ∈ univ.erase i, β (A.θ j ω)) := by
    intro ω
    show A.spec.φ _ = _
    have := congr_fun A.scarcity_is_linear <|
      b + ∑ j ∈ univ.erase i, β (A.θ j ω)
    rw [this]
    ring
  simp_rw [hφ]
  have hS_int : Integrable (fun ω => ∑ j ∈ univ.erase i, β (A.θ j ω)) ℙ :=
    integrable_finset_sum _ (fun j _ => hβ_int j)
  rw [integral_add (integrable_const _) (hS_int.const_mul _),
      integral_const_mul, integral_const, probReal_univ, one_smul]
  rw [A.expected_sum_erase β hβ_meas i hβ_int]
  unfold meanPurchase
  ring

/-- Against opponents using strategy `β`, linear scarcity gives bidder `i` quadratic net cost
`C(b) = α·b² + K·b`, where `K = K_linear β`. -/
theorem allPurchaseNetCost_eq
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (hβ_int : ∀ j, Integrable (fun ω => β (A.θ j ω)) ℙ)
    (i : Fin n) (b : ℝ) :
    A.allPurchaseNetCost A.spec β i b =
      A.α_coeff * b ^ 2 + A.K_linear β * b := by
  unfold Auction.allPurchaseNetCost
  rw [A.expected_scarcity_linear β hβ_meas hβ_int i b]
  unfold K_linear meanPurchase
  have hn : 1 ≤ n := by
    have := Nat.AtLeastTwo.prop (n := n)
    omega
  rw [Nat.cast_sub hn]
  ring

/-! ## Interim bidder problem -/

omit [NeZero n] [n.AtLeastTwo] [A.HasIdenticalTypes] in
/-- Bidder `i`'s interim payment for purchasing `b` against opponents using `β` equals gross
expenditure minus expected edition value: `p·b − b·𝔼[φ(b + Σ_{j≠i} β(θⱼ))]`. -/
theorem p_strat_eq_allPurchaseNetCost
    (β : ℝ → ℝ)
    (hβ_int : ∀ j, Integrable (fun ω => β (A.θ j ω)) ℙ)
    (i : Fin n) (b : ℝ) :
    A.p_strat β i b = A.allPurchaseNetCost A.spec β i b := by
  simp only [Auction.p_strat, Auction.allPurchaseNetCost]
  simp_rw [A.spec.payment_eq, Finset.sum_update_univ, Function.update_self]
  simp_rw [show ∀ ω, (A.spec.price -
      A.spec.φ
        (b + ∑ j ∈ univ.erase i, β (A.θ j ω))) * b =
    A.spec.price * b +
      (-b) * A.spec.φ
        (b + ∑ j ∈ univ.erase i, β (A.θ j ω)) from fun _ => by ring]
  have hφ_int : Integrable (fun ω => A.spec.φ
      (b + ∑ j ∈ univ.erase i, β (A.θ j ω))) ℙ := by
    simp_rw [show ∀ ω, A.spec.φ
        (b + ∑ j ∈ univ.erase i, β (A.θ j ω)) =
      A.φ_bar - A.α_coeff * (b + ∑ j ∈ univ.erase i, β (A.θ j ω)) from
      fun ω => congr_fun A.scarcity_is_linear _]
    exact (integrable_const _).sub
      ((integrable_const_add_iff.mpr
        (integrable_finset_sum _ fun j _ => hβ_int j)).const_mul _)
  rw [integral_add (integrable_const _) (hφ_int.const_mul _),
    integral_const, probReal_univ, one_smul, integral_const_mul]
  ring

/-- Under linear scarcity, bidder `i`'s interim payment against opponents using `β` is
`p_strat(β, i, b) = α·b² + K·b`, where `K = K_linear β`. -/
theorem p_strat_eq_quadratic
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (hβ_int : ∀ j, Integrable (fun ω => β (A.θ j ω)) ℙ)
    (i : Fin n) (b : ℝ) :
    A.p_strat β i b = A.α_coeff * b ^ 2 + A.K_linear β * b := by
  rw [A.p_strat_eq_allPurchaseNetCost β hβ_int i b]
  exact A.allPurchaseNetCost_eq β hβ_meas hβ_int i b

/-- Bidder `i`'s interim problem in a linear scarcity auction when opponents use strategy `β`. At
purchase `b`, the winning probability is `A.q_strat β i b` and net cost is `α·b² + (K_linear β)·b`,
so type `v` receives expected utility equal to `v` times that winning probability minus this cost.
The bidder's prescribed strategy is also `β`. -/
noncomputable def toQuadraticCostProblem
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (hβ_int : ∀ j, Integrable (fun ω => β (A.θ j ω)) ℙ)
    (i : Fin n) : QuadraticCostProblem where
  toBidderProblem := A.toBidderProblem A.spec.isUnitIntervalAllocation β i
  α_coeff := A.α_coeff
  K_param := A.K_linear β
  α_pos := A.α_pos
  cost_eq b := A.p_strat_eq_quadratic β hβ_meas hβ_int i b

end LinearScarcityAuction

end

end MathEconLib
