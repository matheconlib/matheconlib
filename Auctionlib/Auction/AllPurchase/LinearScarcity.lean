module

public import Auctionlib.Auction.AllPurchase.Basic
public import Auctionlib.Auction.IdenticalTypes
public import Auctionlib.Mechanism.AllPurchase

/-!
# Linear Scarcity for All-Purchase Auctions (Chapter 6)

## Structures

### BidderProblem level
- `QuadraticCostProblem` — cost function is `α · b² + K · b`
- `LinearCostProblem` — cost function is `p_net · b` (constant scarcity)
- `InteriorRegimeProblem` — extends `QuadraticCostProblem` with `K < 0`

### BidderProblem typeclasses (Prop)
- `IsBoundaryRegime R` — lowest type has zero utility

### Auction level
- `LinearScarcityAuction` — all-purchase auction with `φ(B) = φ̄ − αB`

## Expectation computation

Under linear scarcity and identical types, the expected net cost
`C(b) = p·b − b·E[φ(b + B₋ᵢ)]` reduces to the quadratic form
`C(b) = α·b² + K·b`, where `K = p − φ̄ + α(n−1)μ`.

## Main results

- `expected_scarcity_linear`: `E[φ(b + B₋ᵢ)] = φ̄ − α·(b + (n−1)·μ)`
- `allPurchaseNetCost_eq`: `C(b) = α·b² + K·b`
- `toQuadraticCostProblem`: quantity-space QuadraticCostProblem bridge
-/

@[expose] public section

/-! ## BidderProblem-level structures -/

/-- A bidder problem where cost is quadratic: `cost(b) = α · b² + K · b`.
This arises from linear scarcity `φ(B) = φ̄ − αB` in the all-purchase auction. -/
structure QuadraticCostProblem extends BidderProblem where
  /-- dilution intensity (slope of scarcity function) -/
  α_coeff : ℝ
  /-- effective marginal net cost: `K = p − φ̄ + α(n−1)μ` -/
  K_param : ℝ
  /-- dilution intensity is positive -/
  α_pos : 0 < α_coeff
  /-- the cost function equals the quadratic form -/
  cost_eq : ∀ b, toBidderProblem.cost b = α_coeff * b ^ 2 + K_param * b

/-- A bidder problem where cost is linear: `cost(b) = p_net · b`.
This arises from constant scarcity `φ(B) = u₀` in the all-purchase auction. -/
structure LinearCostProblem extends BidderProblem where
  /-- net cost per unit: `p − u₀` -/
  p_net : ℝ
  /-- net cost per unit is positive (no-arbitrage) -/
  p_net_pos : 0 < p_net
  /-- the cost function equals the linear form -/
  cost_eq : ∀ b, toBidderProblem.cost b = p_net * b

namespace BidderProblem

/-- **Boundary regime**: the lowest type purchases zero, so `U(lowestType) = 0`.
Applies when `K ≥ 0`.

Unlike `InteriorRegimeProblem`, this is a Prop typeclass: the boundary
regime arises under both constant scarcity (`LinearCostProblem`, Prop 6.5) and
linear scarcity (`QuadraticCostProblem`, Prop 6.6), so bundling either would
exclude the other. -/
class IsBoundaryRegime (B : BidderProblem) : Prop where
  U_lowestType_zero : B.U B.lowestType = 0

end BidderProblem

/-- **Interior regime**: all types purchase a positive baseline quantity,
so `U(lowestType) = K²/(4α)`.  Applies when `K < 0`.
Extends `QuadraticCostProblem` so that `α_coeff`, `K_param`, `cost_eq` are
directly accessible. -/
structure InteriorRegimeProblem extends QuadraticCostProblem where
  K_neg : K_param < 0
  U_lowestType_eq : toBidderProblem.U toBidderProblem.lowestType = K_param ^ 2 / (4 * α_coeff)

/-! ## Auction-level definitions -/

open MeasureTheory ProbabilityTheory Set Finset

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} [NeZero n] [n.AtLeastTwo]

namespace Auction

variable (A : Auction Ω n) [Mechanism.IsAllPurchase A.rules]

/-- The all-purchase expected net expenditure for bid `b`:
`C(b) = p·b − b·E[φ(b + Σ_{j≠i} β(V_j))]`. -/
noncomputable def allPurchaseNetCost
    (β : ℝ → ℝ) (i : Fin n) (b : ℝ) : ℝ :=
  Mechanism.IsAllPurchase.p_price (M := A.rules) * b - b *
    𝔼[fun ω => Mechanism.IsAllPurchase.φ (M := A.rules) <|
      b + ∑ j ∈ univ.erase i, β (A.θ j ω)]

/-- Construct the quantity-space BidderProblem for bidder `i` in the
all-purchase auction with equilibrium strategy `β`.

- `strategy := β` (maps types to quantities)
- `cost := allPurchaseNetCost` (net expenditure, derived from `t_eq`)
- `winProb := q_strat β i` (winning probability, derived from `x_eq`) -/
noncomputable def toAllPurchaseBidderProblem [HasIdenticalTypes A]
    (β : ℝ → ℝ) (hβ : Measurable β) (i : Fin n) :
    BidderProblem where
  lowestType := A.lowestType
  highestType := A.highestType
  winProb := A.q_strat β i
  winProb_range := A.q_strat_range Mechanism.IsAllPurchase.hasValidAllocation hβ i
  cost := A.allPurchaseNetCost β i
  strategy := β

omit [n.AtLeastTwo] in
@[simp]
theorem toAllPurchaseBidderProblem_winProb [HasIdenticalTypes A]
    (β : ℝ → ℝ) (hβ : Measurable β) (i : Fin n) (b : ℝ) :
    (A.toAllPurchaseBidderProblem β hβ i).winProb b = A.q_strat β i b := rfl

omit [n.AtLeastTwo] in
@[simp]
theorem toAllPurchaseBidderProblem_cost [HasIdenticalTypes A]
    (β : ℝ → ℝ) (hβ : Measurable β) (i : Fin n) (b : ℝ) :
    (A.toAllPurchaseBidderProblem β hβ i).cost b = A.allPurchaseNetCost β i b := rfl

omit [n.AtLeastTwo] in
@[simp]
theorem toAllPurchaseBidderProblem_strategy [HasIdenticalTypes A]
    (β : ℝ → ℝ) (hβ : Measurable β) (i : Fin n) (v : ℝ) :
    (A.toAllPurchaseBidderProblem β hβ i).strategy v = β v := rfl

end Auction

/-! ## LinearScarcityAuction -/

/-- A linear scarcity auction: an all-purchase auction where the scarcity
function satisfies `φ(B) = φ̄ − α · B`. -/
structure LinearScarcityAuction (Ω : Type) [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] (n : ℕ)
    extends Auction Ω n where
  /-- the mechanism is all-purchase -/
  isAllPurchase : Mechanism.IsAllPurchase toAuction.rules
  /-- intercept of the scarcity function -/
  φ_bar : ℝ
  /-- slope of the scarcity function (dilution intensity) -/
  α_coeff : ℝ
  /-- dilution intensity is positive -/
  α_pos : 0 < α_coeff
  /-- intercept is positive -/
  φ_bar_pos : 0 < φ_bar
  /-- the scarcity function is linear -/
  scarcity_is_linear : isAllPurchase.φ = fun b => φ_bar - α_coeff * b

namespace LinearScarcityAuction

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} [NeZero n] [n.AtLeastTwo]
variable (A : LinearScarcityAuction Ω n)

instance : Mechanism.IsAllPurchase A.rules := A.isAllPurchase

/-- Shorthand for the all-purchase BidderProblem of bidder `i`. -/
noncomputable abbrev bidderProblem [Auction.HasIdenticalTypes A.toAuction]
    (β : ℝ → ℝ) (hβ : Measurable β) (i : Fin n) : BidderProblem :=
  A.toAuction.toAllPurchaseBidderProblem β hβ i

/-- Mean equilibrium purchase per bidder: `μ = 𝔼[β(V₀)]`. -/
noncomputable def meanPurchase [Auction.HasIdenticalTypes A.toAuction] (β : ℝ → ℝ) : ℝ :=
  𝔼[fun ω => β (A.θ 0 ω)]

/-- The effective marginal net cost `K = p − φ̄ + α(n−1)μ`,
where `μ = 𝔼[β(V₀)]` is computed from the equilibrium strategy. -/
noncomputable def K_linear [Auction.HasIdenticalTypes A.toAuction] (β : ℝ → ℝ) : ℝ :=
  Mechanism.IsAllPurchase.p_price (M := A.rules) -
    A.φ_bar + A.α_coeff * (↑n - 1) * A.meanPurchase β

/-! ## Expectation computation -/

omit [n.AtLeastTwo] in
/-- Under linear scarcity, `E[φ(b + B₋ᵢ)] = φ̄ − α·(b + (n−1)·μ)`,
where `μ = 𝔼[β(V₀)]` is computed from the equilibrium strategy. -/
theorem expected_scarcity_linear [Auction.HasIdenticalTypes A.toAuction]
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (hβ_int : ∀ j, Integrable (fun ω => β (A.θ j ω)) ℙ)
    (i : Fin n) (b : ℝ) :
    𝔼[fun ω => Mechanism.IsAllPurchase.φ (M := A.rules) <|
      b + ∑ j ∈ univ.erase i, β (A.θ j ω)] =
      A.φ_bar -
        A.α_coeff *
          (b + (↑(n - 1) : ℝ) * A.meanPurchase β) := by
  have hφ : ∀ ω, (Mechanism.IsAllPurchase.φ (M := A.rules) <|
      b + ∑ j ∈ univ.erase i, β (A.θ j ω)) =
      (A.φ_bar - A.α_coeff * b) +
        (-A.α_coeff) *
          (∑ j ∈ univ.erase i, β (A.θ j ω)) := by
    intro ω
    have := congr_fun A.scarcity_is_linear <|
      b + ∑ j ∈ univ.erase i, β (A.θ j ω)
    rw [this]; ring
  simp_rw [hφ]
  have hS_int : Integrable (fun ω => ∑ j ∈ univ.erase i, β (A.θ j ω)) ℙ :=
    integrable_finset_sum _ (fun j _ => hβ_int j)
  rw [integral_add (integrable_const _) (hS_int.const_mul _),
      integral_const_mul, integral_const, probReal_univ, one_smul]
  rw [A.toAuction.expected_sum_erase β hβ_meas i hβ_int]
  unfold meanPurchase; ring

/-- Under linear scarcity, the all-purchase net cost equals the quadratic form:
`C(b) = α·b² + K·b`. -/
theorem allPurchaseNetCost_eq [Auction.HasIdenticalTypes A.toAuction]
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (hβ_int : ∀ j, Integrable (fun ω => β (A.θ j ω)) ℙ)
    (i : Fin n) (b : ℝ) :
    A.toAuction.allPurchaseNetCost β i b =
      A.α_coeff * b ^ 2 + A.K_linear β * b := by
  unfold Auction.allPurchaseNetCost
  rw [A.expected_scarcity_linear β hβ_meas hβ_int i b]
  unfold K_linear meanPurchase
  have hn : 1 ≤ n := by have := Nat.AtLeastTwo.prop (n := n); omega
  rw [Nat.cast_sub hn]
  ring

/-! ## Quantity-space QuadraticCostProblem -/

/-- Construct the `QuadraticCostProblem` for bidder `i` in the
linear scarcity auction with equilibrium strategy `β`.

- `strategy := β` (maps types to quantities)
- `cost := allPurchaseNetCost` (net expenditure, with quadratic form `α·b² + K·b`)
- `winProb := q_strat β i` (winning probability, derived from `x_eq`) -/
noncomputable def toQuadraticCostProblem [Auction.HasIdenticalTypes A.toAuction]
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (hβ_int : ∀ j, Integrable (fun ω => β (A.θ j ω)) ℙ)
    (i : Fin n) : QuadraticCostProblem where
  lowestType := A.toAuction.lowestType
  highestType := A.toAuction.highestType
  winProb := A.toAuction.q_strat β i
  winProb_range := A.toAuction.q_strat_range Mechanism.IsAllPurchase.hasValidAllocation hβ_meas i
  cost := A.toAuction.allPurchaseNetCost β i
  strategy := β
  α_coeff := A.α_coeff
  K_param := A.K_linear β
  α_pos := A.α_pos
  cost_eq b := A.allPurchaseNetCost_eq β hβ_meas hβ_int i b

@[simp]
theorem toQuadraticCostProblem_toBidderProblem [Auction.HasIdenticalTypes A.toAuction]
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (hβ_int : ∀ j, Integrable (fun ω => β (A.θ j ω)) ℙ)
    (i : Fin n) :
    (A.toQuadraticCostProblem β hβ_meas hβ_int i).toBidderProblem =
      A.toAuction.toAllPurchaseBidderProblem β hβ_meas i := rfl

end LinearScarcityAuction

end
