module

public import MathEconLib.Auction.AllPurchase.Basic
public import MathEconLib.Auction.IdenticalTypes
public import MathEconLib.Mechanism.AllPurchase
public import MathEconLib.ForMathlib.FinsetUpdate

/-!
# Linear Scarcity for All-Purchase Auctions (Chapter 6)
-/

namespace MathEconLib

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

variable (A : Auction Ω n) [A.rules.IsAllPurchase]

noncomputable def allPurchaseNetCost
    (β : ℝ → ℝ) (i : Fin n) (b : ℝ) : ℝ :=
  A.rules.allPurchase_p_price * b - b *
    𝔼[fun ω => A.rules.allPurchaseφ <| b + ∑ j ∈ univ.erase i, β (A.θ j ω)]

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
variable (A : LinearScarcityAuction Ω n) [A.HasIdenticalTypes]

instance : Mechanism.IsAllPurchase A.rules := A.isAllPurchase

/-- Mean equilibrium purchase per bidder: `μ = 𝔼[β(V₀)]`. -/
noncomputable def meanPurchase (β : ℝ → ℝ) : ℝ :=
  𝔼[fun ω => β (A.θ 0 ω)]

/-- The effective marginal net cost `K = p − φ̄ + α(n−1)μ`,
where `μ = 𝔼[β(V₀)]` is computed from the equilibrium strategy. -/
noncomputable def K_linear (β : ℝ → ℝ) : ℝ :=
  A.rules.allPurchase_p_price -
    A.φ_bar + A.α_coeff * (↑n - 1) * A.meanPurchase β

/-! ## Expectation computation -/

omit [n.AtLeastTwo] in
/-- Under linear scarcity, `E[φ(b + B₋ᵢ)] = φ̄ − α·(b + (n−1)·μ)`,
where `μ = 𝔼[β(V₀)]` is computed from the equilibrium strategy. -/
theorem expected_scarcity_linear
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (hβ_int : ∀ j, Integrable (fun ω => β (A.θ j ω)) ℙ)
    (i : Fin n) (b : ℝ) :
    𝔼[fun ω => A.rules.allPurchaseφ <|
      b + ∑ j ∈ univ.erase i, β (A.θ j ω)] =
      A.φ_bar - A.α_coeff * (b + (↑(n - 1) : ℝ) * A.meanPurchase β) := by
  have hφ : ∀ ω, (A.rules.allPurchaseφ <|
      b + ∑ j ∈ univ.erase i, β (A.θ j ω)) =
      (A.φ_bar - A.α_coeff * b) +
        (-A.α_coeff) * (∑ j ∈ univ.erase i, β (A.θ j ω)) := by
    intro ω
    show A.rules.allPurchaseφ _ = _
    have := congr_fun A.scarcity_is_linear <|
      b + ∑ j ∈ univ.erase i, β (A.θ j ω)
    unfold Mechanism.allPurchaseφ; rw [this]; ring
  simp_rw [hφ]
  have hS_int : Integrable (fun ω => ∑ j ∈ univ.erase i, β (A.θ j ω)) ℙ :=
    integrable_finset_sum _ (fun j _ => hβ_int j)
  rw [integral_add (integrable_const _) (hS_int.const_mul _),
      integral_const_mul, integral_const, probReal_univ, one_smul]
  rw [A.expected_sum_erase β hβ_meas i hβ_int]
  unfold meanPurchase; ring

/-- Under linear scarcity, the all-purchase net cost equals the quadratic form:
`C(b) = α·b² + K·b`. -/
theorem allPurchaseNetCost_eq
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (hβ_int : ∀ j, Integrable (fun ω => β (A.θ j ω)) ℙ)
    (i : Fin n) (b : ℝ) :
    A.allPurchaseNetCost β i b =
      A.α_coeff * b ^ 2 + A.K_linear β * b := by
  unfold Auction.allPurchaseNetCost
  rw [A.expected_scarcity_linear β hβ_meas hβ_int i b]
  unfold K_linear meanPurchase
  have hn : 1 ≤ n := by have := Nat.AtLeastTwo.prop (n := n); omega
  rw [Nat.cast_sub hn]; ring

/-! ## Quantity-space QuadraticCostProblem -/

omit [NeZero n] [n.AtLeastTwo] [A.HasIdenticalTypes] in
/-- `p_strat` equals `allPurchaseNetCost` under linear scarcity:
`𝔼[tᵢ(b, β(θ₋ᵢ))] = p·b − b·𝔼[φ(b + Σ_{j≠i} β(θⱼ))]`. -/
theorem p_strat_eq_allPurchaseNetCost
    (β : ℝ → ℝ)
    (hβ_int : ∀ j, Integrable (fun ω => β (A.θ j ω)) ℙ)
    (i : Fin n) (b : ℝ) :
    A.p_strat β i b = A.allPurchaseNetCost β i b := by
  simp only [Auction.p_strat, Auction.allPurchaseNetCost]
  simp_rw [Mechanism.IsAllPurchase.t_eq, Finset.sum_update_univ,
           Function.update_self]
  simp_rw [show ∀ ω, (Mechanism.IsAllPurchase.p_price (M := A.rules) -
      A.rules.allPurchaseφ
        (b + ∑ j ∈ univ.erase i, β (A.θ j ω))) * b =
    Mechanism.IsAllPurchase.p_price (M := A.rules) * b +
      (-b) * A.rules.allPurchaseφ
        (b + ∑ j ∈ univ.erase i, β (A.θ j ω)) from fun _ => by ring]
  have hφ_int : Integrable (fun ω => A.rules.allPurchaseφ
      (b + ∑ j ∈ univ.erase i, β (A.θ j ω))) ℙ := by
    simp_rw [show ∀ ω, A.rules.allPurchaseφ
        (b + ∑ j ∈ univ.erase i, β (A.θ j ω)) =
      A.φ_bar - A.α_coeff * (b + ∑ j ∈ univ.erase i, β (A.θ j ω)) from
      fun ω => congr_fun A.scarcity_is_linear _]
    exact (integrable_const _).sub
      ((integrable_const_add_iff.mpr
        (integrable_finset_sum _ fun j _ => hβ_int j)).const_mul _)
  rw [integral_add (integrable_const _) (hφ_int.const_mul _),
      integral_const, probReal_univ, one_smul, integral_const_mul]; ring

/-- Under linear scarcity, the interim payment equals the quadratic form:
`p_strat(β, i, b) = α·b² + K·b`. -/
theorem p_strat_eq_quadratic
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (hβ_int : ∀ j, Integrable (fun ω => β (A.θ j ω)) ℙ)
    (i : Fin n) (b : ℝ) :
    A.p_strat β i b = A.α_coeff * b ^ 2 + A.K_linear β * b := by
  rw [A.p_strat_eq_allPurchaseNetCost β hβ_int i b]
  exact A.allPurchaseNetCost_eq β hβ_meas hβ_int i b

/-- Construct the `QuadraticCostProblem` for bidder `i` in the
linear scarcity auction with equilibrium strategy `β`. Uses
`toBidderProblem` (cost = `p_strat`), with `cost_eq` proved via
`p_strat_eq_quadratic`. -/
noncomputable def toQuadraticCostProblem
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (hβ_int : ∀ j, Integrable (fun ω => β (A.θ j ω)) ℙ)
    (i : Fin n) : QuadraticCostProblem where
  toBidderProblem := A.toBidderProblem β i
  α_coeff := A.α_coeff
  K_param := A.K_linear β
  α_pos := A.α_pos
  cost_eq b := A.p_strat_eq_quadratic β hβ_meas hβ_int i b

end LinearScarcityAuction

end

end MathEconLib
