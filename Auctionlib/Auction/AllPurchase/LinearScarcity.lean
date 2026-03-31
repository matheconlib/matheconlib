module

public import Auctionlib.Auction.AllPurchase

/-!
# Linear Scarcity for All-Purchase Auctions (Chapter 6)

## Typeclasses

### ReducedForm level
- `HasQuadraticCost R` — cost function is `α · b² + K · b`
- `HasLinearCost R` — cost function is `p_net · b` (constant scarcity)
- `IsBoundaryRegime R` — lowest type has zero utility
- `IsInteriorRegime R` — lowest type has positive baseline utility `K²/(4α)`

### Auction level
- `HasLinearScarcity A` — scarcity function is `φ(B) = φ̄ − αB`

## Expectation computation

Under linear scarcity and identical types, the expected net cost
`C(b) = p·b − b·E[φ(b + B₋ᵢ)]` reduces to the quadratic form
`C(b) = α·b² + K·b`, where `K = p − φ̄ + α(n−1)μ`.

## Main results

- `expected_scarcity_linear`: `E[φ(b + B₋ᵢ)] = φ̄ − α·(b + (n−1)·μ)`
- `allPurchaseNetCost_eq`: `C(b) = α·b² + K·b`
- `toAllPurchaseReducedForm`: quantity-space ReducedForm (winProb = `q_strat`, cost = C)
- `allPurchaseHasQuadraticCost`: `HasQuadraticCost` instance
-/

@[expose] public section

/-! ## ReducedForm-level typeclasses -/

namespace ReducedForm

/-- The cost function has quadratic form `cost(b) = α · b² + K · b`.
This arises from linear scarcity `φ(B) = φ̄ − αB` in the all-purchase auction. -/
class HasQuadraticCost (R : ReducedForm) where
  /-- dilution intensity (slope of scarcity function) -/
  α_coeff : ℝ
  /-- effective marginal net cost: `K = p − φ̄ + α(n−1)μ` -/
  K_param : ℝ
  /-- dilution intensity is positive -/
  α_pos : 0 < α_coeff
  /-- the cost function equals the quadratic form -/
  cost_eq : ∀ b, R.cost b = α_coeff * b ^ 2 + K_param * b

/-- The cost function has linear form `cost(b) = p_net · b`.
This arises from constant scarcity `φ(B) = u₀` in the all-purchase auction. -/
class HasLinearCost (R : ReducedForm) where
  /-- net cost per unit: `p − u₀` -/
  p_net : ℝ
  /-- net cost per unit is positive (no-arbitrage) -/
  p_net_pos : 0 < p_net
  /-- the cost function equals the linear form -/
  cost_eq : ∀ b, R.cost b = p_net * b

/-- **Boundary regime**: the lowest type purchases zero, so `U(lowestType) = 0`.
Applies when `K ≥ 0`. -/
class IsBoundaryRegime (R : ReducedForm) : Prop where
  U_lowestType_zero : R.U R.lowestType = 0

/-- **Interior regime**: all types purchase a positive baseline quantity,
so `U(lowestType) = K²/(4α)`.  Applies when `K < 0`.
Extends `HasQuadraticCost` so that `α_coeff`, `K_param`, `cost_eq` are
directly accessible. -/
class IsInteriorRegime (R : ReducedForm) extends HasQuadraticCost R where
  K_neg : K_param < 0
  U_lowestType_eq : R.U R.lowestType = K_param ^ 2 / (4 * α_coeff)

end ReducedForm

/-! ## Auction-level typeclass -/

open MeasureTheory ProbabilityTheory Set Finset

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} [NeZero n] [n.AtLeastTwo]

namespace Auction

variable (A : Auction Ω n)

/-- Linear scarcity: the edition value function satisfies `φ(B) = φ̄ − α · B`. -/
class HasLinearScarcity [inst : Mechanism.IsAllPurchase A.rules] where
  /-- intercept of the scarcity function -/
  φ_bar : ℝ
  /-- slope of the scarcity function (dilution intensity) -/
  α_coeff : ℝ
  /-- dilution intensity is positive -/
  α_pos : 0 < α_coeff
  /-- intercept is positive -/
  φ_bar_pos : 0 < φ_bar
  /-- the scarcity function is linear -/
  scarcity_is_linear : inst.φ = fun b => φ_bar - α_coeff * b

variable [Mechanism.IsAllPurchase A.rules] [HasLinearScarcity A]

/-- Mean equilibrium purchase per bidder: `μ = 𝔼[β(V₀)]`. -/
noncomputable def meanPurchase [HasIdenticalTypes A] (β : ℝ → ℝ) : ℝ :=
  𝔼[fun ω => β (A.θ 0 ω)]

/-- The effective marginal net cost `K = p − φ̄ + α(n−1)μ`,
where `μ = 𝔼[β(V₀)]` is computed from the equilibrium strategy. -/
noncomputable def K_linear [HasIdenticalTypes A] (β : ℝ → ℝ) : ℝ :=
  Mechanism.IsAllPurchase.p_price (M := A.rules) -
    HasLinearScarcity.φ_bar A +
    HasLinearScarcity.α_coeff A * (↑n - 1) * A.meanPurchase β

/-! ## Expectation computation -/

/-- The all-purchase expected net expenditure for bid `b`:
`C(b) = p·b − b·E[φ(b + Σ_{j≠i} β(V_j))]`. -/
noncomputable def allPurchaseNetCost
    (β : ℝ → ℝ) (i : Fin n) (b : ℝ) : ℝ :=
  Mechanism.IsAllPurchase.p_price (M := A.rules) * b - b *
    𝔼[fun ω => Mechanism.IsAllPurchase.φ (M := A.rules) <|
      b + ∑ j ∈ univ.erase i, β (A.θ j ω)]

omit [n.AtLeastTwo] in
/-- Under linear scarcity, `E[φ(b + B₋ᵢ)] = φ̄ − α·(b + (n−1)·μ)`,
where `μ = 𝔼[β(V₀)]` is computed from the equilibrium strategy. -/
theorem expected_scarcity_linear [HasIdenticalTypes A]
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (hβ_int : ∀ j, Integrable (fun ω => β (A.θ j ω)) ℙ)
    (i : Fin n) (b : ℝ) :
    𝔼[fun ω => Mechanism.IsAllPurchase.φ (M := A.rules) <|
      b + ∑ j ∈ univ.erase i, β (A.θ j ω)] =
      HasLinearScarcity.φ_bar A -
        HasLinearScarcity.α_coeff A *
          (b + (↑(n - 1) : ℝ) * A.meanPurchase β) := by
  have hφ : ∀ ω, (Mechanism.IsAllPurchase.φ (M := A.rules) <|
      b + ∑ j ∈ univ.erase i, β (A.θ j ω)) =
      (HasLinearScarcity.φ_bar A - HasLinearScarcity.α_coeff A * b) +
        (-HasLinearScarcity.α_coeff A) *
          (∑ j ∈ univ.erase i, β (A.θ j ω)) := by
    intro ω
    have := congr_fun (HasLinearScarcity.scarcity_is_linear (A := A)) <|
      b + ∑ j ∈ univ.erase i, β (A.θ j ω)
    rw [this]; ring
  simp_rw [hφ]
  have hS_int : Integrable (fun ω => ∑ j ∈ univ.erase i, β (A.θ j ω)) ℙ :=
    integrable_finset_sum _ (fun j _ => hβ_int j)
  rw [integral_add (integrable_const _) (hS_int.const_mul _),
      integral_const_mul, integral_const, probReal_univ, one_smul]
  rw [A.expected_sum_erase β hβ_meas i hβ_int]
  unfold meanPurchase; ring

/-- Under linear scarcity, the all-purchase net cost equals the quadratic form:
`C(b) = α·b² + K·b`. -/
theorem allPurchaseNetCost_eq [HasIdenticalTypes A]
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (hβ_int : ∀ j, Integrable (fun ω => β (A.θ j ω)) ℙ)
    (i : Fin n) (b : ℝ) :
    A.allPurchaseNetCost β i b =
      HasLinearScarcity.α_coeff A * b ^ 2 + A.K_linear β * b := by
  unfold allPurchaseNetCost
  rw [A.expected_scarcity_linear β hβ_meas hβ_int i b]
  unfold K_linear meanPurchase
  have hn : 1 ≤ n := by have := Nat.AtLeastTwo.prop (n := n); omega
  rw [Nat.cast_sub hn]
  ring

/-! ## Quantity-space ReducedForm -/

/-- Construct the quantity-space ReducedForm for bidder `i` in the
all-purchase auction with equilibrium strategy `β`.

- `strategy := β` (maps types to quantities)
- `cost := allPurchaseNetCost` (net expenditure, derived from `t_eq`)
- `winProb := q_strat β i` (winning probability, derived from `x_eq`) -/
noncomputable def toAllPurchaseReducedForm [HasIdenticalTypes A]
    (β : ℝ → ℝ) (hβ : Measurable β) (i : Fin n) :
    ReducedForm where
  lowestType := A.lowestType
  highestType := A.highestType
  winProb := A.q_strat β i
  winProb_range := A.q_strat_range Mechanism.IsAllPurchase.hasValidAllocation hβ i
  cost := A.allPurchaseNetCost β i
  strategy := β

omit [n.AtLeastTwo] [HasLinearScarcity A] in
@[simp]
theorem toAllPurchaseReducedForm_winProb [HasIdenticalTypes A]
    (β : ℝ → ℝ) (hβ : Measurable β) (i : Fin n) (b : ℝ) :
    (A.toAllPurchaseReducedForm β hβ i).winProb b = A.q_strat β i b := rfl

omit [n.AtLeastTwo] [HasLinearScarcity A] in
@[simp]
theorem toAllPurchaseReducedForm_cost [HasIdenticalTypes A]
    (β : ℝ → ℝ) (hβ : Measurable β) (i : Fin n) (b : ℝ) :
    (A.toAllPurchaseReducedForm β hβ i).cost b = A.allPurchaseNetCost β i b := rfl

omit [n.AtLeastTwo] [HasLinearScarcity A] in
@[simp]
theorem toAllPurchaseReducedForm_strategy [HasIdenticalTypes A]
    (β : ℝ → ℝ) (hβ : Measurable β) (i : Fin n) (v : ℝ) :
    (A.toAllPurchaseReducedForm β hβ i).strategy v = β v := rfl

/-- Under linear scarcity, the all-purchase ReducedForm has quadratic cost. -/
noncomputable def allPurchaseHasQuadraticCost [HasIdenticalTypes A]
    (β : ℝ → ℝ) (hβ_meas : Measurable β)
    (hβ_int : ∀ j, Integrable (fun ω => β (A.θ j ω)) ℙ)
    (i : Fin n) :
    ReducedForm.HasQuadraticCost (A.toAllPurchaseReducedForm β hβ_meas i) where
  α_coeff := HasLinearScarcity.α_coeff A
  K_param := A.K_linear β
  α_pos := HasLinearScarcity.α_pos
  cost_eq b := A.allPurchaseNetCost_eq β hβ_meas hβ_int i b

end Auction

end
