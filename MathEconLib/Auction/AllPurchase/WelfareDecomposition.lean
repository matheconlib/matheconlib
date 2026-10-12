module

public import MathEconLib.Auction.AllPurchase.LinearScarcity
public import MathEconLib.Auction.AllPurchase.RevenueDecomposition
public import Mathlib.Probability.Moments.Variance

/-!
# Welfare decomposition for the all-purchase auction

Under linear scarcity `φ(B) = φ̄ − α·B`, edition welfare at total quantity `B` is
`W^{ed}(B) = (φ̄ − c)·B − α·B²`, where `φbar` is the scarcity-value intercept, `c` is unit
production cost, and `α` is the dilution coefficient. The quantity and surplus benchmarks are
defined for arbitrary real parameters. When `α > 0`, they give the optimizer and maximum over all
real quantities; the optimizer is nonnegative exactly when `φbar ≥ c`.

The algebraic helper splits a supplied welfare gap at a supplied intermediate quantity. The
auction-level decomposition instead uses the auction's editions-only Cournot quantity and actual
expected edition welfare. A separate best-response certificate verifies that the Cournot profile
is feasible when `p ≤ φ̄`. No equilibrium assumption on bundled purchases is needed for the
decomposition itself.

For square-integrable aggregate purchases, the difference between welfare at the mean and
expected welfare is exactly the nonnegative penalty `α · Var(B)`. The Cournot gap is nonnegative.
The contest gap is nonnegative when editions-only purchases already exceed the efficient quantity
and the contest weakly raises mean purchases; it can be negative without these conditions. All
welfare quantities here concern editions, excluding the contest prize's value.

## Main definitions

* `editionWelfare`: edition welfare net of production cost.
* `firstBestQuantity` and `firstBestEditionSurplus`: quantity and surplus benchmarks.
* `cournotLoss` and `contestLoss`: welfare gaps at supplied quantity and welfare benchmarks.
* `bundledEditionWelfareMoments`: the welfare expression in two supplied moments.
* `LinearScarcityAuction.bundledEditionWelfare`: the auction's edition-welfare moment expression.
* `LinearScarcityAuction.cournotPurchaseLinear`: symmetric editions-only purchases per bidder.

## Main statements

* `editionWelfare_firstBestQuantity`: welfare at the quantity benchmark equals the surplus
  benchmark when `α ≠ 0`.
* `editionWelfare_le_firstBest`: the surplus benchmark bounds welfare at every real quantity when
  `α > 0`.
* `AllPurchase.welfare_decomposition`: the algebraic welfare-gap helper, retained for reuse.
* `LinearScarcityAuction.welfare_decomposition`: the decomposition of actual expected edition
  welfare using the auction's Cournot benchmark.
* `LinearScarcityAuction.cournotPurchaseLinear_best_response`: feasibility and optimality against
  nonnegative unilateral deviations in the editions-only game.
* `LinearScarcityAuction.editionWelfare_mean_sub_bundled_eq_variance`: the variance penalty for
  actual square-integrable purchases.
* `LinearScarcityAuction.contestLoss_nonneg_of_mean_ge`: a sufficient quantity condition for a
  nonnegative contest welfare gap.
* `LinearScarcityAuction.bundledEditionWelfare_eq`: the auction's moment expression equals
  `𝔼[B·φ(B)] − c·𝔼[B]` under integrability assumptions.

## Tags

all-purchase auction, linear scarcity, welfare, cournot competition, variance
-/

namespace MathEconLib

@[expose] public section

namespace AllPurchase

variable (φbar c α : ℝ)

/-- Edition welfare at total quantity `B` under linear scarcity, net of unit production cost `c`:
`W^{ed}(B) = (φ̄ − c)·B − α·B²`. Here `φbar` is the scarcity-value intercept and `α` is the
dilution coefficient; all four arguments may be arbitrary real numbers. -/
noncomputable def editionWelfare (B : ℝ) : ℝ := (φbar - c) * B - α * B ^ 2

/-- The quantity benchmark `B* = (φ̄ − c)/(2α)`, defined for arbitrary real parameters. For
`α > 0`, it maximizes edition welfare over all real quantities and is nonnegative exactly when
`φbar ≥ c`. -/
noncomputable def firstBestQuantity : ℝ := (φbar - c) / (2 * α)

/-- The surplus benchmark `W* = (φ̄ − c)²/(4α)`, defined for arbitrary real parameters. For
`α > 0`, it is the maximum edition welfare over all real quantities. -/
noncomputable def firstBestEditionSurplus : ℝ := (φbar - c) ^ 2 / (4 * α)

/-- If `α ≠ 0`, edition welfare at the quantity benchmark equals the surplus benchmark. The maximum
interpretation additionally requires `α > 0`. -/
theorem editionWelfare_firstBestQuantity (hα : α ≠ 0) :
    editionWelfare φbar c α (firstBestQuantity φbar c α)
      = firstBestEditionSurplus φbar c α := by
  unfold editionWelfare firstBestQuantity firstBestEditionSurplus
  field_simp
  ring

/-- For positive dilution `α`, the surplus benchmark bounds edition welfare at every real quantity
`B`. -/
theorem editionWelfare_le_firstBest (hα : 0 < α) (B : ℝ) :
    editionWelfare φbar c α B ≤ firstBestEditionSurplus φbar c α := by
  have key : firstBestEditionSurplus φbar c α - editionWelfare φbar c α B
      = (φbar - c - 2 * α * B) ^ 2 / (4 * α) := by
    unfold firstBestEditionSurplus editionWelfare
    field_simp
    ring
  have hnn : 0 ≤ firstBestEditionSurplus φbar c α - editionWelfare φbar c α B := by
    rw [key]
    positivity
  linarith

/-- The unconstrained first-best quantity is feasible for nonnegative purchases when the
scarcity intercept covers unit production cost. -/
theorem firstBestQuantity_nonneg (hα : 0 < α) (hc : c ≤ φbar) :
    0 ≤ firstBestQuantity φbar c α := by
  unfold firstBestQuantity
  exact div_nonneg (sub_nonneg.mpr hc) (by positivity)

/-- Above the efficient quantity, additional purchases weakly reduce edition welfare. -/
theorem editionWelfare_le_of_firstBest_le (hα : 0 < α) {B₁ B₂ : ℝ}
    (hfirst : firstBestQuantity φbar c α ≤ B₁) (hB : B₁ ≤ B₂) :
    editionWelfare φbar c α B₂ ≤ editionWelfare φbar c α B₁ := by
  have hfirst' : φbar - c ≤ B₁ * (2 * α) :=
    (div_le_iff₀ (by positivity : 0 < 2 * α)).mp hfirst
  have hdiff : 0 ≤ α * (B₂ - B₁) := mul_nonneg hα.le (sub_nonneg.mpr hB)
  have hfactor : 0 ≤ (B₂ - B₁) * (α * (B₂ + B₁) - (φbar - c)) :=
    mul_nonneg (sub_nonneg.mpr hB) (by nlinarith)
  unfold editionWelfare
  nlinarith only [hfactor]

/-- The welfare gap `L_Cournot = W* − W^B`, with `W^B` evaluated at the supplied quantity `B_ed`.
It represents Cournot deadweight loss for nonnegative purchases when `B_ed` is the editions-only
Cournot quantity, `α > 0`, and `φbar ≥ c`; the definition itself imposes none of these conditions.
-/
noncomputable def cournotLoss (B_ed : ℝ) : ℝ :=
  firstBestEditionSurplus φbar c α - editionWelfare φbar c α B_ed

/-- Positive dilution makes the gap from the unconstrained welfare maximum nonnegative at every
benchmark quantity. Feasibility of the benchmark is a separate economic condition. -/
theorem cournotLoss_nonneg (hα : 0 < α) (B_ed : ℝ) :
    0 ≤ cournotLoss φbar c α B_ed :=
  sub_nonneg.mpr (editionWelfare_le_firstBest φbar c α hα B_ed)

/-- The welfare gap `L_Contest = W^B − WC`, with `W^B` evaluated at the supplied quantity `B_ed`.
It represents the contest-induced welfare loss when `B_ed` is the editions-only Cournot quantity
and `WC` is bundled edition welfare. These interpretations and nonnegativity are not assumed. -/
noncomputable def contestLoss (B_ed WC : ℝ) : ℝ :=
  editionWelfare φbar c α B_ed - WC

/-- **Welfare decomposition:** for any supplied quantity `B_ed` and welfare value `WC`,
`W* − WC = L_Cournot + L_Contest`. This identity imposes no equilibrium conditions on the
benchmarks and does not assert that either gap is nonnegative. -/
theorem welfare_decomposition (B_ed WC : ℝ) :
    firstBestEditionSurplus φbar c α - WC
      = cournotLoss φbar c α B_ed + contestLoss φbar c α B_ed WC := by
  unfold cournotLoss contestLoss
  ring

/-- The moment expression `W^C = (φ̄ − c)·EB − α·EB2` for supplied real numbers `EB` and `EB2`.
When these are the first two moments of a square-integrable total quantity, the expression is
expected edition welfare. -/
noncomputable def bundledEditionWelfareMoments (EB EB2 : ℝ) : ℝ :=
  (φbar - c) * EB - α * EB2

/-- For arbitrary supplied values `EB` and `EB2`, the welfare difference equals `α · (EB2 − EB²)`.
If these are the first two moments of a square-integrable quantity and `α ≥ 0`, the right side is
the nonnegative variance penalty from evaluating welfare at the mean. -/
theorem editionWelfare_mean_sub_bundled (EB EB2 : ℝ) :
    editionWelfare φbar c α EB - bundledEditionWelfareMoments φbar c α EB EB2
      = α * (EB2 - EB ^ 2) := by
  unfold editionWelfare bundledEditionWelfareMoments
  ring

end AllPurchase

/-! ## Identifying `W^C` with the auction's edition welfare -/

open MeasureTheory ProbabilityTheory Set Finset

namespace LinearScarcityAuction

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} [NeZero n] [n.AtLeastTwo]
variable (A : LinearScarcityAuction Ω n) [A.HasIdenticalTypes]

/-- Expected squared aggregate quantity `𝔼[B²]` when every bidder uses strategy `β`, with
`B = A.toAuction.aggregateBid β`. -/
noncomputable def expectedAggregateBidSq (β : ℝ → ℝ) : ℝ :=
  𝔼[fun ω => (A.toAuction.aggregateBid β ω) ^ 2]

/-- The bundled edition-welfare moment expression `W^C = (φ̄ − c)·𝔼[B] − α·𝔼[B²]`, where `B` is
aggregate quantity under the common strategy `β`, `c` is unit production cost, and `φ̄` and `α` are
the auction's scarcity-value intercept and dilution coefficient. It equals expected edition value
net of production cost when `B` and `B²` are integrable. -/
noncomputable def bundledEditionWelfare (β : ℝ → ℝ) (c : ℝ) : ℝ :=
  (A.φ_bar - c) * A.toAuction.expectedAggregateBid β
    - A.α_coeff * A.expectedAggregateBidSq β

omit [n.AtLeastTwo] [NeZero n] [A.HasIdenticalTypes] in
/-- Under linear scarcity, expected edition value satisfies `𝔼[B·φ(B)] = φ̄·𝔼[B] − α·𝔼[B²]` when
aggregate quantity `B` under strategy `β` and its square are integrable. -/
theorem expectedEditionValue_linear (β : ℝ → ℝ)
    (hB_int : Integrable (A.toAuction.aggregateBid β) ℙ)
    (hB2_int : Integrable (fun ω => (A.toAuction.aggregateBid β ω) ^ 2) ℙ) :
    A.toAuction.expectedEditionValue A.spec β
      = A.φ_bar * A.toAuction.expectedAggregateBid β
        - A.α_coeff * A.expectedAggregateBidSq β := by
  unfold Auction.expectedEditionValue Auction.expectedAggregateBid
    expectedAggregateBidSq
  have hpt : ∀ ω, A.toAuction.aggregateBid β ω *
      A.spec.φ (A.toAuction.aggregateBid β ω)
      = A.φ_bar * A.toAuction.aggregateBid β ω
        - A.α_coeff * (A.toAuction.aggregateBid β ω) ^ 2 := by
    intro ω
    show A.toAuction.aggregateBid β ω * A.spec.φ _ = _
    rw [congr_fun A.scarcity_is_linear (A.toAuction.aggregateBid β ω)]
    ring
  simp_rw [hpt]
  rw [integral_sub (hB_int.const_mul _) (hB2_int.const_mul _),
      integral_const_mul, integral_const_mul]

omit [n.AtLeastTwo] [NeZero n] [A.HasIdenticalTypes] in
/-- When aggregate quantity under strategy `β` and its square are integrable, bundled edition
welfare equals expected edition value less expected production cost, `𝔼[B·φ(B)] − c·𝔼[B]`. -/
theorem bundledEditionWelfare_eq (β : ℝ → ℝ) (c : ℝ)
    (hB_int : Integrable (A.toAuction.aggregateBid β) ℙ)
    (hB2_int : Integrable (fun ω => (A.toAuction.aggregateBid β ω) ^ 2) ℙ) :
    A.bundledEditionWelfare β c
      = A.toAuction.expectedEditionValue A.spec β
        - c * A.toAuction.expectedAggregateBid β := by
  unfold bundledEditionWelfare
  rw [A.expectedEditionValue_linear β hB_int hB2_int]
  ring

end LinearScarcityAuction

/-! ## Feasible Cournot benchmark and expected-welfare decomposition -/

namespace LinearScarcityAuction

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} (A : LinearScarcityAuction Ω n)

/-- The symmetric per-bidder editions-only Cournot candidate. It is a feasible purchase when
the posted price does not exceed the scarcity intercept. -/
noncomputable def cournotPurchaseLinear : ℝ :=
  (A.φ_bar - A.spec.price) / (A.α_coeff * ((n : ℝ) + 1))

/-- At a price below the scarcity intercept, the symmetric Cournot purchase is nonnegative. -/
theorem cournotPurchaseLinear_nonneg (hp : A.spec.price ≤ A.φ_bar) :
    0 ≤ A.cournotPurchaseLinear := by
  unfold cournotPurchaseLinear
  exact div_nonneg (sub_nonneg.mpr hp)
    (mul_nonneg A.α_pos.le (by positivity))

/-- Total purchases at the symmetric Cournot profile equal the previously defined quantity. -/
theorem cournotQuantityLinear_eq_total :
    A.cournotQuantityLinear = (n : ℝ) * A.cournotPurchaseLinear := by
  unfold cournotQuantityLinear cournotPurchaseLinear
  ring

/-- The symmetric editions-only Cournot profile is feasible and admits no profitable
nonnegative unilateral deviation. Each buyer receives `x · (φ(total) − p)`; the contest prize
is absent. The deviation inequality follows by completing the square, rather than merely
checking a first-order condition. -/
theorem cournotPurchaseLinear_best_response [NeZero n] (hp : A.spec.price ≤ A.φ_bar) :
    0 ≤ A.cournotPurchaseLinear ∧
      ∀ x : ℝ, 0 ≤ x →
        x * (A.spec.φ (x + ((n : ℝ) - 1) * A.cournotPurchaseLinear) - A.spec.price) ≤
          A.cournotPurchaseLinear *
            (A.spec.φ ((n : ℝ) * A.cournotPurchaseLinear) - A.spec.price) := by
  refine ⟨A.cournotPurchaseLinear_nonneg hp, ?_⟩
  intro x _hx
  have hden : A.α_coeff * ((n : ℝ) + 1) ≠ 0 := by
    exact ne_of_gt (mul_pos A.α_pos (by positivity))
  have hstationary :
      A.cournotPurchaseLinear * (A.α_coeff * ((n : ℝ) + 1)) =
        A.φ_bar - A.spec.price := by
    exact div_mul_cancel₀ _ hden
  simp_rw [congr_fun A.scarcity_is_linear]
  rw [show A.φ_bar = A.spec.price +
    A.cournotPurchaseLinear * (A.α_coeff * ((n : ℝ) + 1)) by linarith]
  have hsq := mul_nonneg A.α_pos.le (sq_nonneg (x - A.cournotPurchaseLinear))
  nlinarith only [hsq]

/-- Square-integrable aggregate purchases make bundled edition welfare the expectation of
realized edition value net of production cost. This is edition welfare; it excludes the prize's
value. -/
theorem bundledEditionWelfare_eq_integral (β : ℝ → ℝ) (c : ℝ)
    (hB : MemLp (A.toAuction.aggregateBid β) 2 ℙ) :
    A.bundledEditionWelfare β c =
      𝔼[fun ω => A.toAuction.aggregateBid β ω *
        A.spec.φ (A.toAuction.aggregateBid β ω) - c * A.toAuction.aggregateBid β ω] := by
  have hB_int := hB.integrable (by norm_num)
  have hB2_int := hB.integrable_sq
  have hedition_int : Integrable
      (fun ω => A.toAuction.aggregateBid β ω * A.spec.φ (A.toAuction.aggregateBid β ω)) ℙ := by
    have heq : (fun ω => A.toAuction.aggregateBid β ω *
        A.spec.φ (A.toAuction.aggregateBid β ω)) =
        (fun ω => A.φ_bar * A.toAuction.aggregateBid β ω -
          A.α_coeff * (A.toAuction.aggregateBid β ω) ^ 2) := by
      funext ω
      rw [congr_fun A.scarcity_is_linear]
      ring
    rw [heq]
    exact (hB_int.const_mul _).sub (hB2_int.const_mul _)
  rw [integral_sub hedition_int (hB_int.const_mul _), integral_const_mul]
  exact A.bundledEditionWelfare_eq β c hB_int hB2_int

/-- The auction-level edition-welfare decomposition: the gap between the first-best surplus and
actual expected edition welfare is the Cournot gap plus the contest gap, evaluated at this
auction's editions-only Cournot quantity and bundled welfare.

The equality holds for every square-integrable strategy, including equilibrium strategies. The
Cournot benchmark is feasible and a best response when `price ≤ φ_bar`, as proved by
`cournotPurchaseLinear_best_response`; the first-best quantity is feasible when `c ≤ φ_bar`.
The signs of the two gaps are separate conclusions, not hypotheses hidden in the identity. -/
theorem welfare_decomposition (β : ℝ → ℝ) (c : ℝ)
    (hB : MemLp (A.toAuction.aggregateBid β) 2 ℙ) :
    AllPurchase.firstBestEditionSurplus A.φ_bar c A.α_coeff -
        𝔼[fun ω => A.toAuction.aggregateBid β ω *
          A.spec.φ (A.toAuction.aggregateBid β ω) - c * A.toAuction.aggregateBid β ω] =
      AllPurchase.cournotLoss A.φ_bar c A.α_coeff A.cournotQuantityLinear +
        AllPurchase.contestLoss A.φ_bar c A.α_coeff A.cournotQuantityLinear
          (A.bundledEditionWelfare β c) := by
  rw [← A.bundledEditionWelfare_eq_integral β c hB]
  exact AllPurchase.welfare_decomposition A.φ_bar c A.α_coeff
    A.cournotQuantityLinear (A.bundledEditionWelfare β c)

/-- For an actual square-integrable aggregate quantity, the moment correction is precisely the
nonnegative variance penalty. No independence or identical-distribution assumptions are needed. -/
theorem editionWelfare_mean_sub_bundled_eq_variance (β : ℝ → ℝ) (c : ℝ)
    (hB : MemLp (A.toAuction.aggregateBid β) 2 ℙ) :
    AllPurchase.editionWelfare A.φ_bar c A.α_coeff (A.toAuction.expectedAggregateBid β) -
        A.bundledEditionWelfare β c =
      A.α_coeff * variance (A.toAuction.aggregateBid β) ℙ := by
  rw [variance_eq_sub hB]
  unfold AllPurchase.editionWelfare bundledEditionWelfare expectedAggregateBidSq
    Auction.expectedAggregateBid
  simp only [Pi.pow_apply]
  ring

/-- Expected edition welfare does not exceed edition welfare evaluated at mean purchases. -/
theorem bundledEditionWelfare_le_mean (β : ℝ → ℝ) (c : ℝ)
    (hB : MemLp (A.toAuction.aggregateBid β) 2 ℙ) :
    A.bundledEditionWelfare β c ≤
      AllPurchase.editionWelfare A.φ_bar c A.α_coeff (A.toAuction.expectedAggregateBid β) := by
  have h := A.editionWelfare_mean_sub_bundled_eq_variance β c hB
  have hnonneg := mul_nonneg A.α_pos.le (variance_nonneg (A.toAuction.aggregateBid β) ℙ)
  linarith

/-- Actual expected edition welfare is bounded by the first-best surplus. -/
theorem bundledEditionWelfare_le_firstBest (β : ℝ → ℝ) (c : ℝ)
    (hB : MemLp (A.toAuction.aggregateBid β) 2 ℙ) :
    A.bundledEditionWelfare β c ≤ AllPurchase.firstBestEditionSurplus A.φ_bar c A.α_coeff :=
  (A.bundledEditionWelfare_le_mean β c hB).trans
    (AllPurchase.editionWelfare_le_firstBest A.φ_bar c A.α_coeff A.α_pos _)

/-- The auction's Cournot welfare gap is nonnegative. Feasibility of its first-best and Cournot
quantities additionally requires `c ≤ φ_bar` and `price ≤ φ_bar`, respectively. -/
theorem cournotLoss_nonneg (c : ℝ) :
    0 ≤ AllPurchase.cournotLoss A.φ_bar c A.α_coeff A.cournotQuantityLinear :=
  AllPurchase.cournotLoss_nonneg A.φ_bar c A.α_coeff A.α_pos A.cournotQuantityLinear

/-- If editions-only purchases already exceed the efficient quantity, a contest that weakly
raises mean purchases weakly lowers edition welfare. Square integrability accounts for the
additional variance penalty. Contest welfare need not fall when these quantity conditions fail. -/
theorem contestLoss_nonneg_of_mean_ge (β : ℝ → ℝ) (c : ℝ)
    (hB : MemLp (A.toAuction.aggregateBid β) 2 ℙ)
    (hfirst : AllPurchase.firstBestQuantity A.φ_bar c A.α_coeff ≤ A.cournotQuantityLinear)
    (hmean : A.cournotQuantityLinear ≤ A.toAuction.expectedAggregateBid β) :
    0 ≤ AllPurchase.contestLoss A.φ_bar c A.α_coeff A.cournotQuantityLinear
      (A.bundledEditionWelfare β c) := by
  exact sub_nonneg.mpr ((A.bundledEditionWelfare_le_mean β c hB).trans
    (AllPurchase.editionWelfare_le_of_firstBest_le A.φ_bar c A.α_coeff A.α_pos hfirst hmean))

end LinearScarcityAuction

end

end MathEconLib
