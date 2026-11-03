/-
Copyright (c) 2026 Daniel Lyng, Ruiz Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng, Ruiz Chen
-/
module

public import MathEconLib.Auction.AllPurchase.LinearScarcity
public import MathEconLib.Auction.AllPurchase.RevenueDecomposition

/-!
# Welfare decomposition for the all-purchase auction

Under linear scarcity `φ(B) = φ̄ − α·B`, edition welfare at total quantity `B` is
`W^{ed}(B) = (φ̄ − c)·B − α·B²`, where `φbar` is the scarcity-value intercept, `c` is unit
production cost, and `α` is the dilution coefficient. The quantity and surplus benchmarks are
defined for arbitrary real parameters. When `α > 0`, they give the optimizer and maximum over all
real quantities; the optimizer is nonnegative exactly when `φbar ≥ c`.

The welfare decomposition splits the gap from the surplus benchmark at a supplied intermediate
quantity. The moment identity relates welfare at a supplied mean to a supplied second moment. When
these are moments of a square-integrable quantity and `α ≥ 0`, the difference is the nonnegative
variance penalty `α · Var(B)`. For a linear-scarcity auction, integrability of total quantity and
its square identifies the moment expression with expected edition value net of production cost.

## Main definitions

* `editionWelfare`: edition welfare net of production cost.
* `firstBestQuantity` and `firstBestEditionSurplus`: quantity and surplus benchmarks.
* `cournotLoss` and `contestLoss`: welfare gaps at supplied quantity and welfare benchmarks.
* `bundledEditionWelfareMoments`: the welfare expression in two supplied moments.
* `LinearScarcityAuction.bundledEditionWelfare`: the auction's edition-welfare moment expression.

## Main statements

* `editionWelfare_firstBestQuantity`: welfare at the quantity benchmark equals the surplus
  benchmark when `α ≠ 0`.
* `editionWelfare_le_firstBest`: the surplus benchmark bounds welfare at every real quantity when
  `α > 0`.
* `welfare_decomposition`: the algebraic decomposition into Cournot and contest welfare gaps.
* `editionWelfare_mean_sub_bundled`: the algebraic identity underlying the variance penalty.
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

/-- The welfare gap `L_Cournot = W* − W^B`, with `W^B` evaluated at the supplied quantity `B_ed`.
It represents Cournot deadweight loss for nonnegative purchases when `B_ed` is the editions-only
Cournot quantity, `α > 0`, and `φbar ≥ c`; the definition itself imposes none of these conditions.
-/
noncomputable def cournotLoss (B_ed : ℝ) : ℝ :=
  firstBestEditionSurplus φbar c α - editionWelfare φbar c α B_ed

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

end

end MathEconLib
