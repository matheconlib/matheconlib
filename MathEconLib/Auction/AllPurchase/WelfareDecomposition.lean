module

public import MathEconLib.Auction.AllPurchase.RevenueDecomposition
public import MathEconLib.Auction.AllPurchase.LinearScarcity

/-!
# Welfare decomposition for the all-purchase auction (§6.7.3)

Edition welfare under linear scarcity `φ(B) = φ̄ − α·B`, net of production cost
`c`, is `W^{ed}(B) = (φ̄ − c)·B − α·B²`.

* `firstBestEditionSurplus` — the planner optimum `W* = (φ̄ − c)²/(4α)`,
  attained at `B* = (φ̄ − c)/(2α)` and shown to be the maximum of `W^{ed}`.
* `welfare_decomposition` — **Proposition 6.13**: the total loss relative to
  the first best splits as `W* − W^C = L_Cournot + L_Contest`.
* `editionWelfare_mean_sub_bundled` — the variance penalty of Remark 18:
  evaluating welfare at the mean quantity overstates bundled welfare by
  `α · Var(B)`.
* `LinearScarcityAuction.bundledEditionWelfare_eq` — identifies the bundled
  edition welfare with the auction quantity `𝔼[B·φ(B)] − c·𝔼[B]`.
-/

@[expose] public section

namespace AllPurchase

variable (φbar c α : ℝ)

/-- Edition welfare at total quantity `B` under linear scarcity, net of cost:
`W^{ed}(B) = (φ̄ − c)·B − α·B²`. -/
noncomputable def editionWelfare (B : ℝ) : ℝ := (φbar - c) * B - α * B ^ 2

/-- The surplus-maximizing total quantity `B* = (φ̄ − c)/(2α)`. -/
noncomputable def firstBestQuantity : ℝ := (φbar - c) / (2 * α)

/-- First-best edition surplus `W* = (φ̄ − c)²/(4α)`. -/
noncomputable def firstBestEditionSurplus : ℝ := (φbar - c) ^ 2 / (4 * α)

/-- The first-best surplus is attained at the first-best quantity. -/
theorem editionWelfare_firstBestQuantity (hα : α ≠ 0) :
    editionWelfare φbar c α (firstBestQuantity φbar c α)
      = firstBestEditionSurplus φbar c α := by
  unfold editionWelfare firstBestQuantity firstBestEditionSurplus
  field_simp; ring

/-- The first-best surplus is the maximum of edition welfare (completing the
square). -/
theorem editionWelfare_le_firstBest (hα : 0 < α) (B : ℝ) :
    editionWelfare φbar c α B ≤ firstBestEditionSurplus φbar c α := by
  have key : firstBestEditionSurplus φbar c α - editionWelfare φbar c α B
      = (φbar - c - 2 * α * B) ^ 2 / (4 * α) := by
    unfold firstBestEditionSurplus editionWelfare
    field_simp; ring
  have hnn : 0 ≤ firstBestEditionSurplus φbar c α - editionWelfare φbar c α B := by
    rw [key]; positivity
  linarith

/-- The Cournot deadweight loss `L_Cournot = W* − W^B`, where `W^B` is the
edition welfare at the editions-only Cournot quantity `B_ed`. -/
noncomputable def cournotLoss (B_ed : ℝ) : ℝ :=
  firstBestEditionSurplus φbar c α - editionWelfare φbar c α B_ed

/-- The contest-induced loss `L_Contest = W^B − W^C`, where `WC` is the bundled
all-purchase edition welfare. -/
noncomputable def contestLoss (B_ed WC : ℝ) : ℝ :=
  editionWelfare φbar c α B_ed - WC

/-- **Proposition 6.13 (Welfare decomposition).**
The total welfare loss relative to the first best decomposes into a Cournot
deadweight loss and a contest-induced loss:
`W* − W^C = L_Cournot + L_Contest`. -/
theorem welfare_decomposition (B_ed WC : ℝ) :
    firstBestEditionSurplus φbar c α - WC
      = cournotLoss φbar c α B_ed + contestLoss φbar c α B_ed WC := by
  unfold cournotLoss contestLoss; ring

/-- Bundled edition welfare from the first two moments of total quantity:
`W^C = (φ̄ − c)·EB − α·EB2`, the expectation of `W^{ed}(B)`. -/
noncomputable def bundledEditionWelfareMoments (EB EB2 : ℝ) : ℝ :=
  (φbar - c) * EB - α * EB2

/-- **Remark 18 (variance penalty).** Evaluating edition welfare at the mean
quantity overstates bundled welfare by `α · Var(B)`:
`W^{ed}(EB) − W^C = α · (EB2 − EB²)`. -/
theorem editionWelfare_mean_sub_bundled (EB EB2 : ℝ) :
    editionWelfare φbar c α EB - bundledEditionWelfareMoments φbar c α EB EB2
      = α * (EB2 - EB ^ 2) := by
  unfold editionWelfare bundledEditionWelfareMoments; ring

end AllPurchase

/-! ## Identifying `W^C` with the auction's edition welfare -/

open MeasureTheory ProbabilityTheory Set Finset

namespace LinearScarcityAuction

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} [NeZero n] [n.AtLeastTwo]
variable (A : LinearScarcityAuction Ω n) [A.HasIdenticalTypes]

/-- Expected squared aggregate quantity `𝔼[B²]`. -/
noncomputable def expectedAggregateBidSq (β : ℝ → ℝ) : ℝ :=
  𝔼[fun ω => (A.toAuction.aggregateBid β ω) ^ 2]

/-- Bundled all-purchase edition welfare `W^C = (φ̄ − c)·𝔼[B] − α·𝔼[B²]`. -/
noncomputable def bundledEditionWelfare (β : ℝ → ℝ) (c : ℝ) : ℝ :=
  (A.φ_bar - c) * A.toAuction.expectedAggregateBid β
    - A.α_coeff * A.expectedAggregateBidSq β

omit [n.AtLeastTwo] [NeZero n] [A.HasIdenticalTypes] in
/-- Under linear scarcity, `𝔼[B·φ(B)] = φ̄·𝔼[B] − α·𝔼[B²]`. -/
theorem expectedEditionValue_linear (β : ℝ → ℝ)
    (hB_int : Integrable (A.toAuction.aggregateBid β) ℙ)
    (hB2_int : Integrable (fun ω => (A.toAuction.aggregateBid β ω) ^ 2) ℙ) :
    A.toAuction.expectedEditionValue β
      = A.φ_bar * A.toAuction.expectedAggregateBid β
        - A.α_coeff * A.expectedAggregateBidSq β := by
  unfold Auction.expectedEditionValue Auction.expectedAggregateBid
    expectedAggregateBidSq
  have hpt : ∀ ω, A.toAuction.aggregateBid β ω *
      A.rules.allPurchaseφ (A.toAuction.aggregateBid β ω)
      = A.φ_bar * A.toAuction.aggregateBid β ω
        - A.α_coeff * (A.toAuction.aggregateBid β ω) ^ 2 := by
    intro ω
    show A.toAuction.aggregateBid β ω * A.rules.allPurchaseφ _ = _
    unfold Mechanism.allPurchaseφ
    rw [congr_fun A.scarcity_is_linear (A.toAuction.aggregateBid β ω)]
    ring
  simp_rw [hpt]
  rw [integral_sub (hB_int.const_mul _) (hB2_int.const_mul _),
      integral_const_mul, integral_const_mul]

omit [n.AtLeastTwo] [NeZero n] [A.HasIdenticalTypes] in
/-- The bundled edition welfare equals the auction quantity
`𝔼[B·φ(B)] − c·𝔼[B]`. -/
theorem bundledEditionWelfare_eq (β : ℝ → ℝ) (c : ℝ)
    (hB_int : Integrable (A.toAuction.aggregateBid β) ℙ)
    (hB2_int : Integrable (fun ω => (A.toAuction.aggregateBid β ω) ^ 2) ℙ) :
    A.bundledEditionWelfare β c
      = A.toAuction.expectedEditionValue β
        - c * A.toAuction.expectedAggregateBid β := by
  unfold bundledEditionWelfare
  rw [A.expectedEditionValue_linear β hB_int hB2_int]
  ring

end LinearScarcityAuction

end
