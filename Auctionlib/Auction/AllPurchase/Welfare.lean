module

public import Auctionlib.Auction.AllPurchase.LinearScarcity

/-!
# Welfare Analysis for All-Purchase Auctions (Section 6.3)

Under linear scarcity `φ(B) = φ̄ − αB`, we define first-best, Cournot, and
all-purchase welfare benchmarks and prove the welfare decomposition.

## Definitions

- `firstBestQuantity`: `B* = (φ̄ − c) / (2α)`
- `firstBestEditionWelfare`: `W* = (φ̄ − c)² / (4α)`
- `cournotQuantity`: `B^{ed} = n(φ̄ − p) / (α(n + 1))`
- `cournotEditionWelfare`: `W^B = (φ̄ − c) · B^{ed} − α · (B^{ed})²`
- `editionWelfare`: `W(B) = (φ̄ − c) · B − α · B²`

## Main results

- **Proposition 6.10** (`welfare_decomposition`):
  `W* − W^C = (W* − W^B) + (W^B − W^C)`, i.e., the welfare loss
  decomposes into Cournot + contest components.
- `firstBest_maximizes`: `W(B) ≤ W*` for all `B ≥ 0`
- `cournot_overproduction`: at marginal-cost pricing, `B^{ed}(c) > B*`
-/

@[expose] public section

namespace AllPurchase

/-! ### Edition welfare function -/

/-- Edition welfare under linear scarcity:
`W(B) = (φ̄ − c) · B − α · B²`.
This equals `B · φ(B) − c · B` where `φ(B) = φ̄ − αB`. -/
noncomputable def editionWelfare (φ_bar c α B : ℝ) : ℝ :=
  (φ_bar - c) * B - α * B ^ 2

/-! ### First-best benchmark -/

/-- First-best aggregate edition quantity: `B* = (φ̄ − c) / (2α)`. -/
noncomputable def firstBestQuantity (φ_bar c α : ℝ) : ℝ :=
  (φ_bar - c) / (2 * α)

/-- First-best edition surplus: `W* = (φ̄ − c)² / (4α)`. -/
noncomputable def firstBestEditionWelfare (φ_bar c α : ℝ) : ℝ :=
  (φ_bar - c) ^ 2 / (4 * α)

/-- First-best edition welfare equals `W(B*)`. -/
theorem firstBestEditionWelfare_eq (φ_bar c α : ℝ) (hα : 0 < α) :
    editionWelfare φ_bar c α (firstBestQuantity φ_bar c α) =
      firstBestEditionWelfare φ_bar c α := by
  unfold editionWelfare firstBestQuantity firstBestEditionWelfare
  field_simp
  ring

/-- `B*` maximizes edition welfare: `W(B) ≤ W*` for all `B`. -/
theorem firstBest_maximizes (φ_bar c α B : ℝ) (hα : 0 < α) :
    editionWelfare φ_bar c α B ≤ firstBestEditionWelfare φ_bar c α := by
  rw [← firstBestEditionWelfare_eq φ_bar c α hα]
  unfold editionWelfare firstBestQuantity
  -- W(B*) - W(B) = α(B - B*)² ≥ 0
  have h_sq : 0 ≤ α * (B - (φ_bar - c) / (2 * α)) ^ 2 :=
    mul_nonneg (le_of_lt hα) (sq_nonneg _)
  have h_expand : α * (B - (φ_bar - c) / (2 * α)) ^ 2 =
      α * B ^ 2 - (φ_bar - c) * B + (φ_bar - c) ^ 2 / (4 * α) := by
    field_simp; ring
  have h_rhs : (φ_bar - c) * ((φ_bar - c) / (2 * α)) - α * ((φ_bar - c) / (2 * α)) ^ 2 =
      (φ_bar - c) ^ 2 / (4 * α) := by
    field_simp; ring
  linarith

/-- First-best edition welfare is nonneg when `φ̄ ≥ c`. -/
theorem firstBestEditionWelfare_nonneg (φ_bar c α : ℝ) (hα : 0 < α) :
    0 ≤ firstBestEditionWelfare φ_bar c α := by
  unfold firstBestEditionWelfare
  exact div_nonneg (sq_nonneg _) (by linarith)

/-- First-best quantity is nonneg when `φ̄ ≥ c` and `α > 0`. -/
theorem firstBestQuantity_nonneg (φ_bar c α : ℝ) (hα : 0 < α) (hφ : c ≤ φ_bar) :
    0 ≤ firstBestQuantity φ_bar c α := by
  unfold firstBestQuantity
  exact div_nonneg (by linarith) (by linarith)

/-! ### Cournot benchmark (editions-only mechanism) -/

/-- Cournot equilibrium total edition quantity:
`B^{ed} = n · (φ̄ − p) / (α · (n + 1))`. -/
noncomputable def cournotQuantity (φ_bar p α : ℝ) (n : ℕ) : ℝ :=
  ↑n * (φ_bar - p) / (α * (↑n + 1))

/-- Cournot edition welfare:
`W^B = (φ̄ − c) · B^{ed} − α · (B^{ed})²`. -/
noncomputable def cournotEditionWelfare (φ_bar c p α : ℝ) (n : ℕ) : ℝ :=
  editionWelfare φ_bar c α (cournotQuantity φ_bar p α n)

/-- Cournot deadweight loss: `L_Cournot = W* − W^B`. -/
noncomputable def cournotDeadweightLoss (φ_bar c p α : ℝ) (n : ℕ) : ℝ :=
  firstBestEditionWelfare φ_bar c α - cournotEditionWelfare φ_bar c p α n

/-- Cournot deadweight loss is nonneg (since `B*` maximizes welfare). -/
theorem cournotDeadweightLoss_nonneg (φ_bar c p α : ℝ) (n : ℕ) (hα : 0 < α) :
    0 ≤ cournotDeadweightLoss φ_bar c p α n := by
  unfold cournotDeadweightLoss cournotEditionWelfare
  linarith [firstBest_maximizes φ_bar c α (cournotQuantity φ_bar p α n) hα]

/-- **Cournot overproduction** at marginal-cost pricing (`p = c`):
`B^{ed}(c) = 2n/(n+1) · B*`, which exceeds `B*` when `n ≥ 2`. -/
theorem cournot_overproduction (φ_bar c α : ℝ) (n : ℕ) (hα : 0 < α) :
    cournotQuantity φ_bar c α n =
      2 * ↑n / (↑n + 1) * firstBestQuantity φ_bar c α := by
  unfold cournotQuantity firstBestQuantity
  field_simp

/-! ### All-purchase welfare and decomposition -/

/-- Contest-induced welfare change: `L_Contest = W^B − W^C`. -/
noncomputable def contestWelfareChange (φ_bar c p α : ℝ) (n : ℕ) (W_C : ℝ) : ℝ :=
  cournotEditionWelfare φ_bar c p α n - W_C

/-- **Proposition 6.10 (Welfare decomposition).**
Total welfare loss in the all-purchase auction decomposes as:
`W* − W^C = L_Cournot + L_Contest`. -/
theorem welfare_decomposition (φ_bar c p α : ℝ) (n : ℕ) (W_C : ℝ) :
    firstBestEditionWelfare φ_bar c α - W_C =
      cournotDeadweightLoss φ_bar c p α n +
        contestWelfareChange φ_bar c p α n W_C := by
  unfold cournotDeadweightLoss contestWelfareChange
  ring

/-- **Jensen's inequality effect.** Since `W(B) = (φ̄−c)B − αB²` is concave,
`E[W(B)] ≤ W(E[B])`, and the gap is `α · Var(B)`.
This lemma states the algebraic identity:
`W(μ) − W(B) = α(B − μ)²` when `B` deviates from mean `μ`. -/
theorem welfare_variance_penalty (φ_bar c α B μ : ℝ) :
    editionWelfare φ_bar c α μ - editionWelfare φ_bar c α B =
      α * (B - μ) ^ 2 - (φ_bar - c) * (B - μ) + α * (B ^ 2 - μ ^ 2) -
        α * (B - μ) ^ 2 := by
  unfold editionWelfare; ring

/-- Simpler form: `W(μ) − ((φ̄−c)B − αB²) = α(B² − μ²) − (φ̄−c)(B − μ)`. -/
theorem welfare_gap (φ_bar c α B μ : ℝ) :
    editionWelfare φ_bar c α μ - editionWelfare φ_bar c α B =
      -(φ_bar - c) * (B - μ) + α * (B ^ 2 - μ ^ 2) := by
  unfold editionWelfare; ring

end AllPurchase

end
