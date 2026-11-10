/-
Copyright (c) 2026 Jujian Zhang, Ruiz Chen, Scott Duke Kominers, Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Ruiz Chen, Scott Duke Kominers, Bo Cowgill
-/
module

public import MathEconLib.Auction.SymmetricIPV
public import MathEconLib.Auction.IdenticalTypes

/-!
# Revenue Equivalence Theorem

Under BIC, zero lowest-type utility, and strict-highest-bid allocation in a symmetric IPV auction,
the expected total revenue equals `𝔼[S₂]` (expected second-highest type).

More generally, two symmetric-IPV BIC mechanisms with zero lowest-type utility and the same `q`
yield the same expected revenue, without any efficiency assumption.

Revenue means realized receipts under the joint type law. Relating it to marginal interim payments
requires measurable payment rules and integrable realized payments; BIC and bounded allocations
alone do not supply these conditions.

## References

Vijay Krishna (2010), *Auction Theory*, 2nd ed., Academic Press:

* §3.1, Proposition 3.1, p. 28: revenue equivalence for symmetric increasing equilibria
  of standard auctions. `Auction.revenue_equivalence` expresses the sufficient common-allocation
  condition directly through the interim functions `q`; this formulation also allows
  common allocation rules that are not efficient.
* §2.4, equations (2.6)–(2.7), pp. 18–19: expected revenue as the expected second-highest
  value, corresponding to `Auction.total_revenue`.

See the [auction reference map](../../docs/AuctionReferences.md) for the scope of these matches.
-/

namespace MathEconLib

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open MathEconLib.Mechanism.Auctions

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} [n.AtLeastTwo]

namespace Auction

variable (A : Auction Ω n) [A.IsSymmetricIPV]

/-- Under BIC, strict-highest-bid allocation, and zero lowest-type utility, the per-type expected
payment is uniquely determined by the common CDF. -/
lemma payment_formula_strictHighestBid
    (hwinner : UsesStrictHighestBidAllocation A.rules (fun o i => o i))
    [IPV.BIC A] [A.HasZeroLowestTypeUtility]
    (i : Fin n) {s : ℝ} (hs : s ∈ A.interval i) :
    A.p i s = s * A.commonCDF s ^ (n - 1) -
      ∫ ψ in A.lowestType..s, A.commonCDF ψ ^ (n - 1) := by
  have hpf := A.payment_formula hwinner.isUnitIntervalAllocation i hs
  simp [A.q_eq_pow hwinner, HasZeroLowestTypeUtility.zeroLowestTypeUtility i] at hpf ⊢
  linarith

/-- **Revenue Equivalence Theorem.**

Two BIC symmetric IPV auctions with zero lowest-type utility, the same `q`, same type bounds, and
identically distributed types yield the same expected total revenue, provided the payment rules
are measurable and the realized truthful payments are integrable.

See Krishna (2010), §§2.4 and 3.1, and `docs/AuctionReferences.md`. -/
theorem revenue_equivalence
    {Ω₂ : Type} [MeasureSpace Ω₂] [IsProbabilityMeasure (ℙ : Measure Ω₂)]
    (A₂ : Auction Ω₂ n) [A₂.IsSymmetricIPV]
    (halloc : IsUnitIntervalAllocation A.rules (fun o i => o i))
    (halloc₂ : IsUnitIntervalAllocation A₂.rules (fun o i => o i))
    (hq : ∀ i, A.q i = A₂.q i)
    (hmin : A.lowestType = A₂.lowestType)
    (hmax : A.highestType = A₂.highestType)
    (ident : ∀ i, IdentDistrib (A.θ i) (A₂.θ i) ℙ ℙ)
    [IPV.BIC A] [IPV.BIC A₂]
    [A.HasZeroLowestTypeUtility] [A₂.HasZeroLowestTypeUtility]
    (p_meas : ∀ i, Measurable (A₂.p i))
    (payment_meas₁ : ∀ i, Measurable (A.rules.payment i))
    (payment_meas₂ : ∀ i, Measurable (A₂.rules.payment i))
    (hint₁ : ∀ i, Integrable (fun ω => A.rules.payment i (A.θ · ω)) ℙ)
    (hint₂ : ∀ i, Integrable (fun ω => A₂.rules.payment i (A₂.θ · ω)) ℙ) :
    A.expectedRevenue = A₂.expectedRevenue := by
  rw [A.expectedRevenue_eq_sum_integral_p payment_meas₁ hint₁,
    A₂.expectedRevenue_eq_sum_integral_p payment_meas₂ hint₂]
  congr 1
  ext i
  have hθmin : A.θmin i = A₂.θmin i := by simp [hmin]
  have hθmax : A.θmax i = A₂.θmax i := by simp [hmax]
  have hU : (A.toBidderProblem halloc id i).U (A.θmin i) =
            (A₂.toBidderProblem halloc₂ id i).U (A₂.θmin i) := by
    simp only [toBidderProblem_U, A.θmin_eq_lowestType, A₂.θmin_eq_lowestType,
      HasZeroLowestTypeUtility.zeroLowestTypeUtility i]
  have heq (ω) : A.p i (A.θ i ω) = A₂.p i (A.θ i ω) :=
    (A.toBidderProblem halloc id i).payment_unique (A₂.toBidderProblem halloc₂ id i)
      hθmin hθmax (hq i) hU (A.θ i ω) (HasBoundedTypes.θ_in i ω)
  calc ∫ ω, A.p i (A.θ i ω) ∂ℙ
      = ∫ ω, A₂.p i (A.θ i ω) ∂ℙ := integral_congr_ae (ae_of_all _ heq)
    _ = ∫ ω, A₂.p i (A₂.θ i ω) ∂ℙ :=
        ((ident i).comp (p_meas i)).integral_eq

/-- Under strict-highest-bid allocation, BIC, and zero lowest-type utility, expected realized
revenue equals `𝔼[S₂]`, provided payment rules are measurable and truthful payments are
integrable.

See Krishna (2010), §§2.4 and 3.1, and `docs/AuctionReferences.md`. -/
lemma total_revenue
    (hwinner : UsesStrictHighestBidAllocation A.rules (fun o i => o i))
    [IPV.BIC A] [A.HasZeroLowestTypeUtility]
    (payment_meas : ∀ i, Measurable (A.rules.payment i))
    (payment_integrable : ∀ i, Integrable (fun ω => A.rules.payment i (A.θ · ω)) ℙ) :
    A.expectedRevenue = 𝔼[A.S₂] := by
  rw [A.expectedRevenue_eq_sum_integral_p payment_meas payment_integrable]
  let φ : ℝ → ℝ :=
    fun s => s * A.commonCDF s ^ (n - 1) -
      ∫ ψ in A.lowestType..s, A.commonCDF ψ ^ (n - 1)
  have hrw (j ω) : A.p j (A.θ j ω) = φ (A.θ j ω) :=
    A.payment_formula_strictHighestBid hwinner j (HasBoundedTypes.θ_in j ω)
  simp_rw [hrw]
  have hφ_meas : Measurable φ := by
    refine Measurable.sub
      (measurable_id.mul (A.commonCDF_measurable.pow measurable_const)) <|
      Monotone.measurable fun s t hst => ?_
    have hpow_mono : Monotone (fun ψ => A.commonCDF ψ ^ (n - 1)) := fun a b hab =>
      pow_le_pow_left₀ (A.commonCDF_nonneg a) (A.commonCDF_mono hab) _
    have hii1 : IntervalIntegrable (fun ψ => A.commonCDF ψ ^ (n - 1))
        volume A.lowestType s := hpow_mono.intervalIntegrable (μ := volume)
    have hii2 : IntervalIntegrable (fun ψ => A.commonCDF ψ ^ (n - 1))
        volume s t := hpow_mono.intervalIntegrable (μ := volume)
    have hadd := (intervalIntegral.integral_add_adjacent_intervals hii1 hii2).symm
    linarith [intervalIntegral.integral_nonneg (μ := volume) hst
      (fun ψ _ => pow_nonneg (A.commonCDF_nonneg ψ) (n - 1))]
  have hsym i : ∫ ω, φ (A.θ i ω) ∂ℙ = ∫ ω, φ (A.θ 0 ω) ∂ℙ :=
    A.integral_comp_type_eq φ hφ_meas i 0
  simp_rw [hsym, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  change n * ∫ ω, φ (A.θ 0 ω) ∂ℙ = ∫ ω, A.S₂ ω ∂ℙ
  simp only [S₂]
  have hbounded i : ∀ᵐ ω ∂(ℙ : Measure Ω),
      A.toOrderStatisticsSetup.X i ω ∈
        Icc A.lowestType A.highestType := by
    filter_upwards with ω
    have h := HasBoundedTypes.θ_in (A := A) i ω
    simp only [A.θmin_eq_lowestType, A.θmax_eq_highestType] at h
    simpa [toOrderStatisticsSetup] using h
  have hab : A.lowestType ≤ A.highestType := by
    obtain ⟨ω, hω⟩ := (hbounded 0).exists
    exact hω.1.trans hω.2
  exact (A.toOrderStatisticsSetup.expected_second_highest 0 _ _ hab
    hbounded A.commonCDF_lowestType A.commonCDF_highestType).symm

end Auction

end

end MathEconLib
