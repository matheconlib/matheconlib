module

public import Auctionlib.Auction.SymmetricIPV

/-!
# Revenue Equivalence Theorem

Under BIC, IR, and efficient allocation in a symmetric IPV auction,
the expected total revenue equals `𝔼[S₂]` (expected second-highest type).

More generally, two BIC + IR mechanisms with the same `q` yield the same
expected revenue, without any efficiency assumption.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} [n.AtLeastTwo]

namespace Auction

variable (A : Auction Ω n) [A.IsSymmetricIPV]

/-- Under BIC, efficient allocation, and IR, the per-type expected payment
is uniquely determined by the common CDF. -/
lemma payment_formula_efficient
    (hx : A.rules.HasValidAllocation) (eff : A.Efficient)
    (hbic : A.BIC) (ir : A.IndividuallyRational)
    (i : Fin n) {s : ℝ} (hs : s ∈ A.interval i) :
    A.p i s = s * A.commonCDF s ^ (n - 1) -
      ∫ ψ in A.lowestType..s, A.commonCDF ψ ^ (n - 1) := by
  have hpf := A.payment_formula hx hbic i hs
  simp [A.q_eq_pow eff, ir i] at hpf ⊢
  linarith

/-- **Revenue Equivalence Theorem.**

Two BIC, IR symmetric IPV auctions with the same `q`, same type bounds,
and identically distributed types yield the same expected total revenue. -/
theorem revenue_equivalence
    {Ω₂ : Type} [MeasureSpace Ω₂] [IsProbabilityMeasure (ℙ : Measure Ω₂)]
    (A₂ : Auction Ω₂ n) [A₂.IsSymmetricIPV]
    (hx₁ : A.rules.HasValidAllocation) (hx₂ : A₂.rules.HasValidAllocation)
    (hq : ∀ i, A.q i = A₂.q i)
    (hmin : A.lowestType = A₂.lowestType)
    (hmax : A.highestType = A₂.highestType)
    (ident : ∀ i, IdentDistrib (A.θ i) (A₂.θ i) ℙ ℙ)
    (hbic₁ : A.BIC) (hbic₂ : A₂.BIC)
    (ir₁ : A.IndividuallyRational) (ir₂ : A₂.IndividuallyRational)
    (p_meas : ∀ i, Measurable (A₂.p i))
    (hint₁ : ∀ i, Integrable (fun ω => A.p i (A.θ i ω)) ℙ)
    (hint₂ : ∀ i, Integrable (fun ω => A₂.p i (A₂.θ i ω)) ℙ) :
    A.expectedRevenue = A₂.expectedRevenue := by
  simp only [expectedRevenue]
  rw [integral_finset_sum _ fun i _ => hint₁ i,
      integral_finset_sum _ fun i _ => hint₂ i]
  congr 1; ext i
  have hθmin : A.θmin i = A₂.θmin i := by simp [hmin]
  have hθmax : A.θmax i = A₂.θmax i := by simp [hmax]
  -- Use the ReducedForm payment_unique via the bridge
  have h_td1 := A.hasTypeDeviationIC_of_bic hx₁ hbic₁ i
  have h_td2 := A₂.hasTypeDeviationIC_of_bic hx₂ hbic₂ i
  have hU : (A.toReducedForm hx₁ i).U (A.θmin i) =
            (A₂.toReducedForm hx₂ i).U (A₂.θmin i) := by
    simp only [toReducedForm_U, A.θmin_eq_lowestType, A₂.θmin_eq_lowestType,
      ir₁ i, ir₂ i]
  have heq (ω) : A.p i (A.θ i ω) = A₂.p i (A.θ i ω) :=
    (A.toReducedForm hx₁ i).payment_unique (A₂.toReducedForm hx₂ i)
      hθmin hθmax (hq i) hU (A.θ i ω) (HasBoundedTypes.θ_in i ω)
  calc ∫ ω, A.p i (A.θ i ω) ∂ℙ
      = ∫ ω, A₂.p i (A.θ i ω) ∂ℙ := integral_congr_ae (ae_of_all _ heq)
    _ = ∫ ω, A₂.p i (A₂.θ i ω) ∂ℙ :=
        ((ident i).comp (p_meas i)).integral_eq

/-- Under efficient allocation, BIC, and IR, the expected total revenue equals
`𝔼[S₂]`, the expected second-highest order statistic. -/
lemma total_revenue
    (hx : A.rules.HasValidAllocation) (eff : A.Efficient)
    (hbic : A.BIC) (ir : A.IndividuallyRational) :
    A.expectedRevenue = 𝔼[A.S₂] := by
  simp only [expectedRevenue]
  let φ : ℝ → ℝ :=
    fun s => s * A.commonCDF s ^ (n - 1) -
      ∫ ψ in A.lowestType..s, A.commonCDF ψ ^ (n - 1)
  have hrw (j ω) : A.p j (A.θ j ω) = φ (A.θ j ω) :=
    A.payment_formula_efficient hx eff hbic ir j (HasBoundedTypes.θ_in j ω)
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
  rw [integral_finset_sum Finset.univ fun i _ => by
    refine Integrable.mono'
      (integrable_const
        (max |A.lowestType| |A.highestType| + (A.highestType - A.lowestType)))
      ((hφ_meas.comp (A.θ_measurable i)).aestronglyMeasurable) ?_
    filter_upwards with ω
    have hs := HasBoundedTypes.θ_in (A := A) i ω
    simp only [A.θmin_eq_lowestType, A.θmax_eq_highestType] at hs
    obtain ⟨hlo, hhi⟩ := hs
    have hpow_nn t : 0 ≤ A.commonCDF t ^ (n - 1) :=
      pow_nonneg (A.commonCDF_nonneg t) _
    have hpow_le1 t : A.commonCDF t ^ (n - 1) ≤ 1 :=
      pow_le_one₀ (A.commonCDF_nonneg t) (A.commonCDF_le_one t)
    have hint_nn : 0 ≤ ∫ ψ in A.lowestType..A.θ i ω,
        A.commonCDF ψ ^ (n - 1) :=
      intervalIntegral.integral_nonneg hlo fun ψ _ => hpow_nn ψ
    have hpow_mono' : Monotone (fun ψ => A.commonCDF ψ ^ (n - 1)) :=
      fun a b hab => pow_le_pow_left₀ (A.commonCDF_nonneg a) (A.commonCDF_mono hab) _
    have hint_le :
        ∫ ψ in A.lowestType..A.θ i ω, A.commonCDF ψ ^ (n - 1) ≤
          A.highestType - A.lowestType := by
      calc ∫ ψ in A.lowestType..A.θ i ω, A.commonCDF ψ ^ (n - 1)
          _ ≤ ∫ _ in A.lowestType..A.θ i ω, (1 : ℝ) :=
            intervalIntegral.integral_mono_on hlo
              hpow_mono'.intervalIntegrable intervalIntegrable_const
              (fun ψ _ => hpow_le1 ψ)
          _ = A.θ i ω - A.lowestType := by simp
          _ ≤ A.highestType - A.lowestType := by linarith
    have hmul_le :
        |A.θ i ω * A.commonCDF (A.θ i ω) ^ (n - 1)| ≤ |A.θ i ω| := by
      rw [abs_mul, abs_of_nonneg (hpow_nn _)]
      exact mul_le_of_le_one_right (abs_nonneg _) (hpow_le1 _)
    have habs_le :
        |A.θ i ω| ≤ max |A.lowestType| |A.highestType| := by
      by_cases hnn : 0 ≤ A.θ i ω
      · calc |A.θ i ω| = A.θ i ω := abs_of_nonneg hnn
          _ ≤ A.highestType := hhi
          _ ≤ |A.highestType| := le_abs_self _
          _ ≤ max |A.lowestType| |A.highestType| := le_max_right _ _
      · push_neg at hnn
        calc |A.θ i ω| = -(A.θ i ω) := abs_of_neg hnn
          _ ≤ -(A.lowestType) := by linarith
          _ ≤ |-(A.lowestType)| := le_abs_self _
          _ = |A.lowestType| := abs_neg _
          _ ≤ max |A.lowestType| |A.highestType| := le_max_left _ _
    simp only [φ, Real.norm_eq_abs]
    rw [abs_le]
    exact ⟨by linarith [neg_abs_le (A.θ i ω * A.commonCDF (A.θ i ω) ^ (n - 1))],
           by linarith [le_abs_self (A.θ i ω * A.commonCDF (A.θ i ω) ^ (n - 1))]⟩]
  have hsym i : ∫ ω, φ (A.θ i ω) ∂ℙ = ∫ ω, φ (A.θ 0 ω) ∂ℙ := by
    rw [← integral_map (A.θ_measurable i).aemeasurable
          hφ_meas.aestronglyMeasurable,
        (HasIdenticalTypes.θ_identical i 0).map_eq,
        integral_map (A.θ_measurable 0).aemeasurable
          hφ_meas.aestronglyMeasurable]
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
    obtain ⟨ω, hω⟩ := (hbounded 0).exists; exact hω.1.trans hω.2
  exact (A.toOrderStatisticsSetup.expected_second_highest 0 _ _ hab
    hbounded A.commonCDF_lowestType A.commonCDF_highestType).symm

end Auction

end
