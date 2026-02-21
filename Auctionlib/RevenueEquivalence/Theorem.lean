module

public import Mathlib.Probability.Notation
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.CDF
public import Auctionlib.Envelope.Theorem
public import Auctionlib.Statistics.OrderStatistics

/-!
# Revenue Equivalence Theorem

This file specializes `RevenueEquivalenceMathsCore` to the symmetric IPV auction model.

## Setup

`RevenueEquivalenceSetup` **extends** `EnvelopSetup Ω n`, adding:
- mutual independence of types (`θ_indep`),
- an identical-distribution condition (`θ_identical`), and
- an **efficient** allocation rule (the bidder with the strictly highest type wins).

The common CDF `ℰ.cdf s = ℙ[θ₀ ≤ s]` is a *derived definition* using bidder 0 as representative
(valid by `θ_identical`: all bidders share the same distribution).

All derived quantities (`q`, `p`, `U`, `interval`, `q_range`) and the `IncentiveCompatible`
predicate are inherited from `EnvelopSetup` via dot notation.

## Main results

`revenue_equivalence_theorem`: Under IC and IR at the bottom type:

1. The expected payment of any bidder with type `s` is uniquely determined:

   `p i s = s · cdf(s)^(n-1) - ∫ ψ in lowestType..s, cdf(ψ)^(n-1) dψ`

2. The total expected revenue equals the expected second-highest type:

   `∑ i, 𝔼[p i (θ i)] = 𝔼[S₂]`

-/

@[expose] public section

section revenueEquivalence

open MeasureTheory ProbabilityTheory

/--
Extension of `EnvelopSetup` for the Revenue Equivalence Theorem.

Adds to the general auction setup:
- mutual independence of types (`θ_indep`),
- identical marginal distributions (`θ_cdf`): any two bidders have the same CDF, and
- an efficient allocation rule (`efficient`).

The common CDF is the definition `ℰ.cdf s = ℙ[θ₀ ≤ s]` (bidder 0 as representative),
not a separate field.

All of `q`, `p`, `U`, `interval`, `IncentiveCompatible`, etc. are inherited.
-/
structure RevenueEquivalenceSetup
    (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (n : ℕ) [n.AtLeastTwo] extends EnvelopSetup Ω n where
  /-- Types are mutually independent -/
  θ_indep : iIndepFun θ ℙ
  /-- Types are identically distributed: any two bidders have the same law -/
  θ_identical i j : IdentDistrib (θ i) (θ j) ℙ ℙ
  /-- Each bidder's type lies in their type interval -/
  θ_in i (ω : Ω) : θ i ω ∈ toEnvelopSetup.interval i
  /-- Efficient allocation: bidder i wins iff they have the strictly highest type -/
  efficient i : x i = {f | ∀ j ≠ i, f j < f i}.indicator 1
  /-- The common type distribution has a density w.r.t. Lebesgue measure. -/
  θ_hasPDF : ∀ i, HasPDF (θ i) ℙ volume
  /-- The common type distribution is atomless: `ℙ[θ₀ = t] = 0` for all `t`.
  Required to equate `ℙ[θⱼ < s]` (from strict efficiency) with `cdf s = ℙ[θ₀ ≤ s]`. -/
  [θ_noAtoms : NoAtoms (Measure.map (θ 0) ℙ)]

  θmin_eq i : θmin i = θmin 0
  θmax_eq i : θmax i = θmax 0


namespace RevenueEquivalenceSetup

attribute [instance] θ_noAtoms

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} [n.AtLeastTwo]
variable (ℰ : RevenueEquivalenceSetup Ω n)

/--
The expected revenue is the expected sum of all payment
-/
noncomputable def expectedRevenue : ℝ := 𝔼[fun ω => ∑ i : Fin n, ℰ.p i (ℰ.θ i ω)]

noncomputable def lowestType : ℝ := ℰ.θmin 0
@[simp] lemma θmin_eq_lowestType (i) : ℰ.θmin i = ℰ.lowestType := by rw [ℰ.θmin_eq]; rfl

noncomputable def highestType : ℝ := ℰ.θmax 0
@[simp] lemma θmax_eq_highestType (i) : ℰ.θmax i = ℰ.highestType := by rw [ℰ.θmax_eq]; rfl

/-- The common CDF of the type distribution, defined via `ProbabilityTheory.cdf`.
`ℰ.cdf s = ProbabilityTheory.cdf (Measure.map (θ₀) ℙ) s`.
Since types are identically distributed (`θ_identical`), the CDF is the same for all bidders. -/
noncomputable abbrev commonCDF (s : ℝ) : ℝ := ProbabilityTheory.cdf (Measure.map (ℰ.θ 0) ℙ) s

instance isProbabilityMeasure_map_θ₀ : IsProbabilityMeasure (Measure.map (ℰ.θ 0) ℙ) :=
  Measure.isProbabilityMeasure_map (ℰ.θ_measurable 0).aemeasurable

/-- Bridge: unfold `ℰ.cdf s` to the raw measure expression `(ℙ (θ₀ ⁻¹' Iic s)).toReal`. -/
lemma commonCDF_eq (s : ℝ) : ℰ.commonCDF s = Measure.real ℙ (ℰ.θ 0 ⁻¹' Set.Iic s) := by
  simp [ProbabilityTheory.cdf_eq_real, Measure.real,
    Measure.map_apply (ℰ.θ_measurable 0) measurableSet_Iic]

lemma commonCDF_nonneg (s : ℝ) : 0 ≤ ℰ.commonCDF s := ProbabilityTheory.cdf_nonneg _ s

lemma commonCDF_le_one (s : ℝ) : ℰ.commonCDF s ≤ 1 := ProbabilityTheory.cdf_le_one _ s

lemma commonCDF_mono : Monotone ℰ.commonCDF := ProbabilityTheory.monotone_cdf _

lemma commonCDF_measurable : Measurable ℰ.commonCDF := ℰ.commonCDF_mono.measurable

/-- At the lowest type, `cdf = 0`: since `θ₀ ≥ lowestType` always and the distribution
is atomless, `ℙ[θ₀ ≤ lowestType] = ℙ[θ₀ = lowestType] = 0`. -/
@[simp] lemma commonCDF_lowestType : ℰ.commonCDF ℰ.lowestType = 0 := by
  rw [ℰ.commonCDF_eq, Measure.real]
  suffices h : ℙ (ℰ.θ 0 ⁻¹' Set.Iic ℰ.lowestType) = 0 by simp [h]
  have heq : ℰ.θ 0 ⁻¹' Set.Iic ℰ.lowestType = ℰ.θ 0 ⁻¹' {ℰ.lowestType} := by
    ext ω; simpa using by grind [ℰ.θmin_eq_lowestType, ℰ.θmax_eq_highestType, ℰ.θ_in 0 ω]
  rw [heq, ← Measure.map_apply (ℰ.θ_measurable 0) (measurableSet_singleton _), measure_singleton]

/-- At the highest type, `cdf = 1`: since `θ₀ ≤ highestType` always,
`ℙ[θ₀ ≤ highestType] = 1`. -/
@[simp] lemma commonCDF_highestType : ℰ.commonCDF ℰ.highestType = 1 := by
  rw [ℰ.commonCDF_eq]
  simp [show ℰ.θ 0 ⁻¹' Set.Iic ℰ.highestType = Set.univ by
    ext ω; simpa using by grind [ℰ.θmin_eq_lowestType, ℰ.θmax_eq_highestType, ℰ.θ_in 0 ω]]


/-- Bridge: construct an `OrderStatisticsSetup` from the revenue equivalence setup. -/
@[simps]
noncomputable def toOrderStatisticsSetup : OrderStatisticsSetup Ω n where
  X := ℰ.θ
  X_measurable := ℰ.θ_measurable
  X_indep := ℰ.θ_indep
  X_ident := ℰ.θ_identical
  X_hasPDF := ℰ.θ_hasPDF

/-- The second-highest order statistic: `S₂ ω = minᵢ maxₙₒₜ ⱼ₌ᵢ θⱼ(ω)`.
In a symmetric efficient auction, the seller's total revenue equals `𝔼[S₂]`. -/
noncomputable def S₂ (ω : Ω) : ℝ :=
  ℰ.toOrderStatisticsSetup.val ⟨n - 2, by have := Nat.AtLeastTwo.prop (n := n); omega⟩ ω

/-- In a symmetric efficient IPV auction, the probability that bidder `i`
wins when reporting type `s` equals `cdf(i, s)^(n-1)`. -/
lemma q_eq_pow (i : Fin n) (s : ℝ) : ℰ.q i s = ℰ.commonCDF s ^ (n - 1) := by
  simp only [EnvelopSetup.q, ℰ.efficient i, ne_eq]
  have hrw (ω) :
      {f : Fin n → ℝ | ∀ j ≠ i, f j < f i}.indicator 1 (Function.update (ℰ.θ · ω) i s) =
      (⋂ j ∈ Finset.univ.erase i, ℰ.θ j ⁻¹' Set.Iio s).indicator (1 : Ω → ℝ) ω := by
    simpa [Function.update, Set.indicator] using by grind
  simp_rw [hrw]
  have hmeas : MeasurableSet <| ⋂ j ∈ Finset.univ.erase i, ℰ.θ j ⁻¹' Set.Iio s :=
    MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ℰ.θ_measurable j measurableSet_Iio
  rw [integral_indicator_one hmeas, Measure.real, ℰ.θ_indep.meas_biInter fun j _ =>
        ⟨Set.Iio s, measurableSet_Iio, rfl⟩, ENNReal.toReal_prod]
  have hfactor j : (ℙ (ℰ.θ j ⁻¹' Set.Iio s)).toReal = ℰ.commonCDF s := by
    rw [ℰ.commonCDF_eq]
    congr 1
    calc ℙ (ℰ.θ j ⁻¹' Set.Iio s)
        _ = ℙ (ℰ.θ 0 ⁻¹' Set.Iio s) :=
            (ℰ.θ_identical j 0).measure_mem_eq measurableSet_Iio
        _ = (Measure.map (ℰ.θ 0) ℙ) (Set.Iio s) :=
            (Measure.map_apply (ℰ.θ_measurable 0) measurableSet_Iio).symm
        _ = (Measure.map (ℰ.θ 0) ℙ) (Set.Iic s) := measure_congr Iio_ae_eq_Iic
        _ = ℙ (ℰ.θ 0 ⁻¹' Set.Iic s) :=
            Measure.map_apply (ℰ.θ_measurable 0) measurableSet_Iic
  simp_rw [hfactor, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin]

/-- Individual rationality at the bottom: the lowest type gets zero utility -/
def IndividuallyRational : Prop := ∀ i, ℰ.U i ℰ.lowestType = 0

/-- Under IC and IR, the per-type expected payment is uniquely determined by `cdf i`.
This is the core pointwise fact used by both `payment_formula` and `total_payment`. -/
lemma payment_formula (ic : ℰ.IncentiveCompatible) (ir : ℰ.IndividuallyRational)
    (i : Fin n) {s : ℝ} (hs : s ∈ ℰ.interval i) :
    ℰ.p i s = s * ℰ.commonCDF s ^ (n - 1) - ∫ ψ in ℰ.lowestType..s, ℰ.commonCDF ψ ^ (n - 1) := by
  have hpU : ℰ.p i s = s * ℰ.q i s - ℰ.U i s := by
    linarith [show ℰ.U i s = s * ℰ.q i s - ℰ.p i s by rfl]
  simp [hpU, envelop_theorem ℰ.toEnvelopSetup ic |>.U_eq i s hs, ℰ.q_eq_pow, ir i]

lemma total_revenue (ic : ℰ.IncentiveCompatible) (ir : ℰ.IndividuallyRational) :
    ℰ.expectedRevenue = 𝔼[ℰ.S₂] := by
  simp only [RevenueEquivalenceSetup.expectedRevenue]
  let φ : ℝ → ℝ :=
    fun s => s * ℰ.commonCDF s ^ (n - 1) - ∫ ψ in ℰ.lowestType..s, ℰ.commonCDF ψ ^ (n - 1)
  have hrw (j ω) : ℰ.p j (ℰ.θ j ω) = φ (ℰ.θ j ω) := ℰ.payment_formula ic ir j (ℰ.θ_in j ω)
  simp_rw [hrw]
  have hφ_meas : Measurable φ := by
    refine Measurable.sub (measurable_id.mul (ℰ.commonCDF_measurable.pow measurable_const)) <|
      Monotone.measurable fun s t hst => ?_
    have hpow_mono : Monotone (fun ψ => ℰ.commonCDF ψ ^ (n - 1)) := fun a b hab =>
      pow_le_pow_left₀ (ℰ.commonCDF_nonneg a) (ℰ.commonCDF_mono hab) _
    have hii1 : IntervalIntegrable (fun ψ => ℰ.commonCDF ψ ^ (n - 1)) volume ℰ.lowestType s :=
      hpow_mono.intervalIntegrable (μ := volume)
    have hii2 : IntervalIntegrable (fun ψ => ℰ.commonCDF ψ ^ (n - 1)) volume s t :=
      hpow_mono.intervalIntegrable (μ := volume)
    have hadd := (intervalIntegral.integral_add_adjacent_intervals hii1 hii2).symm
    linarith [intervalIntegral.integral_nonneg (μ := volume) hst
      (fun ψ _ => pow_nonneg (ℰ.commonCDF_nonneg ψ) (n - 1))]
  rw [integral_finset_sum Finset.univ fun i _ => by
    refine Integrable.mono'
      (integrable_const (max |ℰ.lowestType| |ℰ.highestType| + (ℰ.highestType - ℰ.lowestType)))
      ((hφ_meas.comp (ℰ.θ_measurable i)).aestronglyMeasurable) ?_
    filter_upwards with ω
    have hs := ℰ.θ_in i ω
    simp only [EnvelopSetup.interval, ℰ.θmin_eq_lowestType, ℰ.θmax_eq_highestType] at hs
    obtain ⟨hlo, hhi⟩ := hs
    have hpow_nn t : 0 ≤ ℰ.commonCDF t ^ (n - 1) := pow_nonneg (ℰ.commonCDF_nonneg t) _
    have hpow_le1 t : ℰ.commonCDF t ^ (n - 1) ≤ 1 :=
      pow_le_one₀ (ℰ.commonCDF_nonneg t) (ℰ.commonCDF_le_one t)
    have hint_nn : 0 ≤ ∫ ψ in ℰ.lowestType..ℰ.θ i ω, ℰ.commonCDF ψ ^ (n - 1) :=
      intervalIntegral.integral_nonneg hlo fun ψ _ => hpow_nn ψ
    have hpow_mono' : Monotone (fun ψ => ℰ.commonCDF ψ ^ (n - 1)) := fun a b hab =>
      pow_le_pow_left₀ (ℰ.commonCDF_nonneg a) (ℰ.commonCDF_mono hab) _
    have hint_le := calc ∫ ψ in ℰ.lowestType..ℰ.θ i ω, ℰ.commonCDF ψ ^ (n - 1)
        _ ≤ ∫ ψ in ℰ.lowestType..ℰ.θ i ω, (1 : ℝ) :=
          intervalIntegral.integral_mono_on hlo
            hpow_mono'.intervalIntegrable intervalIntegrable_const fun ψ _ => hpow_le1 ψ
        _ = ℰ.θ i ω - ℰ.lowestType := by simp
        _ ≤ ℰ.highestType - ℰ.lowestType := by linarith
    have hmul_le : |ℰ.θ i ω * ℰ.commonCDF (ℰ.θ i ω) ^ (n - 1)| ≤ |ℰ.θ i ω| := by
      rw [abs_mul, abs_of_nonneg (hpow_nn _)]
      exact mul_le_of_le_one_right (abs_nonneg _) (hpow_le1 _)
    have habs_le : |ℰ.θ i ω| ≤ max |ℰ.lowestType| |ℰ.highestType| := by
      by_cases hnn : 0 ≤ ℰ.θ i ω
      · calc |ℰ.θ i ω| = ℰ.θ i ω := abs_of_nonneg hnn
          _ ≤ ℰ.highestType := hhi
          _ ≤ |ℰ.highestType| := le_abs_self _
          _ ≤ max |ℰ.lowestType| |ℰ.highestType| := le_max_right _ _
      · push_neg at hnn
        calc |ℰ.θ i ω| = -(ℰ.θ i ω) := abs_of_neg hnn
          _ ≤ -(ℰ.lowestType) := by linarith
          _ ≤ |-(ℰ.lowestType)| := le_abs_self _
          _ = |ℰ.lowestType| := abs_neg _
          _ ≤ max |ℰ.lowestType| |ℰ.highestType| := le_max_left _ _
    simpa [φ, Real.norm_eq_abs, abs_le] using
      ⟨by linarith [neg_abs_le (ℰ.θ i ω * ℰ.commonCDF (ℰ.θ i ω) ^ (n - 1))],
        by linarith [le_abs_self (ℰ.θ i ω * ℰ.commonCDF (ℰ.θ i ω) ^ (n - 1))]⟩]
  have hsym i : ∫ ω, φ (ℰ.θ i ω) ∂ℙ = ∫ ω, φ (ℰ.θ 0 ω) ∂ℙ := by
    rw [← integral_map (ℰ.θ_measurable i).aemeasurable hφ_meas.aestronglyMeasurable,
        (ℰ.θ_identical i 0).map_eq,
        integral_map (ℰ.θ_measurable 0).aemeasurable hφ_meas.aestronglyMeasurable]
  simp_rw [hsym, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change n * ∫ ω, φ (ℰ.θ 0 ω) ∂ℙ = ∫ ω, ℰ.S₂ ω ∂ℙ
  simp only [RevenueEquivalenceSetup.S₂]
  have hbounded i : ∀ᵐ ω ∂(ℙ : Measure Ω),
      ℰ.toOrderStatisticsSetup.X i ω ∈ Set.Icc ℰ.lowestType ℰ.highestType := by
    filter_upwards with ω
    simpa [EnvelopSetup.interval] using ℰ.θ_in i ω
  have hab : ℰ.lowestType ≤ ℰ.highestType := by
    obtain ⟨ω, hω⟩ := (hbounded 0).exists; exact hω.1.trans hω.2
  exact (ℰ.toOrderStatisticsSetup.expected_second_highest 0 _ _ hab hbounded
    ℰ.commonCDF_lowestType ℰ.commonCDF_highestType).symm

/-- **Revenue Equivalence (per-type payment).**
Any two efficient, IC, IR mechanisms whose type distributions are identically
distributed yield the same expected payment for any bidder at any type.

The payment formula `s · F(s)^{n-1} - ∫_{θ̲}^s F(ψ)^{n-1} dψ` depends only on the
common CDF `F` and the lowest type `θ̲`—not on the specific allocation or payment
rules of the mechanism, nor on the identity of the bidder.

The two mechanisms may live on different probability spaces `Ω₁`, `Ω₂`. -/
theorem payment_equivalence
    {Ω₁ : Type} [MeasureSpace Ω₁] [IsProbabilityMeasure (ℙ : Measure Ω₁)]
    {Ω₂ : Type} [MeasureSpace Ω₂] [IsProbabilityMeasure (ℙ : Measure Ω₂)]
    (ℰ₁ : RevenueEquivalenceSetup Ω₁ n) (ℰ₂ : RevenueEquivalenceSetup Ω₂ n)
    (hident : ∀ i j, IdentDistrib (ℰ₁.θ i) (ℰ₂.θ j) ℙ ℙ)
    (hmin : ℰ₁.lowestType = ℰ₂.lowestType)
    (ic₁ : ℰ₁.IncentiveCompatible) (ic₂ : ℰ₂.IncentiveCompatible)
    (ir₁ : ℰ₁.IndividuallyRational) (ir₂ : ℰ₂.IndividuallyRational)
    (i j : Fin n) {s : ℝ} (hs₁ : s ∈ ℰ₁.interval i) (hs₂ : s ∈ ℰ₂.interval j) :
    ℰ₁.p i s = ℰ₂.p j s := by
  rw [ℰ₁.payment_formula ic₁ ir₁ i hs₁, ℰ₂.payment_formula ic₂ ir₂ j hs₂]
  have hcdf : ∀ s, ℰ₁.commonCDF s = ℰ₂.commonCDF s := fun s => by
    simp only [commonCDF]; exact congr_arg (cdf · s) (hident 0 0).map_eq
  simp only [hcdf, hmin]

/-- **Revenue Equivalence Theorem.**
Any two efficient, IC, IR mechanisms whose type distributions are identically
distributed yield the same expected total revenue. Both equal `𝔼[S₂]`, the
expected second-highest order statistic, which depends only on the type
distribution `F` and the number of bidders `n`—not on the specific auction format.

The two mechanisms may live on different probability spaces `Ω₁`, `Ω₂`. -/
theorem revenue_equivalence
    {Ω₁ : Type} [MeasureSpace Ω₁] [IsProbabilityMeasure (ℙ : Measure Ω₁)]
    {Ω₂ : Type} [MeasureSpace Ω₂] [IsProbabilityMeasure (ℙ : Measure Ω₂)]
    (ℰ₁ : RevenueEquivalenceSetup Ω₁ n) (ℰ₂ : RevenueEquivalenceSetup Ω₂ n)
    (hident : ∀ i j, IdentDistrib (ℰ₁.θ i) (ℰ₂.θ j) ℙ ℙ)
    (ic₁ : ℰ₁.IncentiveCompatible) (ic₂ : ℰ₂.IncentiveCompatible)
    (ir₁ : ℰ₁.IndividuallyRational) (ir₂ : ℰ₂.IndividuallyRational) :
    ℰ₁.expectedRevenue = ℰ₂.expectedRevenue := by
  rw [ℰ₁.total_revenue ic₁ ir₁, ℰ₂.total_revenue ic₂ ir₂]
  exact (ℰ₁.toOrderStatisticsSetup.identDistrib_val ℰ₂.toOrderStatisticsSetup
    hident ⟨n - 2, by have := Nat.AtLeastTwo.prop (n := n); omega⟩).integral_eq

end RevenueEquivalenceSetup

end revenueEquivalence

end
