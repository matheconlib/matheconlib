module

public import Auctionlib.Auction.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.IdentDistrib
public import Auctionlib.Statistics.OrderStatistics

/-!
# Symmetric IPV Auctions

`IsSymmetricIPV` is a typeclass on `Auction` asserting that types are
i.i.d. with density and atomless distribution.

## Main definitions

- `Auction.lowestType`, `Auction.highestType` — common type bounds
- `Auction.commonCDF` — the shared CDF via `ProbabilityTheory.cdf`

## Main results

- `Auction.q_eq_pow`: under efficient allocation, `q(i, s) = F(s)^(n-1)`
- `Auction.commonCDF_lowestType`: `F(lowestType) = 0`
- `Auction.commonCDF_highestType`: `F(highestType) = 1`
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} [n.AtLeastTwo]

/-- Symmetric IPV: types are i.i.d. with density and atomless distribution,
and all bidders share the same type bounds. -/
class Auction.IsSymmetricIPV (A : Auction Ω n) : Prop where
  /-- Types are mutually independent -/
  θ_indep : iIndepFun A.θ ℙ
  /-- Types are identically distributed -/
  θ_identical : ∀ i j, IdentDistrib (A.θ i) (A.θ j) ℙ ℙ
  /-- Each type lies in its interval -/
  θ_in : ∀ i (ω : Ω), A.θ i ω ∈ Icc (A.θmin i) (A.θmax i)
  /-- Each type has a density -/
  θ_hasPDF : ∀ i, HasPDF (A.θ i) ℙ volume
  /-- Type distribution is atomless -/
  θ_noAtoms : NoAtoms (Measure.map (A.θ 0) ℙ)
  /-- Common lower type bound -/
  θmin_eq : ∀ i, A.θmin i = A.θmin 0
  /-- Common upper type bound -/
  θmax_eq : ∀ i, A.θmax i = A.θmax 0

namespace Auction

variable (A : Auction Ω n) [A.IsSymmetricIPV]

instance noAtoms_map_θ₀ : NoAtoms (Measure.map (A.θ 0) ℙ) :=
  IsSymmetricIPV.θ_noAtoms

/-! ### Common type bounds and CDF -/

noncomputable def lowestType : ℝ := A.θmin 0

@[simp] lemma θmin_eq_lowestType (i) : A.θmin i = A.lowestType := by
  rw [IsSymmetricIPV.θmin_eq]; rfl

noncomputable def highestType : ℝ := A.θmax 0

@[simp] lemma θmax_eq_highestType (i) : A.θmax i = A.highestType := by
  rw [IsSymmetricIPV.θmax_eq]; rfl

/-- The common CDF: `F(s) = cdf(Measure.map (θ₀) ℙ)(s)`. -/
noncomputable abbrev commonCDF (s : ℝ) : ℝ :=
  ProbabilityTheory.cdf (Measure.map (A.θ 0) ℙ) s

instance isProbabilityMeasure_map_θ₀ :
    IsProbabilityMeasure (Measure.map (A.θ 0) ℙ) :=
  Measure.isProbabilityMeasure_map (A.θ_measurable 0).aemeasurable

lemma commonCDF_nonneg (s : ℝ) : 0 ≤ A.commonCDF s := cdf_nonneg _ s
lemma commonCDF_le_one (s : ℝ) : A.commonCDF s ≤ 1 := cdf_le_one _ s
lemma commonCDF_mono : Monotone A.commonCDF := monotone_cdf _
lemma commonCDF_measurable : Measurable A.commonCDF := A.commonCDF_mono.measurable

lemma commonCDF_eq (s : ℝ) :
    A.commonCDF s = Measure.real ℙ (A.θ 0 ⁻¹' Iic s) := by
  simp [ProbabilityTheory.cdf_eq_real, Measure.real,
    Measure.map_apply (A.θ_measurable 0) measurableSet_Iic]

@[simp] lemma commonCDF_lowestType : A.commonCDF A.lowestType = 0 := by
  rw [A.commonCDF_eq, Measure.real]
  suffices h : ℙ (A.θ 0 ⁻¹' Iic A.lowestType) = 0 by simp [h]
  have heq : A.θ 0 ⁻¹' Iic A.lowestType = A.θ 0 ⁻¹' {A.lowestType} := by
    ext ω
    simp only [mem_preimage, mem_Iic, mem_singleton_iff]
    constructor
    · intro h
      have hθ := IsSymmetricIPV.θ_in (A := A) 0 ω
      rw [A.θmin_eq_lowestType] at hθ
      exact le_antisymm h hθ.1
    · intro h; exact le_of_eq h
  rw [heq, ← Measure.map_apply (A.θ_measurable 0) (measurableSet_singleton _),
    measure_singleton]

@[simp] lemma commonCDF_highestType : A.commonCDF A.highestType = 1 := by
  rw [A.commonCDF_eq]
  have huniv : A.θ 0 ⁻¹' Iic A.highestType = Set.univ := by
    ext ω
    simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
    have hθ := IsSymmetricIPV.θ_in (A := A) 0 ω
    rw [A.θmax_eq_highestType] at hθ
    exact hθ.2
  simp [huniv]

/-! ### Bridge to OrderStatistics -/

@[simps]
noncomputable def toOrderStatisticsSetup : OrderStatisticsSetup Ω n where
  X := A.θ
  X_measurable := A.θ_measurable
  X_indep := IsSymmetricIPV.θ_indep
  X_ident := IsSymmetricIPV.θ_identical
  X_hasPDF := IsSymmetricIPV.θ_hasPDF

/-! ### Efficient allocation → q = F^(n-1) -/

/-- Efficient allocation: bidder i wins iff they have the strictly highest type. -/
def Efficient : Prop :=
  ∀ i, A.rules.x i = {f | ∀ j ≠ i, f j < f i}.indicator 1

/-- Under efficient allocation, `q(i, s) = F(s)^(n-1)`. -/
lemma q_eq_pow (eff : A.Efficient) (i : Fin n) (s : ℝ) :
    A.q i s = A.commonCDF s ^ (n - 1) := by
  simp only [q, eff i, ne_eq]
  have hrw (ω) :
      {f : Fin n → ℝ | ∀ j ≠ i, f j < f i}.indicator 1
        (Function.update (A.θ · ω) i s) =
      (⋂ j ∈ Finset.univ.erase i, A.θ j ⁻¹' Iio s).indicator (1 : Ω → ℝ) ω := by
    simpa [Function.update, Set.indicator] using by grind
  simp_rw [hrw]
  have hmeas : MeasurableSet <|
      ⋂ j ∈ Finset.univ.erase i, A.θ j ⁻¹' Iio s :=
    MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      A.θ_measurable j measurableSet_Iio
  rw [integral_indicator_one hmeas, Measure.real,
    IsSymmetricIPV.θ_indep.meas_biInter fun j _ =>
      ⟨Iio s, measurableSet_Iio, rfl⟩, ENNReal.toReal_prod]
  have hfactor j :
      (ℙ (A.θ j ⁻¹' Iio s)).toReal = A.commonCDF s := by
    rw [A.commonCDF_eq]
    congr 1
    calc ℙ (A.θ j ⁻¹' Iio s)
        _ = ℙ (A.θ 0 ⁻¹' Iio s) :=
          (IsSymmetricIPV.θ_identical j 0).measure_mem_eq measurableSet_Iio
        _ = (Measure.map (A.θ 0) ℙ) (Iio s) :=
          (Measure.map_apply (A.θ_measurable 0) measurableSet_Iio).symm
        _ = (Measure.map (A.θ 0) ℙ) (Iic s) := measure_congr Iio_ae_eq_Iic
        _ = ℙ (A.θ 0 ⁻¹' Iic s) :=
          Measure.map_apply (A.θ_measurable 0) measurableSet_Iic
  simp_rw [hfactor, Finset.prod_const,
    Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin]

/-! ### Individual rationality and revenue -/

/-- Individual rationality: lowest type gets zero utility. -/
def IndividuallyRational : Prop := ∀ i, A.U i A.lowestType = 0

/-- Expected total revenue. -/
noncomputable def expectedRevenue : ℝ :=
  𝔼[fun ω => ∑ i : Fin n, A.p i (A.θ i ω)]

/-- The second-highest order statistic. -/
noncomputable def S₂ (ω : Ω) : ℝ :=
  A.toOrderStatisticsSetup.val ⟨n - 2, by grind [Nat.AtLeastTwo.prop (n := n)]⟩ ω

end Auction

end
