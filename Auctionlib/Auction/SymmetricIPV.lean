module

public import Auctionlib.Auction.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.IdentDistrib
public import Auctionlib.Statistics.OrderStatistics

/-!
# Auction Environment Typeclasses

Composable typeclasses describing properties of the auction environment.
These follow the reference (Section 3a):

- `HasIndependentTypes` — types are mutually independent (IPV)
- `HasIdenticalTypes` — all bidders share the same distribution (symmetric)
- `HasBoundedTypes` — each type lies in its declared interval
- `HasDensity` — type distribution has a density (HasPDF)
- `HasAtomlessTypes` — type distribution is atomless

`IsSymmetricIPV` bundles all five for convenience.

## Main results

- `Auction.q_eq_pow`: under efficiency + independence + identical + bounded,
  `q(i, s) = F(s)^(n-1)`
- `commonCDF_lowestType / highestType`: CDF boundary values (needs bounded + atomless)
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} [NeZero n]

namespace Auction

/-! ### Composable typeclasses -/

/-- Types are mutually independent (the "I" in IPV). -/
class HasIndependentTypes (A : Auction Ω n) : Prop where
  θ_indep : iIndepFun A.θ ℙ

/-- All bidders share the same type distribution and bounds (symmetric bidders). -/
class HasIdenticalTypes (A : Auction Ω n) : Prop where
  θ_identical : ∀ i j, IdentDistrib (A.θ i) (A.θ j) ℙ ℙ
  θmin_eq : ∀ i, A.θmin i = A.θmin 0
  θmax_eq : ∀ i, A.θmax i = A.θmax 0

/-- Each bidder's type lies in the declared interval. -/
class HasBoundedTypes (A : Auction Ω n) : Prop where
  θ_in : ∀ i (ω : Ω), A.θ i ω ∈ Icc (A.θmin i) (A.θmax i)

/-- Each bidder's type distribution has a density w.r.t. Lebesgue measure. -/
class HasDensity (A : Auction Ω n) : Prop where
  θ_hasPDF : ∀ i, HasPDF (A.θ i) ℙ volume

/-- The type distribution is atomless. -/
class HasAtomlessTypes (A : Auction Ω n) : Prop where
  θ_noAtoms : NoAtoms (Measure.map (A.θ 0) ℙ)

/-! ### IsSymmetricIPV (convenience bundle) -/

/-- Symmetric IPV: all five properties bundled. -/
class IsSymmetricIPV (A : Auction Ω n) : Prop extends
    HasIndependentTypes A, HasIdenticalTypes A, HasBoundedTypes A,
    HasDensity A, HasAtomlessTypes A

/-! ### Common type bounds (needs HasIdenticalTypes) -/

variable (A : Auction Ω n)

noncomputable def lowestType [HasIdenticalTypes A] : ℝ := A.θmin 0

@[simp] lemma θmin_eq_lowestType [HasIdenticalTypes A] (i) :
    A.θmin i = A.lowestType := by
  rw [HasIdenticalTypes.θmin_eq]; rfl

noncomputable def highestType [HasIdenticalTypes A] : ℝ := A.θmax 0

@[simp] lemma θmax_eq_highestType [HasIdenticalTypes A] (i) :
    A.θmax i = A.highestType := by
  rw [HasIdenticalTypes.θmax_eq]; rfl

/-! ### Common CDF (needs HasIdenticalTypes) -/

instance isProbabilityMeasure_map_θ₀ :
    IsProbabilityMeasure (Measure.map (A.θ 0) ℙ) :=
  Measure.isProbabilityMeasure_map (A.θ_measurable 0).aemeasurable

/-- The common CDF: `F(s) = cdf(Measure.map (θ₀) ℙ)(s)`. -/
noncomputable abbrev commonCDF [HasIdenticalTypes A] (s : ℝ) : ℝ :=
  ProbabilityTheory.cdf (Measure.map (A.θ 0) ℙ) s

set_option linter.unusedSectionVars false in
lemma commonCDF_nonneg [HasIdenticalTypes A] (s : ℝ) :
    0 ≤ A.commonCDF s := cdf_nonneg _ s

set_option linter.unusedSectionVars false in
lemma commonCDF_le_one [HasIdenticalTypes A] (s : ℝ) :
    A.commonCDF s ≤ 1 := cdf_le_one _ s

set_option linter.unusedSectionVars false in
lemma commonCDF_mono [HasIdenticalTypes A] :
    Monotone A.commonCDF := monotone_cdf _

lemma commonCDF_measurable [HasIdenticalTypes A] :
    Measurable A.commonCDF := (A.commonCDF_mono).measurable

lemma commonCDF_eq [HasIdenticalTypes A] (s : ℝ) :
    A.commonCDF s = Measure.real ℙ (A.θ 0 ⁻¹' Iic s) := by
  simp [ProbabilityTheory.cdf_eq_real, Measure.real,
    Measure.map_apply (A.θ_measurable 0) measurableSet_Iic]

/-! ### CDF boundary values (needs HasIdenticalTypes + HasBoundedTypes + HasAtomlessTypes) -/

@[simp] lemma commonCDF_lowestType
    [HasIdenticalTypes A] [HasBoundedTypes A] [HasAtomlessTypes A] :
    A.commonCDF A.lowestType = 0 := by
  rw [A.commonCDF_eq, Measure.real]
  suffices h : ℙ (A.θ 0 ⁻¹' Iic A.lowestType) = 0 by simp [h]
  have heq : A.θ 0 ⁻¹' Iic A.lowestType = A.θ 0 ⁻¹' {A.lowestType} := by
    ext ω
    simp only [mem_preimage, mem_Iic, mem_singleton_iff]
    constructor
    · intro h
      have hθ := HasBoundedTypes.θ_in (A := A) 0 ω
      rw [A.θmin_eq_lowestType] at hθ
      exact le_antisymm h hθ.1
    · intro h; exact le_of_eq h
  rw [heq, ← Measure.map_apply (A.θ_measurable 0) (measurableSet_singleton _)]
  have : NoAtoms (Measure.map (A.θ 0) ℙ) := HasAtomlessTypes.θ_noAtoms
  exact measure_singleton _

@[simp] lemma commonCDF_highestType
    [HasIdenticalTypes A] [HasBoundedTypes A] :
    A.commonCDF A.highestType = 1 := by
  rw [A.commonCDF_eq]
  have huniv : A.θ 0 ⁻¹' Iic A.highestType = Set.univ := by
    ext ω
    simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
    have hθ := HasBoundedTypes.θ_in (A := A) 0 ω
    rw [A.θmax_eq_highestType] at hθ
    exact hθ.2
  simp [huniv]

/-! ### Bridge to OrderStatistics (needs independence + identical + density) -/

variable [n.AtLeastTwo]

@[simps]
noncomputable def toOrderStatisticsSetup
    [HasIndependentTypes A] [HasIdenticalTypes A] [HasDensity A] :
    OrderStatisticsSetup Ω n where
  X := A.θ
  X_measurable := A.θ_measurable
  X_indep := HasIndependentTypes.θ_indep
  X_ident := HasIdenticalTypes.θ_identical
  X_hasPDF := HasDensity.θ_hasPDF

/-! ### Efficient allocation → q = F^(n-1) -/

/-- Efficient allocation: bidder i wins iff they have the strictly highest type. -/
def Efficient : Prop :=
  ∀ i, A.rules.x i = {f | ∀ j ≠ i, f j < f i}.indicator 1

omit [n.AtLeastTwo] in
/-- Under efficient allocation, `q(i, s) = F(s)^(n-1)`.
Needs: independence + identical + atomless. -/
lemma q_eq_pow [HasIndependentTypes A] [HasIdenticalTypes A] [HasAtomlessTypes A]
    (eff : A.Efficient) (i : Fin n) (s : ℝ) :
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
    HasIndependentTypes.θ_indep.meas_biInter fun j _ =>
      ⟨Iio s, measurableSet_Iio, rfl⟩, ENNReal.toReal_prod]
  have hfactor j :
      (ℙ (A.θ j ⁻¹' Iio s)).toReal = A.commonCDF s := by
    rw [A.commonCDF_eq]
    congr 1
    calc ℙ (A.θ j ⁻¹' Iio s)
        _ = ℙ (A.θ 0 ⁻¹' Iio s) :=
          (HasIdenticalTypes.θ_identical j 0).measure_mem_eq measurableSet_Iio
        _ = (Measure.map (A.θ 0) ℙ) (Iio s) :=
          (Measure.map_apply (A.θ_measurable 0) measurableSet_Iio).symm
        _ = (Measure.map (A.θ 0) ℙ) (Iic s) := by
          have : NoAtoms (Measure.map (A.θ 0) ℙ) := HasAtomlessTypes.θ_noAtoms
          exact measure_congr Iio_ae_eq_Iic
        _ = ℙ (A.θ 0 ⁻¹' Iic s) :=
          Measure.map_apply (A.θ_measurable 0) measurableSet_Iic
  simp_rw [hfactor, Finset.prod_const,
    Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin]

/-! ### Expectation of sum over identical types -/

omit [n.AtLeastTwo] in
/-- **Linearity + symmetry**: for identically distributed types,
`E[Σ_{j≠i} f(V_j)] = (n−1) · E[f(V₀)]`.

Combines linearity of expectation (`integral_finset_sum`) with
identical distribution (`IdentDistrib.map_eq`). -/
theorem expected_sum_erase [HasIdenticalTypes A]
    (f : ℝ → ℝ) (hf_meas : Measurable f) (i : Fin n)
    (hf_int : ∀ j, Integrable (fun ω => f (A.θ j ω)) ℙ) :
    𝔼[fun ω => ∑ j ∈ Finset.univ.erase i, f (A.θ j ω)] =
      (↑(n - 1) : ℝ) * 𝔼[fun ω => f (A.θ 0 ω)] := by
  rw [integral_finset_sum _ (fun j _ => hf_int j)]
  have hsym : ∀ j, ∫ ω, f (A.θ j ω) ∂ℙ = ∫ ω, f (A.θ 0 ω) ∂ℙ := fun j => by
    rw [← integral_map (A.θ_measurable j).aemeasurable
          hf_meas.aestronglyMeasurable,
        (HasIdenticalTypes.θ_identical j 0).map_eq,
        integral_map (A.θ_measurable 0).aemeasurable
          hf_meas.aestronglyMeasurable]
  simp_rw [hsym]
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ### Individual rationality and revenue -/

/-- Individual rationality: lowest type gets zero utility. -/
def IndividuallyRational [HasIdenticalTypes A] : Prop :=
  ∀ i, A.U i A.lowestType = 0

/-- Expected total revenue. -/
noncomputable def expectedRevenue : ℝ :=
  𝔼[fun ω => ∑ i : Fin n, A.p i (A.θ i ω)]

/-- The second-highest order statistic. -/
noncomputable def S₂ [HasIndependentTypes A] [HasIdenticalTypes A] [HasDensity A]
    (ω : Ω) : ℝ :=
  A.toOrderStatisticsSetup.val ⟨n - 2, by grind [Nat.AtLeastTwo.prop (n := n)]⟩ ω

end Auction

end
