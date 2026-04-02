module

public import Auctionlib.Auction.Typeclasses
public import Auctionlib.Statistics.OrderStatistics

/-!
# Symmetric IPV Results

Results requiring the full `IsSymmetricIPV` bundle or multiple composable
typeclasses together with `OrderStatistics`:

- `Auction.toOrderStatisticsSetup`: bridge to order-statistics framework
- `Auction.q_eq_pow`: under efficiency + independence + identical + atomless,
  `q(i, s) = F(s)^(n-1)`
- `Auction.Efficient`: efficient allocation definition
- `Auction.S₂`: second-highest order statistic
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} [NeZero n]

namespace Auction

variable (A : Auction Ω n)

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
def Efficient : Prop := A.rules.IsEfficient

omit [n.AtLeastTwo] in
/-- Under efficient allocation, `q(i, s) = F(s)^(n-1)`.
Needs: independence + identical + atomless. -/
lemma q_eq_pow [HasIndependentTypes A] [HasIdenticalTypes A] [HasAtomlessTypes A]
    (eff : A.Efficient) (i : Fin n) (s : ℝ) :
    A.q i s = A.commonCDF s ^ (n - 1) := by
  simp only [q, q_strat, id, eff i, ne_eq]
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

/-! ### Second-highest order statistic -/

/-- The second-highest order statistic. -/
noncomputable def S₂ [HasIndependentTypes A] [HasIdenticalTypes A] [HasDensity A]
    (ω : Ω) : ℝ :=
  A.toOrderStatisticsSetup.val ⟨n - 2, by grind [Nat.AtLeastTwo.prop (n := n)]⟩ ω

end Auction

end
