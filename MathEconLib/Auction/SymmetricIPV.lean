module

public import MathEconLib.Auction.Typeclasses
public import MathEconLib.Statistics.OrderStatistics

/-!
# Winning probabilities and ordered types in symmetric IPV auctions

For independent, identically distributed, atomless private values, a bidder's probability of
winning under strict-highest-bid allocation is the probability that all opponents bid strictly
less. Against truthful opponents this is `F(b)^(n-1)`, where `F` is the common type CDF. Against
opponents using a common weakly increasing strategy on a bounded type interval, the same formula
holds with `F` evaluated at the type threshold associated with the bid.

When types have a common density, their order statistics describe the distribution of ordered
bidder values. The second-highest type is the order statistic with zero-based index `n - 2`.

## Main definitions

* `bidThreshold`: the supremum of types bidding strictly below a bid, including the lower endpoint.
* `Auction.toOrderStatisticsSetup`: the independent, identically distributed bidder types with
  their common density.
* `Auction.S₂`: the second-highest bidder type.

## Main statements

* `Auction.q_eq_pow`: the winning probability against truthful opponents is `F(s)^(n-1)`.
* `Auction.q_strat_eq_cdf_pow`: the winning probability against opponents using a common weakly
  increasing strategy is `F(v₀)^(n-1)`, where `v₀` is the bid threshold.

## Tags

auctions, independent private values, winning probability, order statistics
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open MathEconLib.Mechanism.Auctions

/-! ### Bid threshold for monotone strategies -/

/-- For a bidding strategy `σ` and bid `b`, the supremum of the types in `[lo, hi]` that bid
strictly below `b`, with the lower endpoint `lo` included in the set. If `lo ≤ hi`, the threshold
lies in `[lo, hi]`. -/
noncomputable def bidThreshold (σ : ℝ → ℝ) (lo hi b : ℝ) : ℝ :=
  sSup (insert lo { v ∈ Icc lo hi | σ v < b })

namespace bidThreshold

variable {σ : ℝ → ℝ} {lo hi b v : ℝ}

private lemma set_nonempty : (insert lo { v ∈ Icc lo hi | σ v < b }).Nonempty :=
  Set.insert_nonempty lo _

private lemma set_bddAbove (hle : lo ≤ hi) :
    BddAbove (insert lo { v ∈ Icc lo hi | σ v < b }) :=
  ⟨hi, fun v hv => by
    rcases Set.mem_insert_iff.mp hv with rfl | ⟨hm, _⟩
    · exact hle
    · exact hm.2⟩

lemma mem_Icc (hle : lo ≤ hi) :
    bidThreshold σ lo hi b ∈ Icc lo hi :=
  ⟨le_csSup (set_bddAbove hle) (Set.mem_insert lo _),
   csSup_le set_nonempty fun v hv => by
     rcases Set.mem_insert_iff.mp hv with rfl | ⟨hm, _⟩
     · exact hle
     · exact hm.2⟩

lemma above (hle : lo ≤ hi) (hv : v ∈ Icc lo hi) (hσ : σ v < b) :
    v ≤ bidThreshold σ lo hi b :=
  le_csSup (set_bddAbove hle) (Set.mem_insert_of_mem lo ⟨hv, hσ⟩)

lemma below (hle : lo ≤ hi) (hσ_mono : MonotoneOn σ (Icc lo hi))
    (hv : v ∈ Icc lo hi) (hlt : v < bidThreshold σ lo hi b) :
    σ v < b := by
  obtain ⟨w, hw_mem, hvw⟩ := exists_lt_of_lt_csSup set_nonempty hlt
  rcases Set.mem_insert_iff.mp hw_mem with rfl | ⟨hw_Icc, hw_lt⟩
  · exact absurd hvw (not_lt.mpr hv.1)
  · exact lt_of_le_of_lt (hσ_mono hv hw_Icc (le_of_lt hvw)) hw_lt

lemma le_of_not_lt (hle : lo ≤ hi) (hσ_mono : MonotoneOn σ (Icc lo hi))
    (hv : v ∈ Icc lo hi) (hσ : ¬ σ v < b) :
    bidThreshold σ lo hi b ≤ v :=
  not_lt.mp fun h => hσ (below hle hσ_mono hv h)

end bidThreshold

/-! ### Auction-level results -/

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} [NeZero n]

namespace Auction

variable (A : Auction Ω n)

/-- Under strict-highest-bid allocation and independent, identically distributed, atomless types,
bidder `i` wins with probability `F(s)^(n-1)` when bidding `s` against truthful opponents, where
`F` is the common type CDF. -/
lemma q_eq_pow [HasIndependentTypes A] [HasIdenticalTypes A] [HasAtomlessTypes A]
    (hwinner : UsesStrictHighestBidAllocation A.rules (fun o i => o i))
    (i : Fin n) (s : ℝ) :
    A.q i s = A.commonCDF s ^ (n - 1) := by
  have hx (b) : A.rules.outcome b i =
      {f : Fin n → ℝ | ∀ j ≠ i, f j < f i}.indicator 1 b := congr_fun (hwinner i) b
  simp only [q, q_strat, id, hx, ne_eq]
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

/-! ### Generalized winning probability via bid threshold -/

section QStratCdfPow

variable [HasIndependentTypes A] [HasIdenticalTypes A]
    [HasBoundedTypes A] [HasAtomlessTypes A]

omit [HasIndependentTypes A] [HasAtomlessTypes A] in
private lemma lowestType_le_highestType : A.lowestType ≤ A.highestType := by
  have ⟨ω⟩ := nonempty_of_isProbabilityMeasure (ℙ : Measure Ω)
  have h := HasBoundedTypes.θ_in (A := A) 0 ω
  rw [A.θmin_eq_lowestType, A.θmax_eq_highestType] at h
  exact h.1.trans h.2

omit [HasIndependentTypes A] in
/-- For identically distributed, bounded, atomless types and a weakly increasing strategy `σ`, the
probability that bidder `j` bids strictly below `b` is the probability that a type is at most the
bid threshold. -/
private lemma measure_sigma_lt_eq
    {σ : ℝ → ℝ} (hσ_mono : MonotoneOn σ (Icc A.lowestType A.highestType))
    (j : Fin n) (b : ℝ) :
    ℙ (A.θ j ⁻¹' (σ ⁻¹' Iio b)) =
      ℙ (A.θ 0 ⁻¹' Iic (bidThreshold σ A.lowestType A.highestType b)) := by
  set v₀ := bidThreshold σ A.lowestType A.highestType b
  have hle := A.lowestType_le_highestType
  -- Sandwich: {θⱼ < v₀} ⊆ {σ(θⱼ) < b} ⊆ {θⱼ ≤ v₀}
  have h_lo : A.θ j ⁻¹' Iio v₀ ⊆ A.θ j ⁻¹' (σ ⁻¹' Iio b) := fun ω hω => by
    simp only [mem_preimage, mem_Iio] at hω ⊢
    have hθ := HasBoundedTypes.θ_in (A := A) j ω
    rw [A.θmin_eq_lowestType, A.θmax_eq_highestType] at hθ
    exact bidThreshold.below hle hσ_mono hθ hω
  have h_hi : A.θ j ⁻¹' (σ ⁻¹' Iio b) ⊆ A.θ j ⁻¹' Iic v₀ := fun ω hω => by
    simp only [mem_preimage, mem_Iio, mem_Iic] at hω ⊢
    have hθ := HasBoundedTypes.θ_in (A := A) j ω
    rw [A.θmin_eq_lowestType, A.θmax_eq_highestType] at hθ
    exact bidThreshold.above hle hθ hω
  -- Squeeze using identical distributions and atomless types.
  have h_ident_lo : ℙ (A.θ j ⁻¹' Iio v₀) = ℙ (A.θ 0 ⁻¹' Iio v₀) :=
    (HasIdenticalTypes.θ_identical j 0).measure_mem_eq measurableSet_Iio
  have h_ident_hi : ℙ (A.θ j ⁻¹' Iic v₀) = ℙ (A.θ 0 ⁻¹' Iic v₀) :=
    (HasIdenticalTypes.θ_identical j 0).measure_mem_eq measurableSet_Iic
  have h_atomless : ℙ (A.θ 0 ⁻¹' Iio v₀) = ℙ (A.θ 0 ⁻¹' Iic v₀) := by
    have : NoAtoms (Measure.map (A.θ 0) ℙ) := HasAtomlessTypes.θ_noAtoms
    rw [← Measure.map_apply (A.θ_measurable 0) measurableSet_Iio,
        ← Measure.map_apply (A.θ_measurable 0) measurableSet_Iic]
    exact measure_congr Iio_ae_eq_Iic
  apply le_antisymm
  · calc ℙ (A.θ j ⁻¹' (σ ⁻¹' Iio b))
        _ ≤ ℙ (A.θ j ⁻¹' Iic v₀) := measure_mono h_hi
        _ = ℙ (A.θ 0 ⁻¹' Iic v₀) := h_ident_hi
  · calc ℙ (A.θ 0 ⁻¹' Iic v₀)
        _ = ℙ (A.θ 0 ⁻¹' Iio v₀) := h_atomless.symm
        _ = ℙ (A.θ j ⁻¹' Iio v₀) := h_ident_lo.symm
        _ ≤ ℙ (A.θ j ⁻¹' (σ ⁻¹' Iio b)) := measure_mono h_lo

/-- Under strict-highest-bid allocation and independent, identically distributed, bounded, atomless
types, bidder `i` wins with bid `b` against opponents using a measurable, weakly increasing
strategy `σ` with probability `F(v₀)^(n-1)`, where `F` is the common type CDF and `v₀` is the bid
threshold. -/
lemma q_strat_eq_cdf_pow
    (hwinner : UsesStrictHighestBidAllocation A.rules (fun o i => o i)) {σ : ℝ → ℝ}
    (hσ_mono : MonotoneOn σ (Icc A.lowestType A.highestType))
    (hσ_meas : Measurable σ) (i : Fin n) (b : ℝ) :
    A.q_strat σ i b =
      A.commonCDF (bidThreshold σ A.lowestType A.highestType b) ^ (n - 1) := by
  set v₀ := bidThreshold σ A.lowestType A.highestType b
  have hx (b) : A.rules.outcome b i =
      {f : Fin n → ℝ | ∀ j ≠ i, f j < f i}.indicator 1 b := congr_fun (hwinner i) b
  simp only [q_strat, hx, ne_eq]
  have hrw (ω) :
      {f : Fin n → ℝ | ∀ j ≠ i, f j < f i}.indicator 1
        (Function.update (fun j => σ (A.θ j ω)) i b) =
      (⋂ j ∈ Finset.univ.erase i, A.θ j ⁻¹' (σ ⁻¹' Iio b)).indicator
        (1 : Ω → ℝ) ω := by
    simpa [Function.update, Set.indicator] using by grind
  simp_rw [hrw]
  have hmeas : MeasurableSet <|
      ⋂ j ∈ Finset.univ.erase i, A.θ j ⁻¹' (σ ⁻¹' Iio b) :=
    MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      A.θ_measurable j (hσ_meas measurableSet_Iio)
  rw [integral_indicator_one hmeas, Measure.real,
    HasIndependentTypes.θ_indep.meas_biInter fun j _ =>
      ⟨σ ⁻¹' Iio b, hσ_meas measurableSet_Iio, rfl⟩,
    ENNReal.toReal_prod]
  have hfactor (j : Fin n) :
      (ℙ (A.θ j ⁻¹' (σ ⁻¹' Iio b))).toReal = A.commonCDF v₀ := by
    rw [A.commonCDF_eq]
    congr 1
    exact A.measure_sigma_lt_eq hσ_mono j b
  simp_rw [hfactor, Finset.prod_const,
    Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin]

end QStratCdfPow

/-! ### Ordered bidder types -/

variable [n.AtLeastTwo]

/-- The auction's bidder types as independent, identically distributed real random variables with a
common density. Their order statistics give the ordered bidder types. -/
@[simps]
noncomputable def toOrderStatisticsSetup
    [HasIndependentTypes A] [HasIdenticalTypes A] [HasDensity A] :
    OrderStatisticsSetup Ω n where
  X := A.θ
  X_measurable := A.θ_measurable
  X_indep := HasIndependentTypes.θ_indep
  X_ident := HasIdenticalTypes.θ_identical
  X_hasPDF := HasDensity.θ_hasPDF

/-- The second-highest bidder type at state `ω`, for an auction with at least two bidders. -/
noncomputable def S₂ [HasIndependentTypes A] [HasIdenticalTypes A] [HasDensity A]
    (ω : Ω) : ℝ :=
  A.toOrderStatisticsSetup.val ⟨n - 2, by grind [Nat.AtLeastTwo.prop (n := n)]⟩ ω

end Auction

end
