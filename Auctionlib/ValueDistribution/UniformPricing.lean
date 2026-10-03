module

public import Auctionlib.ValueDistribution.PostedPrice
public import Auctionlib.ValueDistribution.Uniform

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Posted Pricing with Uniform Buyer Values

For a buyer whose value is uniform on `[a, b]`, this file specializes the
existing seller-profit formula. The maximization is over posted prices in
`[a, b]`; prices above `b` are not included because they all yield no sale.

The candidate price is the unconstrained quadratic optimum `(b + r) / 2`
projected onto the feasible interval. Here `r` is continuation value, and
the unconditional acquisition cost does not affect the maximizing price.
-/

@[expose] public section

noncomputable section

open Set
open SingleParameterProblem

namespace ValueDistribution

/-- The unconstrained uniform-profit maximizer projected onto `[a, b]`. -/
def uniformOptimalPrice (a b continuationValue : ℝ) : ℝ :=
  max a (min b ((b + continuationValue) / 2))

/-- The projected candidate is a feasible price. -/
theorem uniformOptimalPrice_mem_Icc (a b continuationValue : ℝ) (hab : a < b) :
    uniformOptimalPrice a b continuationValue ∈ Icc a b := by
  constructor
  · exact le_max_left a (min b ((b + continuationValue) / 2))
  · exact max_le hab.le (min_le_left b ((b + continuationValue) / 2))

/-- If the unconstrained peak lies below the support, the lower endpoint is
the selected price. -/
theorem uniformOptimalPrice_eq_left (a b continuationValue : ℝ)
    (hpeak : (b + continuationValue) / 2 ≤ a) :
    uniformOptimalPrice a b continuationValue = a := by
  exact max_eq_left ((min_le_right b ((b + continuationValue) / 2)).trans hpeak)

/-- If the unconstrained peak lies above the support, the upper endpoint is
the selected price. -/
theorem uniformOptimalPrice_eq_right (a b continuationValue : ℝ) (hab : a < b)
    (hpeak : b ≤ (b + continuationValue) / 2) :
    uniformOptimalPrice a b continuationValue = b := by
  simp [uniformOptimalPrice, min_eq_left hpeak, max_eq_right hab.le]

/-- When the unconstrained peak is feasible, no projection is needed. -/
theorem uniformOptimalPrice_eq_peak (a b continuationValue : ℝ)
    (hpeak : (b + continuationValue) / 2 ∈ Icc a b) :
    uniformOptimalPrice a b continuationValue = (b + continuationValue) / 2 := by
  simp [uniformOptimalPrice, min_eq_right hpeak.2, max_eq_right hpeak.1]

private theorem uniform_margin_gap (b continuationValue price candidate : ℝ) :
    (candidate - continuationValue) * (b - candidate) -
        (price - continuationValue) * (b - price) =
      (candidate - price) * (b + continuationValue - candidate - price) := by
  ring

/-- The projected quadratic peak has a nonnegative margin gap, and the gap
vanishes only at that price. The three cases correspond to the lower endpoint,
the upper endpoint, and the interior of the feasible interval. -/
private theorem uniform_margin_gap_nonneg_and_eq
    (a b continuationValue price : ℝ) (hab : a < b) (hprice : price ∈ Icc a b) :
    let candidate := uniformOptimalPrice a b continuationValue
    0 ≤ (candidate - price) * (b + continuationValue - candidate - price) ∧
      ((candidate - price) * (b + continuationValue - candidate - price) = 0 →
        price = candidate) := by
  dsimp only
  by_cases hlow : (b + continuationValue) / 2 ≤ a
  · rw [uniformOptimalPrice_eq_left a b continuationValue hlow]
    have hfactor : b + continuationValue - a - price ≤ a - price := by
      linarith
    have hleft : a - price ≤ 0 := sub_nonpos.mpr hprice.1
    have hright : b + continuationValue - a - price ≤ 0 := hfactor.trans hleft
    constructor
    · exact mul_nonneg_of_nonpos_of_nonpos hleft hright
    · intro hzero
      by_contra hne
      have hstrict : a < price := lt_of_le_of_ne hprice.1 (Ne.symm hne)
      have hleftStrict : a - price < 0 := sub_neg.mpr hstrict
      have hrightStrict : b + continuationValue - a - price < 0 :=
        hfactor.trans_lt hleftStrict
      exact (ne_of_gt (mul_pos_of_neg_of_neg hleftStrict hrightStrict)) hzero
  · by_cases hhigh : b ≤ (b + continuationValue) / 2
    · rw [uniformOptimalPrice_eq_right a b continuationValue hab hhigh]
      have hfactor : b - price ≤ b + continuationValue - b - price := by
        linarith
      have hleft : 0 ≤ b - price := sub_nonneg.mpr hprice.2
      have hright : 0 ≤ b + continuationValue - b - price := hleft.trans hfactor
      constructor
      · exact mul_nonneg hleft hright
      · intro hzero
        by_contra hne
        have hstrict : price < b := lt_of_le_of_ne hprice.2 hne
        have hleftStrict : 0 < b - price := sub_pos.mpr hstrict
        have hrightStrict : 0 < b + continuationValue - b - price :=
          hleftStrict.trans_le hfactor
        exact (ne_of_gt (mul_pos hleftStrict hrightStrict)) hzero
    · have hpeak : (b + continuationValue) / 2 ∈ Icc a b :=
        ⟨le_of_lt (lt_of_not_ge hlow), le_of_lt (lt_of_not_ge hhigh)⟩
      rw [uniformOptimalPrice_eq_peak a b continuationValue hpeak]
      have hfactor :
          b + continuationValue - (b + continuationValue) / 2 - price =
            (b + continuationValue) / 2 - price := by
        ring
      rw [hfactor]
      constructor
      · exact mul_self_nonneg _
      · intro hzero
        have hdiff : (b + continuationValue) / 2 - price = 0 :=
          mul_self_eq_zero.mp hzero
        linarith

/-- Uniform posted-price seller profit is continuation value minus the
unconditional acquisition cost, plus margin times the fraction of buyers
whose values meet the price. -/
theorem sellerProfit_uniformInterval (a b : ℝ) (hab : a < b)
    (price continuationValue acquisitionCost : ℝ) (hprice : price ∈ Icc a b) :
    (uniformInterval a b hab).sellerProfit
        (postedPriceProblem a b price) continuationValue acquisitionCost =
      continuationValue - acquisitionCost +
        (price - continuationValue) * ((b - price) / (b - a)) := by
  rw [(uniformInterval a b hab).sellerProfit_postedPriceProblem,
    uniformInterval_probAtLeast a b hab price hprice]

private theorem sellerProfit_uniformInterval_gap (a b : ℝ) (hab : a < b)
    (price continuationValue acquisitionCost : ℝ) (hprice : price ∈ Icc a b) :
    let candidate := uniformOptimalPrice a b continuationValue
    (uniformInterval a b hab).sellerProfit
        (postedPriceProblem a b candidate) continuationValue acquisitionCost -
      (uniformInterval a b hab).sellerProfit
        (postedPriceProblem a b price) continuationValue acquisitionCost =
      (candidate - price) * (b + continuationValue - candidate - price) /
        (b - a) := by
  dsimp only
  rw [sellerProfit_uniformInterval a b hab _ continuationValue acquisitionCost
      (uniformOptimalPrice_mem_Icc a b continuationValue hab),
    sellerProfit_uniformInterval a b hab price continuationValue acquisitionCost hprice]
  rw [← uniform_margin_gap b continuationValue price
    (uniformOptimalPrice a b continuationValue)]
  ring

/-- Among prices in the value interval, the projected quadratic peak
maximizes the existing seller-profit objective. -/
theorem isMaxOn_sellerProfit_uniformInterval (a b : ℝ) (hab : a < b)
    (continuationValue acquisitionCost : ℝ) :
    IsMaxOn
      (fun price ↦
        (uniformInterval a b hab).sellerProfit
          (postedPriceProblem a b price) continuationValue acquisitionCost)
      (Icc a b) (uniformOptimalPrice a b continuationValue) := by
  intro price hprice
  have hgap :=
    (uniform_margin_gap_nonneg_and_eq a b continuationValue price hab hprice).1
  have hprofitGap :=
    sellerProfit_uniformInterval_gap a b hab price continuationValue acquisitionCost hprice
  have hden : 0 ≤ b - a := sub_nonneg.mpr hab.le
  have hquotient :
      0 ≤ (uniformOptimalPrice a b continuationValue - price) *
        (b + continuationValue - uniformOptimalPrice a b continuationValue - price) /
          (b - a) :=
    div_nonneg hgap hden
  dsimp only at hprofitGap
  rw [← hprofitGap] at hquotient
  exact sub_nonneg.mp hquotient

/-- Any maximizing feasible uniform posted price is the projected peak.
Uniqueness is stated only within `[a, b]`: prices above `b` all produce no
sale and are not compared here. -/
theorem uniformOptimalPrice_eq_of_isMaxOn_sellerProfit_uniformInterval
    (a b : ℝ) (hab : a < b) (price continuationValue acquisitionCost : ℝ)
    (hprice : price ∈ Icc a b)
    (hmax : IsMaxOn
      (fun candidate ↦
        (uniformInterval a b hab).sellerProfit
          (postedPriceProblem a b candidate) continuationValue acquisitionCost)
      (Icc a b) price) :
    price = uniformOptimalPrice a b continuationValue := by
  have hoptimal := isMaxOn_sellerProfit_uniformInterval a b hab
    continuationValue acquisitionCost
  have hcandidate := uniformOptimalPrice_mem_Icc a b continuationValue hab
  have hprofit :
      (uniformInterval a b hab).sellerProfit
          (postedPriceProblem a b price) continuationValue acquisitionCost =
        (uniformInterval a b hab).sellerProfit
          (postedPriceProblem a b (uniformOptimalPrice a b continuationValue))
          continuationValue acquisitionCost :=
    le_antisymm (hoptimal hprice) (hmax hcandidate)
  have hgap :=
    sellerProfit_uniformInterval_gap a b hab price continuationValue acquisitionCost hprice
  have hzero :
      (uniformOptimalPrice a b continuationValue - price) *
        (b + continuationValue - uniformOptimalPrice a b continuationValue - price) /
          (b - a) = 0 := by
    dsimp only at hgap
    linarith
  have hden : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have hnumerator :
      (uniformOptimalPrice a b continuationValue - price) *
        (b + continuationValue - uniformOptimalPrice a b continuationValue - price) = 0 := by
    simpa [hden] using hzero
  exact (uniform_margin_gap_nonneg_and_eq a b continuationValue price hab hprice).2
    hnumerator

/-! ## Comparative statics of the maximizing price -/

/-- Raising the lower endpoint cannot lower the optimal posted price. This
algebraic statement also holds when the interval endpoints are not ordered. -/
theorem monotone_uniformOptimalPrice_lowerEndpoint (b continuationValue : ℝ) :
    Monotone (fun a ↦ uniformOptimalPrice a b continuationValue) := by
  intro a₁ a₂ ha
  exact max_le_max ha le_rfl

/-- Raising the upper endpoint cannot lower the optimal posted price. -/
theorem monotone_uniformOptimalPrice_upperEndpoint (a continuationValue : ℝ) :
    Monotone (fun b ↦ uniformOptimalPrice a b continuationValue) := by
  intro b₁ b₂ hb
  have hmid : (b₁ + continuationValue) / 2 ≤ (b₂ + continuationValue) / 2 := by
    linarith
  exact max_le_max le_rfl (min_le_min hb hmid)

/-- Raising the seller's continuation value cannot lower the optimal price. -/
theorem monotone_uniformOptimalPrice_continuationValue (a b : ℝ) :
    Monotone (fun continuationValue ↦ uniformOptimalPrice a b continuationValue) := by
  intro r₁ r₂ hr
  have hmid : (b + r₁) / 2 ≤ (b + r₂) / 2 := by
    linarith
  exact max_le_max le_rfl (min_le_min le_rfl hmid)

/-- If both prices remain interior, changing the lower endpoint leaves the
optimal price unchanged. -/
theorem uniformOptimalPrice_lowerEndpoint_eq_of_interior
    (a₁ a₂ b continuationValue : ℝ)
    (h₁ : (b + continuationValue) / 2 ∈ Ioo a₁ b)
    (h₂ : (b + continuationValue) / 2 ∈ Ioo a₂ b) :
    uniformOptimalPrice a₂ b continuationValue =
      uniformOptimalPrice a₁ b continuationValue := by
  rw [uniformOptimalPrice_eq_peak a₂ b continuationValue ⟨h₂.1.le, h₂.2.le⟩,
    uniformOptimalPrice_eq_peak a₁ b continuationValue ⟨h₁.1.le, h₁.2.le⟩]

/-- While both optima remain interior, half of a change in the upper endpoint
passes through to the optimal price. -/
theorem uniformOptimalPrice_upperEndpoint_sub_of_interior
    (a b₁ b₂ continuationValue : ℝ)
    (h₁ : (b₁ + continuationValue) / 2 ∈ Ioo a b₁)
    (h₂ : (b₂ + continuationValue) / 2 ∈ Ioo a b₂) :
    uniformOptimalPrice a b₂ continuationValue -
        uniformOptimalPrice a b₁ continuationValue = (b₂ - b₁) / 2 := by
  rw [uniformOptimalPrice_eq_peak a b₂ continuationValue ⟨h₂.1.le, h₂.2.le⟩,
    uniformOptimalPrice_eq_peak a b₁ continuationValue ⟨h₁.1.le, h₁.2.le⟩]
  ring

/-- While both optima remain interior, half of a change in continuation
value passes through to the optimal price. -/
theorem uniformOptimalPrice_continuationValue_sub_of_interior
    (a b r₁ r₂ : ℝ)
    (h₁ : (b + r₁) / 2 ∈ Ioo a b)
    (h₂ : (b + r₂) / 2 ∈ Ioo a b) :
    uniformOptimalPrice a b r₂ - uniformOptimalPrice a b r₁ = (r₂ - r₁) / 2 := by
  rw [uniformOptimalPrice_eq_peak a b r₂ ⟨h₂.1.le, h₂.2.le⟩,
    uniformOptimalPrice_eq_peak a b r₁ ⟨h₁.1.le, h₁.2.le⟩]
  ring

end ValueDistribution

end
