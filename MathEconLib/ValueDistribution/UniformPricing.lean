module

public import MathEconLib.ValueDistribution.PostedPrice
public import MathEconLib.ValueDistribution.Uniform
public import MathEconLib.ValueDistribution.VirtualValue

import MathEconLib.ValueDistribution.PostedPriceFirstOrder
import MathEconLib.ValueDistribution.PostedPriceOptimality
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Posted Pricing with Uniform Buyer Values

For a buyer whose value is uniform on `[a, b]`, this file specializes the
shared seller-profit and pricing results. The maximization is over posted prices in
`[a, b]`; prices above `b` are not included because they all yield no sale.

The candidate price is the unconstrained quadratic optimum `(b + r) / 2`
projected onto the feasible interval. Here `r` is continuation value, and
the unconditional acquisition cost does not affect the maximizing price.

The uniform virtual-surplus weight supplies the sign conditions for
`PostedPriceOptimality`, including at both boundaries. At an interior optimum,
`PostedPriceFirstOrder` gives virtual value equal to continuation value. A
private quadratic profit-gap identity establishes uniqueness on `[a, b]`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open SingleParameterProblem

namespace ValueDistribution

/-- On the uniform support, the virtual-surplus weight for the constant
density representative is `(2 * value - b) / (b - a)`. -/
theorem uniformInterval_virtualSurplusWeight (a b : ℝ) (hab : a < b)
    (value : ℝ) (hvalue : value ∈ Icc a b) :
    (uniformInterval a b hab).virtualSurplusWeight
        (fun _ : ℝ ↦ 1 / (b - a)) value =
      (2 * value - b) / (b - a) := by
  rw [virtualSurplusWeight, uniformInterval_probAtLeast a b hab value hvalue]
  ring

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

/-- The projected price separates the nonpositive and nonnegative net
virtual surplus. At a support boundary, one comparison interval is a
Lebesgue-null singleton, so the corresponding sign condition is automatic. -/
private theorem uniformInterval_netVirtualSurplus_sign
    (a b : ℝ) (hab : a < b) (continuationValue : ℝ) :
    (∀ᵐ value ∂volume.restrict (Icc a (uniformOptimalPrice a b continuationValue)),
      (uniformInterval a b hab).virtualSurplusWeight
          (fun _ : ℝ ↦ 1 / (b - a)) value -
        continuationValue * (1 / (b - a)) ≤ 0) ∧
    (∀ᵐ value ∂volume.restrict (Icc (uniformOptimalPrice a b continuationValue) b),
      0 ≤ (uniformInterval a b hab).virtualSurplusWeight
          (fun _ : ℝ ↦ 1 / (b - a)) value -
        continuationValue * (1 / (b - a))) := by
  constructor
  · by_cases hleft : (b + continuationValue) / 2 ≤ a
    · simp [uniformOptimalPrice_eq_left a b continuationValue hleft]
    · have hcutoff_le_peak :
          uniformOptimalPrice a b continuationValue ≤ (b + continuationValue) / 2 :=
        max_le (le_of_lt (lt_of_not_ge hleft)) (min_le_right _ _)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with value hvalue
      rw [uniformInterval_virtualSurplusWeight a b hab value
        ⟨hvalue.1, hvalue.2.trans (uniformOptimalPrice_mem_Icc a b continuationValue hab).2⟩]
      calc
        (2 * value - b) / (b - a) - continuationValue * (1 / (b - a)) =
            (2 * value - b - continuationValue) / (b - a) := by ring
        _ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith [hvalue.2])
          (sub_nonneg.mpr hab.le)
  · by_cases hright : b ≤ (b + continuationValue) / 2
    · simp [uniformOptimalPrice_eq_right a b continuationValue hab hright]
    · have hpeak_le_cutoff :
          (b + continuationValue) / 2 ≤ uniformOptimalPrice a b continuationValue :=
        (le_min (le_of_lt (lt_of_not_ge hright)) le_rfl).trans (le_max_right _ _)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with value hvalue
      rw [uniformInterval_virtualSurplusWeight a b hab value
        ⟨(uniformOptimalPrice_mem_Icc a b continuationValue hab).1.trans hvalue.1, hvalue.2⟩]
      calc
        0 ≤ (2 * value - b - continuationValue) / (b - a) :=
          div_nonneg (by linarith [hvalue.1]) (sub_nonneg.mpr hab.le)
        _ = (2 * value - b) / (b - a) - continuationValue * (1 / (b - a)) := by ring

/-- A feasible price with zero quadratic margin gap equals the projected peak. -/
private theorem uniform_price_eq_of_margin_gap_eq_zero
    (a b continuationValue price : ℝ) (hab : a < b) (hprice : price ∈ Icc a b)
    (hzero : (uniformOptimalPrice a b continuationValue - price) *
      (b + continuationValue - uniformOptimalPrice a b continuationValue - price) = 0) :
    price = uniformOptimalPrice a b continuationValue := by
  rcases mul_eq_zero.mp hzero with hsame | hreflected
  · exact (sub_eq_zero.mp hsame).symm
  · by_cases hlow : (b + continuationValue) / 2 ≤ a
    · rw [uniformOptimalPrice_eq_left a b continuationValue hlow] at hreflected ⊢
      linarith [hprice.1]
    · by_cases hhigh : b ≤ (b + continuationValue) / 2
      · rw [uniformOptimalPrice_eq_right a b continuationValue hab hhigh] at hreflected ⊢
        linarith [hprice.2]
      · have hpeak : (b + continuationValue) / 2 ∈ Icc a b :=
          ⟨le_of_lt (lt_of_not_ge hlow), le_of_lt (lt_of_not_ge hhigh)⟩
        rw [uniformOptimalPrice_eq_peak a b continuationValue hpeak] at hreflected ⊢
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
  obtain ⟨hbelow, habove⟩ := uniformInterval_netVirtualSurplus_sign a b hab continuationValue
  exact isMaxOn_sellerProfit_postedPriceProblem_of_netVirtualSurplus_sign
    (uniformInterval a b hab) a b (uniformOptimalPrice a b continuationValue)
    (fun _ : ℝ ↦ 1 / (b - a)) continuationValue acquisitionCost
    (uniformOptimalPrice_mem_Icc a b continuationValue hab)
    (uniformInterval_supported a b hab) (uniformInterval_absolutelyContinuous a b hab)
    (uniformInterval_density a b hab) hbelow habove

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
  exact uniform_price_eq_of_margin_gap_eq_zero a b continuationValue price hab hprice
    hnumerator

/-- At an interior uniform optimal price, virtual value for the constant
density representative equals the seller's continuation value. -/
theorem uniformInterval_virtualValue_eq_continuationValue_of_interior
    (a b : ℝ) (hab : a < b) (continuationValue : ℝ)
    (hpeak : (b + continuationValue) / 2 ∈ Ioo a b) :
    (uniformInterval a b hab).virtualValue
        (fun _ : ℝ ↦ 1 / (b - a)) ((b + continuationValue) / 2) =
      continuationValue := by
  have hmax := isMaxOn_sellerProfit_uniformInterval a b hab continuationValue 0
  rw [uniformOptimalPrice_eq_peak a b continuationValue ⟨hpeak.1.le, hpeak.2.le⟩] at hmax
  exact virtualValue_eq_continuationValue_of_isLocalMaxOn_sellerProfit_postedPriceProblem
    (uniformInterval a b hab) a b (fun _ : ℝ ↦ 1 / (b - a))
    continuationValue 0 ((b + continuationValue) / 2) hpeak
    (uniformInterval_hasDerivAt_cdf a b hab _ hpeak) hmax.localize
    (by simp [ne_of_gt (sub_pos.mpr hab)])

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
