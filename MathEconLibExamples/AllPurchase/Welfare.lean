module

public import MathEconLibExamples.AllPurchase.Basic
public import MathEconLib.Auction.AllPurchase

/-!
# A concrete welfare decomposition

The 2 buyers each purchase `1/3` edition at price `2`, with scarcity value `3 - B` and production
cost `0`. The editions-only Cournot quantity is `2/3`; its welfare is `14/9`, while first-best welfare
is `9/4`. This example constructs the auction, proves square integrability, applies the economic
decomposition, and certifies the Cournot profile's best-response property. The deterministic
purchase profile is an editions-only equilibrium; no claim of contest equilibrium is made.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace MathEconLib.Examples.AllPurchase.Welfare

local instance : MeasureSpace Unit where
  toMeasurableSpace := ⊤
  volume := Measure.dirac ()

local instance : IsProbabilityMeasure (ℙ : Measure Unit) := by
  change IsProbabilityMeasure (Measure.dirac () : Measure Unit)
  infer_instance

/-- Both prize values are `0` in the deterministic state. -/
def model : LinearScarcityAuction Unit 2 :=
  auction (fun _ _ => 0) (fun _ => measurable_const)

/-- Each buyer purchases the symmetric editions-only Cournot amount. -/
def purchase : ℝ → ℝ := fun _ => 1 / 3

theorem aggregate_purchase : model.toAuction.aggregateBid purchase = fun _ => (2 : ℝ) / 3 := by
  funext ω
  norm_num [Auction.aggregateBid, purchase, Fin.sum_univ_two]

theorem aggregate_memLp : MemLp (model.toAuction.aggregateBid purchase) 2 ℙ := by
  rw [aggregate_purchase]
  exact memLp_const _

theorem cournot_quantity : model.cournotQuantityLinear = (2 : ℝ) / 3 := by
  change (2 : ℝ) * (3 - 2) / (1 * (2 + 1)) = 2 / 3
  norm_num

theorem cournot_profile_best_response :
    ∀ x : ℝ, 0 ≤ x → x * (3 - (x + 1 / 3) - 2) ≤ (1 : ℝ) / 9 := by
  intro x hx
  have hp : model.spec.price ≤ model.φ_bar := by change (2 : ℝ) ≤ 3; norm_num
  have h := (model.cournotPurchaseLinear_best_response hp).2 x hx
  have hq : model.cournotPurchaseLinear = (1 : ℝ) / 3 := by
    change (3 - 2 : ℝ) / (1 * (2 + 1)) = 1 / 3
    norm_num
  rw [hq] at h
  change x * (3 - (x + (2 - 1) * (1 / 3)) - 2) ≤
    (1 / 3) * (3 - 2 * (1 / 3) - 2) at h
  norm_num at h
  exact h

theorem expected_welfare : model.bundledEditionWelfare purchase 0 = (14 : ℝ) / 9 := by
  rw [model.bundledEditionWelfare_eq_integral purchase 0 aggregate_memLp]
  simp_rw [aggregate_purchase]
  change (∫ _ : Unit, (2 : ℝ) / 3 * (3 - 2 / 3) - 0 * (2 / 3)) = 14 / 9
  norm_num

/-- The named economic theorem yields the welfare gap `25/36`, comprising Cournot loss and contest loss `0` in this deterministic benchmark. -/
theorem welfare_gap :
    MathEconLib.AllPurchase.firstBestEditionSurplus model.φ_bar 0 model.α_coeff -
        𝔼[fun ω => model.toAuction.aggregateBid purchase ω *
          model.spec.φ (model.toAuction.aggregateBid purchase ω)] =
      (25 : ℝ) / 36 := by
  have h := model.welfare_decomposition purchase 0 aggregate_memLp
  simp only [zero_mul, sub_zero] at h
  rw [h, cournot_quantity, expected_welfare]
  norm_num [MathEconLib.AllPurchase.cournotLoss, MathEconLib.AllPurchase.contestLoss,
    MathEconLib.AllPurchase.firstBestEditionSurplus, MathEconLib.AllPurchase.editionWelfare,
    model, auction]

/-- The variance theorem applies to the actual aggregate quantity and gives penalty `0`. -/
theorem variance_penalty :
    MathEconLib.AllPurchase.editionWelfare model.φ_bar 0 model.α_coeff
        (model.toAuction.expectedAggregateBid purchase) -
      model.bundledEditionWelfare purchase 0 = 0 := by
  rw [model.editionWelfare_mean_sub_bundled_eq_variance purchase 0 aggregate_memLp,
    aggregate_purchase]
  rw [variance_eq_integral aemeasurable_const]
  simp

end MathEconLib.Examples.AllPurchase.Welfare

end

end
