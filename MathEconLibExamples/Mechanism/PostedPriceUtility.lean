/-
Copyright (c) 2026 Daniel Lyng, Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng, Bo Cowgill
-/
module

public import MathEconLib.Mechanism.Core.UtilityCompatibility
import Mathlib.Analysis.Convex.Mul
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.MeasureTheory.Measure.DiracProba

/-!
# Posted pricing with supplied wealth utility

The price-one mechanism and its zero-or-two buyer valuations are shared with the existing
mechanism regression development, preserving Daniel Lyng's original definitions and attribution.
Initial wealth is two. The supplied utility `w / (1 + w)` is evaluated at final wealth, which is
positive at every feasible type/report pair. Purchasing gives utilities `3/4` and `1/2` for high
and low types; abstention gives the reservation utility `2/3`.
-/

@[expose] public noncomputable section

open MathEconLib.GameTheory MathEconLib.Mechanism MeasureTheory
open scoped ENNReal

namespace MathEconLibExamples.Mechanism.PostedPriceUtility

/-- One buyer receives the good and pays one exactly when reporting high. -/
@[simps] def mechanism : MathEconLib.Mechanism Unit (fun _ ↦ Bool) Bool where
  outcome r := r ()
  transfer _ r := if r () then -1 else 0

/-- The buyer values the good at two when high and at zero when low. -/
@[simps!] def environment : QuasilinearEnvironment Unit (fun _ ↦ Bool) Bool :=
  QuasilinearEnvironment.ofPrivate fun _ high receives ↦
    if receives then if high then 2 else 0 else 0

/-- Increasing concave utility on the feasible positive-wealth domain. -/
def wealthUtility (w : ℝ) : ℝ := w / (1 + w)

/-- On positive wealth the utility is one minus the reciprocal of one plus wealth. -/
theorem wealthUtility_eq_one_sub_inv {w : ℝ} (hw : 0 < w) :
    wealthUtility w = 1 - (1 + w)⁻¹ := by
  field_simp [ne_of_gt (add_pos zero_lt_one hw)]
  simp [wealthUtility, ne_of_gt (add_pos zero_lt_one hw)]

/-- The supplied wealth utility is concave on the feasible positive-wealth domain. -/
theorem concaveOn_wealthUtility : ConcaveOn ℝ (Set.Ioi 0) wealthUtility := by
  have hinv : ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun w : ℝ ↦ w⁻¹) := by
    simpa using (convexOn_zpow (𝕜 := ℝ) (-1))
  have hshift := hinv.comp_affineMap (AffineEquiv.constVAdd ℝ ℝ (1 : ℝ)).toAffineMap
  have hpositive : ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun w : ℝ ↦ (1 + w)⁻¹) :=
    hshift.subset (fun w hw ↦ show 0 < 1 + w from add_pos zero_lt_one hw) (convex_Ioi _)
  exact ((concaveOn_const (1 : ℝ) (convex_Ioi 0)).sub hpositive).congr
    (fun w hw ↦ (wealthUtility_eq_one_sub_inv hw).symm)

/-- More positive wealth strictly increases supplied utility. -/
theorem strictMonoOn_wealthUtility : StrictMonoOn wealthUtility (Set.Ioi 0) :=
  fun x hx y hy hxy ↦
    (div_lt_div_iff₀ (add_pos zero_lt_one hx) (add_pos zero_lt_one hy)).2 (by nlinarith)

/-- Supply nonlinear wealth utility through the own-transfer adapter. -/
def utility : Unit → (Unit → Bool) → (Bool × (Unit → ℝ)) → ℝ :=
  MathEconLib.Mechanism.utilityFromOwnTransfer
    (fun i θ o τ ↦ wealthUtility (2 + environment.value i θ o + τ))

/-- Every type/report pair of this mechanism leaves strictly positive final wealth. -/
theorem finalWealth_pos (θ a : Unit → Bool) :
    0 < 2 + environment.value () θ (mechanism.outcome a) + mechanism.transfer () a := by
  cases hθ : θ () <;> cases ha : a () <;>
    norm_num [environment, mechanism, QuasilinearEnvironment.ofPrivate, hθ, ha]

/-- A high buyer's purchase gives wealth three and utility three quarters. -/
theorem payoff_high_purchase :
    (mechanism.toStrategicGame utility (fun _ ↦ true)).payoff () (fun _ ↦ true) = 3 / 4 := by
  norm_num [utility, wealthUtility, mechanism, environment, QuasilinearEnvironment.ofPrivate]

/-- A low buyer's purchase gives wealth one and utility one half. -/
theorem payoff_low_purchase :
    (mechanism.toStrategicGame utility (fun _ ↦ false)).payoff () (fun _ ↦ true) = 1 / 2 := by
  norm_num [utility, wealthUtility, mechanism, environment, QuasilinearEnvironment.ofPrivate]

/-- Abstention leaves initial wealth two, for either true type. -/
theorem payoff_abstain (θ : Unit → Bool) :
    (mechanism.toStrategicGame utility θ).payoff () (fun _ ↦ false) = 2 / 3 := by
  norm_num [utility, wealthUtility, mechanism, environment, QuasilinearEnvironment.ofPrivate]

/-- The same nonlinear evaluator weakly prefers truthful play to each alternative report. -/
theorem truthful_payoff_ge (θ a : Unit → Bool) :
    (mechanism.toStrategicGame utility θ).payoff () a ≤
      (mechanism.toStrategicGame utility θ).payoff () θ := by
  cases hθ : θ () <;> cases ha : a () <;>
    norm_num [utility, wealthUtility, mechanism, environment, QuasilinearEnvironment.ofPrivate,
      hθ, ha]

/-- Truthful participation beats the reservation utility of initial wealth two. -/
theorem truthful_participation (θ : Unit → Bool) :
    wealthUtility 2 ≤ (mechanism.toStrategicGame utility θ).payoff () θ := by
  cases hθ : θ () <;>
    norm_num [utility, wealthUtility, mechanism, environment, QuasilinearEnvironment.ofPrivate, hθ]

/-- Fixing true types in the Bayesian view recovers this supplied-utility strategic game. -/
theorem fixedType_agreement (θ : Unit → Bool) :
    (mechanism.toBayesianGame utility).strategicGameAt θ = mechanism.toStrategicGame utility θ :=
  mechanism.toBayesianGame_strategicGameAt utility θ

private theorem half_mass :
    ENNReal.ofReal (1 / 2 : ℝ) + ENNReal.ofReal (1 / 2 : ℝ) = 1 := by
  rw [← ENNReal.ofReal_add (by norm_num : 0 ≤ (1 / 2 : ℝ))
    (by norm_num : 0 ≤ (1 / 2 : ℝ))]
  norm_num

/-- Equal chances of final wealth one and three form a genuine probability measure. -/
def wealthLottery : ProbabilityMeasure ℝ :=
  ⟨ENNReal.ofReal (1 / 2 : ℝ) • Measure.dirac (1 : ℝ) +
    ENNReal.ofReal (1 / 2 : ℝ) • Measure.dirac (3 : ℝ),
    ⟨by simpa [Measure.add_apply, Measure.smul_apply] using half_mass⟩⟩

/-- The existing expected-outcome evaluator averages the supplied wealth utility. -/
def wealthPayoffs : PayoffStructure Unit ℝ ℝ where
  payoff _ w := wealthUtility w

/-- Both lottery outcomes lie in the feasible positive-wealth domain. -/
theorem wealthLottery_positive : (wealthLottery : Measure ℝ) (Set.Ioi 0) = 1 := by
  simpa [wealthLottery, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply',
    measurableSet_Ioi] using half_mass

/-- The supplied utility is integrable at every Dirac outcome. -/
theorem wealthUtility_integrable_dirac (w : ℝ) :
    Integrable wealthUtility (Measure.dirac w) :=
  integrable_dirac (by simp)

/-- Utility is evaluated before averaging, giving five eighths at the equal-chance lottery. -/
theorem expected_payoff : wealthPayoffs.expected.payoff () wealthLottery = 5 / 8 := by
  change ∫ w, wealthUtility w ∂(ENNReal.ofReal (1 / 2 : ℝ) • Measure.dirac (1 : ℝ) +
    ENNReal.ofReal (1 / 2 : ℝ) • Measure.dirac (3 : ℝ)) = 5 / 8
  rw [integral_add_measure
    ((wealthUtility_integrable_dirac 1).smul_measure ENNReal.ofReal_ne_top)
    ((wealthUtility_integrable_dirac 3).smul_measure ENNReal.ofReal_ne_top)]
  norm_num [integral_smul_measure, wealthUtility]

/-- The lottery has mean wealth two. -/
theorem mean_wealth : ∫ w : ℝ, w ∂(wealthLottery : Measure ℝ) = 2 := by
  change ∫ w : ℝ, w ∂(ENNReal.ofReal (1 / 2 : ℝ) • Measure.dirac (1 : ℝ) +
    ENNReal.ofReal (1 / 2 : ℝ) • Measure.dirac (3 : ℝ)) = 2
  rw [integral_add_measure
    ((integrable_dirac (by simp) : Integrable (fun w : ℝ ↦ w) (Measure.dirac 1)).smul_measure
      ENNReal.ofReal_ne_top)
    ((integrable_dirac (by simp) : Integrable (fun w : ℝ ↦ w) (Measure.dirac 3)).smul_measure
      ENNReal.ofReal_ne_top)]
  norm_num [integral_smul_measure]

/-- Expected utility is strictly below utility at mean wealth; utility must be evaluated first. -/
theorem expected_payoff_lt_utility_mean :
    wealthPayoffs.expected.payoff () wealthLottery <
      wealthUtility (∫ w : ℝ, w ∂(wealthLottery : Measure ℝ)) := by
  rw [expected_payoff, mean_wealth]
  norm_num [wealthUtility]

/-- The low-type purchase fails the reservation comparison under the same supplied utility. -/
theorem low_purchase_below_reservation :
    (mechanism.toStrategicGame utility (fun _ ↦ false)).payoff () (fun _ ↦ true) <
      wealthUtility 2 := by
  rw [payoff_low_purchase]
  norm_num [wealthUtility]

end MathEconLibExamples.Mechanism.PostedPriceUtility

end
