/-
Copyright (c) 2026 Ruiz Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiz Chen
-/
module

public import MathEconLib.Auction.AllPurchase.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Uniform distribution closed form for the all-pay bid (§9.6.3)

When types are uniform on `[0, v̄]`, the common CDF is `F(v) = v / v̄`, and the
standard all-pay bid function collapses to the closed form

`b^{AP}(v) = (n − 1)/n · vⁿ / v̄ⁿ⁻¹`.

This is the lead-in identity of §9.6.3 on which the uniform equilibrium
(Proposition 9.9) and its moments are built.  The CDF behaviour `F(v) = v/v̄`
on `[0, v̄]` is taken as a hypothesis, which characterises the uniform law.
-/

namespace MathEconLib

@[expose] public section

open MeasureTheory ProbabilityTheory Set intervalIntegral

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} [NeZero n] [n.AtLeastTwo]

namespace Auction

variable (A : Auction Ω n) [HasIdenticalTypes A]

/-- **Uniform all-pay bid (§9.6.3).** If the common CDF is `F(v) = v / v̄` on
`[0, v̄]` and the lowest type is `0`, then on `[0, v̄]`
`b^{AP}(v) = (n − 1)/n · vⁿ / v̄ⁿ⁻¹`. -/
theorem allPayBid_uniform
    (vbar : ℝ) (hvbar : 0 < vbar)
    (hlow : A.lowestType = 0)
    (hcdf : ∀ t ∈ Icc (0 : ℝ) vbar, A.commonCDF t = t / vbar)
    (v : ℝ) (hv : v ∈ Icc (0 : ℝ) vbar) :
    A.allPayBid v = (↑n - 1) / ↑n * v ^ n / vbar ^ (n - 1) := by
  have hn1 : 1 ≤ n := by have := Nat.AtLeastTwo.prop (n := n); omega
  have hvbar0 : vbar ≠ 0 := ne_of_gt hvbar
  have hv0 : 0 ≤ v := hv.1
  have hvle : v ≤ vbar := hv.2
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hvp : (vbar : ℝ) ^ (n - 1) ≠ 0 := pow_ne_zero _ hvbar0
  have hvn : v ^ n = v * v ^ (n - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hn1]
    rw [pow_succ']
  -- rewrite the integrand to the uniform form on `[0, v]`
  have hcong : (∫ t in (0 : ℝ)..v, A.commonCDF t ^ (n - 1))
      = ∫ t in (0 : ℝ)..v, (t / vbar) ^ (n - 1) := by
    apply integral_congr
    intro t ht
    rw [uIcc_of_le hv0] at ht
    show A.commonCDF t ^ (n - 1) = (t / vbar) ^ (n - 1)
    rw [hcdf t ⟨ht.1, le_trans ht.2 hvle⟩]
  unfold Auction.allPayBid
  rw [hlow, hcdf v hv, hcong]
  simp_rw [div_pow, div_eq_mul_inv]
  rw [intervalIntegral.integral_mul_const, integral_pow]
  rw [Nat.sub_add_cancel hn1, zero_pow (show n ≠ 0 by omega), sub_zero]
  have hden : (↑(n - 1) : ℝ) + 1 = ↑n := by rw [Nat.cast_sub hn1]; ring
  rw [hden, hvn]
  field_simp

end Auction

end

end MathEconLib
