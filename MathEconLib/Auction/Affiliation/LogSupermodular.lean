module

public import MathEconLib.Auction.Affiliation.Basic
public import Mathlib

/-! # Affiliation as log-supermodularity

This file records the standard logarithmic reformulation of the affiliation
inequality: for a strictly positive density
`f : (Fin n → ℝ) → ℝ`, affiliation is equivalent to *log-supermodularity*
of `f` with respect to the pointwise lattice structure on `Fin n → ℝ`,

`log (f x) + log (f y) ≤ log (f (x ⊔ y)) + log (f (x ⊓ y))`.

For strictly positive densities, affiliation is exactly the MTP₂
(multivariate totally positive of order 2) / log-supermodularity condition:
`log f` is supermodular, so "raising some coordinates never decreases the
marginal impact of raising others". The equivalence is a direct consequence
of the monotonicity of `Real.log` on positive reals (`Real.log_le_log_iff`)
together with `Real.log_mul`.
-/

namespace MathEconLib

@[expose] public section

namespace Auction.Affiliation

/-- **Logarithmic characterization of affiliation** (MTP₂ / log-supermodularity). For a strictly
positive density `f`, affiliation is equivalent to supermodularity of `log ∘ f`
with respect to the pointwise lattice operations on `Fin n → ℝ`:

`log (f x) + log (f y) ≤ log (f (x ⊔ y)) + log (f (x ⊓ y))` for all `x`, `y`.

The multiplicative inequality of `Affiliated` transfers to the additive one via
`Real.log_mul` and the strict monotonicity of `Real.log` on `(0, ∞)`
(`Real.log_le_log_iff`); positivity of `f` is what licenses both steps. -/
theorem affiliated_iff_logSupermodular {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ∀ x, 0 < f x) :
    Affiliated f ↔ ∀ x y : Fin n → ℝ,
      Real.log (f x) + Real.log (f y) ≤
        Real.log (f (x ⊔ y)) + Real.log (f (x ⊓ y)) := by
  have key : ∀ x y : Fin n → ℝ,
      (Real.log (f x) + Real.log (f y) ≤
          Real.log (f (x ⊔ y)) + Real.log (f (x ⊓ y))) ↔
        f x * f y ≤ f (x ⊔ y) * f (x ⊓ y) := by
    intro x y
    rw [← Real.log_mul (hf x).ne' (hf y).ne', ← Real.log_mul (hf _).ne' (hf _).ne',
      Real.log_le_log_iff (mul_pos (hf x) (hf y)) (mul_pos (hf _) (hf _))]
  constructor
  · intro h x y
    exact (key x y).mpr (h x y)
  · intro h x y
    exact (key x y).mp (h x y)

end Auction.Affiliation

end

end MathEconLib
