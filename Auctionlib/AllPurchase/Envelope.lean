module

public import Auctionlib.AllPurchase.Monotonicity

/-!
# All-Purchase Auction — Envelope Condition (Lemma 6.3)

In any symmetric pure-strategy BNE, the equilibrium utility satisfies:
- `U` is 1-Lipschitz on `[a, b]`,
- `U'(v) = q(v)` a.e. on `[a, b]`,
- `U(v) = U(a) + ∫ₐᵛ q(ψ) dψ` for all `v ∈ [a, b]`.

These are direct consequences of the Envelope Theorem (`EnvelopeSetUpMathsCore`)
applied via the coercion `AllPurchaseCore.toEnvelopeSetUpMathsCore`.

## Main results

- `AllPurchaseCore.lipschitz`: `U` is 1-Lipschitz on `[a, b]`.
- `AllPurchaseCore.aeDifferentiable`: `U'(v) = q(v)` a.e. on `[a, b]`.
- `AllPurchaseCore.integral_rep`: `U(v) = U(a) + ∫ₐᵛ q(ψ) dψ` (Lemma 6.3).
- `AllPurchaseCore.U_nonneg`: `U(v) ≥ 0` on `[a, b]` given `U(a) ≥ 0`.
-/

@[expose] public section

section envelope

open MeasureTheory

namespace AllPurchaseCore

variable (ε : AllPurchaseCore)

/-- `U` is 1-Lipschitz on `[a, b]`.
Direct from `EnvelopeSetUpMathsCore.lipschitz`. -/
lemma lipschitz : LipschitzOnWith 1 ε.U (Set.Icc ε.a ε.b) :=
  ε.toEnvelopeSetUpMathsCore.lipschitz

/-- `U'(v) = q(v)` for a.e. `v ∈ [a, b]`.
Direct from `EnvelopeSetUpMathsCore.aeDifferentiable`. -/
lemma aeDifferentiable :
    ∀ᵐ s ∂volume.restrict (Set.Icc ε.a ε.b), HasDerivAt ε.U (ε.q s) s :=
  ε.toEnvelopeSetUpMathsCore.aeDifferentiable

/-- **Lemma 6.3 — Envelope Condition.**
`U(v) = U(a) + ∫ₐᵛ q(ψ) dψ` for all `v ∈ [a, b]`.
Direct from `EnvelopeSetUpMathsCore.integral_rep`. -/
lemma integral_rep (v : ℝ) (hv : v ∈ Set.Icc ε.a ε.b) :
    ε.U v = ε.U ε.a + ∫ ψ in ε.a..v, ε.q ψ :=
  ε.toEnvelopeSetUpMathsCore.integral_rep v hv

/-- Non-negativity of equilibrium utility on `[a, b]`.

If the lowest type has non-negative utility (`U(a) ≥ 0`, which holds economically
because the lowest type can choose `b = 0` and get payoff `0`), then every type
has non-negative utility, since `q ≥ 0` implies the integral is non-negative. -/
lemma U_nonneg (hUa : 0 ≤ ε.U ε.a) (v : ℝ) (hv : v ∈ Set.Icc ε.a ε.b) :
    0 ≤ ε.U v := by
  rw [ε.integral_rep v hv]
  have hq_nn : ∀ ψ ∈ Set.Icc ε.a v, 0 ≤ ε.q ψ :=
    fun ψ hψ => (ε.q_range ψ).1
  exact add_nonneg hUa (intervalIntegral.integral_nonneg hv.1 hq_nn)

end AllPurchaseCore

end envelope

end
