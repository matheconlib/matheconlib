import MathEconLib.Auction

/-! # Normalized payment API through the auction umbrella -/

open MeasureTheory ProbabilityTheory
open MathEconLib MathEconLib.Mechanism.Auctions

namespace MathEconLib.Tests.PaymentUniqueness

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} [NeZero n]

-- The normalized formula does not require independence, density, or atomlessness.
example (A : Auction Ω n) [A.HasIdenticalTypes] [A.BIC] [A.HasZeroLowestTypeUtility]
    (halloc : IsUnitIntervalAllocation A.rules (fun o i => o i))
    (i : Fin n) {s : ℝ} (hs : s ∈ A.interval i) :
    A.p i s = s * A.q i s - ∫ ψ in A.lowestType..s, A.q i ψ :=
  A.payment_eq_allocation_integral halloc i hs

#print axioms Auction.payment_eq_allocation_integral
#print axioms Auction.payment_determined_by_allocation
#print axioms Auction.expected_payment_determined_by_allocation

end MathEconLib.Tests.PaymentUniqueness
