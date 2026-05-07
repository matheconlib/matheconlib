module

public import Auctionlib.Auction.RevenueEquivalence

/-!
# Payment Uniqueness

Under Bayesian incentive compatibility (BIC) and individual rationality (IR)
in a symmetric independent-private-values auction, the interim payment rule
is fully determined by the interim allocation rule and the type support.

## Main results

* `Auction.payment_eq_allocation_integral` — the payment at type `s` equals
  `s · q(s) − ∫ₐˢ q(ψ) dψ`, depending only on the allocation rule `q`
  and the lowest type `a`.

* `Auction.payment_determined_by_allocation` — any two BIC + IR mechanisms
  that share `q` and the type bounds assign every bidder the same payment
  at every type in the support.

* `Auction.expected_payment_determined_by_allocation` — the expected payment
  of each bidder is likewise determined by `q`, the type bounds, and the
  common type distribution.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} [n.AtLeastTwo]

namespace Auction

variable (A : Auction Ω n) [A.IsSymmetricIPV]

/-! ### Explicit payment formula -/

/-- Under BIC and IR the interim payment at type `s` is pinned down by the
interim allocation rule:

  `p(s) = s · q(s) − ∫ₐˢ q(ψ) dψ`,

where `a = lowestType`.  The proof combines the envelope-theorem
representation of the indirect utility (via `payment_formula`) with the
IR normalisation `U(a) = 0`. -/
lemma payment_eq_allocation_integral
    [A.rules.HasValidAllocation]
    [A.BIC] [A.IndividuallyRational]
    (i : Fin n) {s : ℝ} (hs : s ∈ A.interval i) :
    A.p i s = s * A.q i s - ∫ ψ in A.lowestType..s, A.q i ψ := by
  have hpf := A.payment_formula i hs
  simp [IndividuallyRational.ir i] at hpf ⊢
  linarith

/-! ### Pointwise payment uniqueness -/

/-- **Payment Uniqueness.** Under BIC and IR, two symmetric IPV mechanisms
that share the same interim allocation rule `q` and type bounds must
charge each bidder identically at every type in the support.

This is the pointwise content of the Revenue Equivalence Theorem: once
the allocation rule is fixed, BIC and IR leave no freedom in the design
of payments. -/
theorem payment_determined_by_allocation
    {Ω₂ : Type} [MeasureSpace Ω₂] [IsProbabilityMeasure (ℙ : Measure Ω₂)]
    (A₂ : Auction Ω₂ n) [A₂.IsSymmetricIPV]
    [A.rules.HasValidAllocation] [A₂.rules.HasValidAllocation]
    (hq : ∀ i, A.q i = A₂.q i)
    (hmin : A.lowestType = A₂.lowestType)
    (hmax : A.highestType = A₂.highestType)
    [A.BIC] [A₂.BIC]
    [A.IndividuallyRational] [A₂.IndividuallyRational]
    (i : Fin n) {s : ℝ} (hs : s ∈ A.interval i) :
    A.p i s = A₂.p i s := by
  have hθmin : A.θmin i = A₂.θmin i := by simp [hmin]
  have hθmax : A.θmax i = A₂.θmax i := by simp [hmax]
  have hU : (A.toBidderProblem id i).U (A.θmin i) =
            (A₂.toBidderProblem id i).U (A₂.θmin i) := by
    simp only [toBidderProblem_U, A.θmin_eq_lowestType, A₂.θmin_eq_lowestType,
      IndividuallyRational.ir i]
  exact (A.toBidderProblem id i).payment_unique (A₂.toBidderProblem id i)
    hθmin hθmax (hq i) hU s hs

/-! ### Expected-payment uniqueness -/

/-- The expected payment of each bidder depends only on the allocation rule,
the type bounds, and the common type distribution.  This follows from the
pointwise result by integrating over types and appealing to the
identical-distribution hypothesis. -/
theorem expected_payment_determined_by_allocation
    {Ω₂ : Type} [MeasureSpace Ω₂] [IsProbabilityMeasure (ℙ : Measure Ω₂)]
    (A₂ : Auction Ω₂ n) [A₂.IsSymmetricIPV]
    [A.rules.HasValidAllocation] [A₂.rules.HasValidAllocation]
    (hq : ∀ i, A.q i = A₂.q i)
    (hmin : A.lowestType = A₂.lowestType)
    (hmax : A.highestType = A₂.highestType)
    (ident : ∀ i, IdentDistrib (A.θ i) (A₂.θ i) ℙ ℙ)
    [A.BIC] [A₂.BIC]
    [A.IndividuallyRational] [A₂.IndividuallyRational]
    (p_meas : ∀ i, Measurable (A₂.p i))
    (i : Fin n) :
    ∫ ω, A.p i (A.θ i ω) ∂ℙ = ∫ ω, A₂.p i (A₂.θ i ω) ∂ℙ := by
  have heq : ∀ ω, A.p i (A.θ i ω) = A₂.p i (A.θ i ω) := fun ω =>
    A.payment_determined_by_allocation A₂ hq hmin hmax i
      (HasBoundedTypes.θ_in i ω)
  calc ∫ ω, A.p i (A.θ i ω) ∂ℙ
      = ∫ ω, A₂.p i (A.θ i ω) ∂ℙ := integral_congr_ae (ae_of_all _ heq)
    _ = ∫ ω, A₂.p i (A₂.θ i ω) ∂ℙ :=
        ((ident i).comp (p_meas i)).integral_eq

end Auction

end
