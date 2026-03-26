module

public import Auctionlib.Auction.SymmetricIPV

/-!
# Revenue Equivalence Theorem

Under BIC, IR, and efficient allocation in a symmetric IPV auction,
the expected total revenue equals `𝔼[S₂]` (expected second-highest type).

More generally, two BIC + IR mechanisms with the same `q` yield the same
expected revenue, without any efficiency assumption.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} [n.AtLeastTwo]

namespace Auction

variable (A : Auction Ω n) [A.IsSymmetricIPV]

/-- Under BIC, efficient allocation, and IR, the per-type expected payment
is uniquely determined by the common CDF. -/
lemma payment_formula_efficient
    (hx : A.rules.HasValidAllocation) (eff : A.Efficient)
    (hbic : A.BIC) (ir : A.IndividuallyRational)
    (i : Fin n) {s : ℝ} (hs : s ∈ A.interval i) :
    A.p i s = s * A.commonCDF s ^ (n - 1) -
      ∫ ψ in A.lowestType..s, A.commonCDF ψ ^ (n - 1) := by
  have hpf := A.payment_formula hx hbic i hs
  simp [A.q_eq_pow eff, ir i] at hpf ⊢
  linarith

/-- **Revenue Equivalence Theorem.**

Two BIC, IR symmetric IPV auctions with the same `q`, same type bounds,
and identically distributed types yield the same expected total revenue. -/
theorem revenue_equivalence
    {Ω₂ : Type} [MeasureSpace Ω₂] [IsProbabilityMeasure (ℙ : Measure Ω₂)]
    (A₂ : Auction Ω₂ n) [A₂.IsSymmetricIPV]
    (hx₁ : A.rules.HasValidAllocation) (hx₂ : A₂.rules.HasValidAllocation)
    (hq : ∀ i, A.q i = A₂.q i)
    (hmin : A.lowestType = A₂.lowestType)
    (hmax : A.highestType = A₂.highestType)
    (ident : ∀ i, IdentDistrib (A.θ i) (A₂.θ i) ℙ ℙ)
    (hbic₁ : A.BIC) (hbic₂ : A₂.BIC)
    (ir₁ : A.IndividuallyRational) (ir₂ : A₂.IndividuallyRational)
    (p_meas : ∀ i, Measurable (A₂.p i))
    (hint₁ : ∀ i, Integrable (fun ω => A.p i (A.θ i ω)) ℙ)
    (hint₂ : ∀ i, Integrable (fun ω => A₂.p i (A₂.θ i ω)) ℙ) :
    A.expectedRevenue = A₂.expectedRevenue := by
  simp only [expectedRevenue]
  rw [integral_finset_sum _ fun i _ => hint₁ i,
      integral_finset_sum _ fun i _ => hint₂ i]
  congr 1; ext i
  have hθmin : A.θmin i = A₂.θmin i := by simp [hmin]
  have hθmax : A.θmax i = A₂.θmax i := by simp [hmax]
  -- Use the ReducedForm payment_unique via the bridge
  have h_td1 := A.hasTypeDeviationIC_of_bic hx₁ hbic₁ i
  have h_td2 := A₂.hasTypeDeviationIC_of_bic hx₂ hbic₂ i
  have hU : (A.toReducedForm hx₁ i).U (A.θmin i) =
            (A₂.toReducedForm hx₂ i).U (A₂.θmin i) := by
    simp only [toReducedForm_U, A.θmin_eq_lowestType, A₂.θmin_eq_lowestType,
      ir₁ i, ir₂ i]
  have heq (ω) : A.p i (A.θ i ω) = A₂.p i (A.θ i ω) :=
    (A.toReducedForm hx₁ i).payment_unique (A₂.toReducedForm hx₂ i)
      hθmin hθmax (hq i) hU (A.θ i ω) (HasBoundedTypes.θ_in i ω)
  calc ∫ ω, A.p i (A.θ i ω) ∂ℙ
      = ∫ ω, A₂.p i (A.θ i ω) ∂ℙ := integral_congr_ae (ae_of_all _ heq)
    _ = ∫ ω, A₂.p i (A₂.θ i ω) ∂ℙ :=
        ((ident i).comp (p_meas i)).integral_eq

end Auction

end
