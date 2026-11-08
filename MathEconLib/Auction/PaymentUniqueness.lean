/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/

/- Migrated from Auctionlib/Auction/PaymentUniqueness.lean in PR #15, commit b51c018. -/
module

public import MathEconLib.Auction.Typeclasses

/-!
# Normalized payment uniqueness

Bayesian incentive compatibility determines interim payments from interim allocation and
lowest-type utility. Fixing that utility at zero gives the normalized formula below. Ordinary
individual rationality, which only bounds utility from below, does not fix this constant.

The pointwise results specialize `Auction.payment_formula` and `Auction.payment_equivalence`.
They explicitly require independent private values and IPV BIC, but not atomless types.
`HasIdenticalTypes` supplies the common bounds used by the normalization; the underlying
payment-equivalence theorem is more general.

`expected_payment_determined_by_allocation` transports integrability from the second auction
and proves equality of the two expected interim payments. This avoids interpreting a totalized
outer Bochner integral of a nonintegrable interim payment as an economic expectation.
The interim quantities themselves retain `Auction.p`'s convention for integration against
opponents' types. Integrability of the underlying realized payments remains a separate
model-specific obligation, as described in `Auction.Basic`.
-/

@[expose] public section

namespace MathEconLib.Auction

open MeasureTheory ProbabilityTheory Set
open MathEconLib.Mechanism.Auctions

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} [NeZero n]
variable (A : Auction Ω n) [A.HasIdenticalTypes]

/-- BIC and zero lowest-type utility give the normalized interim-payment identity. -/
lemma payment_eq_allocation_integral
    (halloc : IsUnitIntervalAllocation A.rules (fun o i => o i))
    [A.IsIPV] [Auction.IPV.BIC A] [A.HasZeroLowestTypeUtility]
    (i : Fin n) {s : ℝ} (hs : s ∈ A.interval i) :
    A.p i s = s * A.q i s - ∫ ψ in A.lowestType..s, A.q i ψ := by
  simpa only [A.θmin_eq_lowestType, HasZeroLowestTypeUtility.zeroLowestTypeUtility i,
    sub_zero] using A.payment_formula halloc i hs

/-- For a bidder `i` with the same interim allocation in two BIC auctions with common type bounds,
normalization to zero lowest-type utility gives identical interim payments throughout `i`'s type
interval. Only bidder `i`'s allocation is compared. -/
theorem payment_determined_by_allocation
    {Ω₂ : Type} [MeasureSpace Ω₂] [IsProbabilityMeasure (ℙ : Measure Ω₂)]
    (A₂ : Auction Ω₂ n) [A₂.HasIdenticalTypes]
    [A.IsIPV] [Auction.IPV.BIC A] [A₂.IsIPV] [Auction.IPV.BIC A₂]
    [A.HasZeroLowestTypeUtility] [A₂.HasZeroLowestTypeUtility] (i : Fin n)
    (halloc : IsUnitIntervalAllocation A.rules (fun o i => o i))
    (halloc₂ : IsUnitIntervalAllocation A₂.rules (fun o i => o i))
    (hq : A.q i = A₂.q i)
    (hmin : A.lowestType = A₂.lowestType)
    (hmax : A.highestType = A₂.highestType)
    {s : ℝ} (hs : s ∈ A.interval i) : A.p i s = A₂.p i s := by
  apply A.payment_equivalence A₂ halloc halloc₂ i i
    (by simpa only [θmin_eq_lowestType] using hmin)
    (by simpa only [θmax_eq_highestType] using hmax) hq _ hs
  simp only [θmin_eq_lowestType, HasZeroLowestTypeUtility.zeroLowestTypeUtility]

/-- For a bidder `i` whose types are identically distributed across the two auctions, normalized
pointwise payment uniqueness gives equality of expected interim payments. Integrability on the
second space is an assumption, and integrability on the first space is part of the conclusion.
Only the first auction needs bounded realized types: the pointwise comparison is evaluated at its
types before transporting their law. All hypotheses on allocations, laws, and payments concern
bidder `i` alone. -/
theorem expected_payment_determined_by_allocation
    {Ω₂ : Type} [MeasureSpace Ω₂] [IsProbabilityMeasure (ℙ : Measure Ω₂)]
    (A₂ : Auction Ω₂ n) [A₂.HasIdenticalTypes] [A.HasBoundedTypes]
    [A.IsIPV] [Auction.IPV.BIC A] [A₂.IsIPV] [Auction.IPV.BIC A₂]
    [A.HasZeroLowestTypeUtility] [A₂.HasZeroLowestTypeUtility] (i : Fin n)
    (halloc : IsUnitIntervalAllocation A.rules (fun o i => o i))
    (halloc₂ : IsUnitIntervalAllocation A₂.rules (fun o i => o i))
    (hq : A.q i = A₂.q i)
    (hmin : A.lowestType = A₂.lowestType)
    (hmax : A.highestType = A₂.highestType)
    (ident : IdentDistrib (A.θ i) (A₂.θ i) ℙ ℙ)
    (p_meas : Measurable (A₂.p i))
    (p_int₂ : Integrable (fun ω => A₂.p i (A₂.θ i ω)) ℙ) :
    Integrable (fun ω => A.p i (A.θ i ω)) ℙ ∧
      ∫ ω, A.p i (A.θ i ω) ∂ℙ = ∫ ω, A₂.p i (A₂.θ i ω) ∂ℙ := by
  have heq : (fun ω => A.p i (A.θ i ω)) = (fun ω => A₂.p i (A.θ i ω)) := by
    funext ω
    exact A.payment_determined_by_allocation A₂ i halloc halloc₂ hq hmin hmax
      (HasBoundedTypes.θ_in i ω)
  rw [heq]
  have hident := ident.comp p_meas
  exact ⟨hident.integrable_iff.mpr p_int₂, hident.integral_eq⟩

end MathEconLib.Auction

end
