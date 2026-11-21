/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLib.RevealedPreference.Equilibrium

/-!
# A finite ordinal linear characterization of revealed equilibrium

For each consumer, assign every observation an integer rank between zero and
the number of observations. A higher-ranked bundle must cost strictly more
than income at a lower-ranked observation. An equally ranked bundle must cost
at least income. Together with nonnegativity, budget exhaustion and clearing,
these are linear weak and strict inequalities in the latent consumptions.

There are finitely many rank profiles. Their union is exactly the set of
GARP-compatible joint allocations. Thus this characterization removes Afriat's
continuous utility levels and multipliers and their bilinear terms. This module
also proves necessary observable dual restrictions. The companion module
`EquilibriumElimination` removes the remaining latent consumptions by
Fourier–Motzkin elimination and proves an exact observable axiom. Sufficiency
of this module's separate dual formulation is not asserted. Ties and repeated
choices are allowed, as are empty observation sets.
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace MathEconLib.RevealedPreference.Equilibrium

variable {L : ℕ} {I T : Type*}

/-- An explicit bound on the number of linear systems in the disjunction.
Different profiles can encode the same weak ordering, so this is redundant. -/
theorem card_rankProfiles [Fintype I] [Fintype T] [DecidableEq I] [DecidableEq T] :
    Fintype.card (I → ObservationRanks T) =
      ((Fintype.card T + 1) ^ Fintype.card T) ^ Fintype.card I := by
  simp [ObservationRanks]

/-- The linear system attached to a fixed profile of ordinal ranks. All its
coefficients are observed prices, incomes, resources, or fixed integers. -/
def OrdinalAllocationFeasible [Fintype I] [Fintype T] (D : MarketData L I T)
    (r : I → ObservationRanks T) (x : I → T → Bundle L) : Prop :=
  AllocationFeasible D x ∧
    (∀ i s t, r i t < r i s → D.income i t < dot (D.price t) (x i s)) ∧
    (∀ i s t, r i t ≤ r i s → D.income i t ≤ dot (D.price t) (x i s))

/-- A finite union of linear systems; unlike the Afriat formulation it has no
continuous utility labels, marginal-utility multipliers, or bilinear terms. -/
def HasOrdinalAllocation [Fintype I] [Fintype T] (D : MarketData L I T) : Prop :=
  ∃ (r : I → ObservationRanks T) (x : I → T → Bundle L), OrdinalAllocationFeasible D r x

/-- The ordinal formulation preserves the same jointly clearing allocation. -/
theorem hasGARPAllocation_iff_hasOrdinalAllocation [Fintype I] [Fintype T]
    (D : MarketData L I T) : HasGARPAllocation D ↔ HasOrdinalAllocation D := by
  classical
  constructor
  · rintro ⟨x, hx, hG⟩
    have hr := fun i => exists_observationRanks_of_graphGARP D.price (x i) (hG i)
    choose r hr using hr
    refine ⟨r, x, hx, ?_, ?_⟩
    · intro i s t hst
      simpa only [hx.budget i t] using (hr i).1 s t hst
    · intro i s t hst
      simpa only [hx.budget i t] using (hr i).2 s t hst
  · rintro ⟨r, x, hx, hstrict, hweak⟩
    refine ⟨x, hx, fun i => graphGARP_of_rankCompatible D.price (x i)
      (fun t => (r i t).val) ⟨?_, ?_⟩⟩
    · intro s t hst
      simpa only [hx.budget i t] using hstrict i s t hst
    · intro s t hst
      simpa only [hx.budget i t] using hweak i s t hst

/-- The finite linear disjunction is an exact utility-maximizing equilibrium
test under positive prices, not merely a necessary pairwise condition. -/
theorem hasRegularEquilibriumRationalization_iff_hasOrdinalAllocation
    [Fintype I] [Fintype T] [Nonempty T]
    (D : MarketData L I T) (hp : ∀ t k, 0 < D.price t k) :
    HasRegularEquilibriumRationalization D ↔ HasOrdinalAllocation D := by
  rw [← hasGARPAllocation_iff_hasOrdinalAllocation D]
  exact ⟨fun h => hasGARPAllocation_of_hasIncreasingEquilibriumRationalization D hp h.to_increasing,
    hasRegularEquilibriumRationalization_of_hasGARPAllocation D hp⟩

/-- Comparison weights can be positive only when the target bundle has at least
the rank of the observation at whose prices it is evaluated. -/
def AdmissibleComparisonWeights [Fintype T] (r : I → ObservationRanks T)
    (a : I → T → T → ℝ) : Prop :=
  (∀ i s t, 0 ≤ a i s t) ∧ (∀ i s t, ¬ r i t ≤ r i s → a i s t = 0)

/-- Free budget and resource multipliers dominate the weighted comparison-price
vector, coordinatewise. This condition mentions observations and weights only. -/
def DualPriceDominates [Fintype T] (D : MarketData L I T)
    (a : I → T → T → ℝ) (b : I → T → ℝ) (c : T → Bundle L) : Prop :=
  ∀ i s k, (∑ t, a i s t * D.price t k) ≤ b i s * D.price s k + c s k

/-- Observable value of a balanced comparison-price certificate. -/
def OrdinalDualValue [Fintype I] [Fintype T] (D : MarketData L I T)
    (a : I → T → T → ℝ) (b : I → T → ℝ) (c : T → Bundle L) : ℝ :=
  (∑ i, ∑ s, b i s * D.income i s) + (∑ s, dot (c s) (D.resources s)) -
    ∑ i, ∑ s, ∑ t, a i s t * D.income i t

/-- Observable dual restrictions for a fixed rank profile. The strict clause
must be retained: a positive weight on a strict comparison forces positive
certificate value. Sufficiency requires a theorem of alternatives. -/
def OrdinalDualCondition [Fintype I] [Fintype T] (D : MarketData L I T)
    (r : I → ObservationRanks T) : Prop :=
  ∀ (a : I → T → T → ℝ) (b : I → T → ℝ) (c : T → Bundle L),
    AdmissibleComparisonWeights r a → DualPriceDominates D a b c →
    0 ≤ OrdinalDualValue D a b c ∧
      ((∃ i s t, r i t < r i s ∧ 0 < a i s t) → 0 < OrdinalDualValue D a b c)

/-- A finite disjunction of observable dual restrictions; its necessity is
proved below. No sufficiency claim is built into this definition. -/
def HasOrdinalDualCondition [Fintype I] [Fintype T] (D : MarketData L I T) : Prop :=
  ∃ r : I → ObservationRanks T, OrdinalDualCondition D r

/-- Dual price domination bounds weighted cross-observation expenditures by
the observable budget/resource value. Multipliers `b` and `c` are unrestricted. -/
theorem AllocationFeasible.weighted_expenditure_le [Fintype I] [Fintype T]
    {D : MarketData L I T} {x : I → T → Bundle L} (hx : AllocationFeasible D x)
    (a : I → T → T → ℝ) (b : I → T → ℝ) (c : T → Bundle L)
    (hd : DualPriceDominates D a b c) :
    (∑ i, ∑ s, ∑ t, a i s t * dot (D.price t) (x i s)) ≤
      (∑ i, ∑ s, b i s * D.income i s) + ∑ s, dot (c s) (D.resources s) := by
  have hpoint (i : I) (s : T) :
      (∑ t, a i s t * dot (D.price t) (x i s)) ≤
        b i s * D.income i s + dot (c s) (x i s) := by
    calc
      _ = dot (∑ t, a i s t • D.price t) (x i s) := by
        simp only [dot, sum_dotProduct, smul_dotProduct, smul_eq_mul]
      _ ≤ dot (b i s • D.price s + c s) (x i s) := by
        apply Finset.sum_le_sum
        intro k _
        apply mul_le_mul_of_nonneg_right _ (hx.nonneg i s k)
        simpa only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul] using hd i s k
      _ = b i s * D.income i s + dot (c s) (x i s) := by
        change dotProduct (b i s • D.price s + c s) (x i s) = _
        rw [add_dotProduct, smul_dotProduct]
        change b i s * dot (D.price s) (x i s) + dot (c s) (x i s) = _
        rw [hx.budget i s]
  have hclear : (∑ i, ∑ s, dot (c s) (x i s)) = ∑ s, dot (c s) (D.resources s) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    rw [← hx.clearing s]
    simp only [dot, dotProduct_sum]
  calc
    _ ≤ ∑ i, ∑ s, (b i s * D.income i s + dot (c s) (x i s)) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun s _ => hpoint i s
    _ = _ := by simp only [Finset.sum_add_distrib, hclear]

/-- Every feasible ordinal allocation satisfies the observable dual test,
including its strict clause. A violating dual certificate rules out that rank
profile without inspecting any candidate allocation. -/
theorem OrdinalAllocationFeasible.ordinalDualCondition [Fintype I] [Fintype T]
    {D : MarketData L I T} {r : I → ObservationRanks T} {x : I → T → Bundle L}
    (hx : OrdinalAllocationFeasible D r x) : OrdinalDualCondition D r := by
  intro a b c ha hd
  have hp (i : I) (s t : T) :
      a i s t * D.income i t ≤ a i s t * dot (D.price t) (x i s) := by
    by_cases hr : r i t ≤ r i s
    · exact mul_le_mul_of_nonneg_left (hx.2.2 i s t hr) (ha.1 i s t)
    · simp only [ha.2 i s t hr, zero_mul, le_refl]
  have hs (i : I) (s : T) :
      (∑ t, a i s t * D.income i t) ≤ ∑ t, a i s t * dot (D.price t) (x i s) :=
    Finset.sum_le_sum fun t _ => hp i s t
  have hi (i : I) :
      (∑ s, ∑ t, a i s t * D.income i t) ≤
        ∑ s, ∑ t, a i s t * dot (D.price t) (x i s) :=
    Finset.sum_le_sum fun s _ => hs i s
  have hweak := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  have hupper := hx.1.weighted_expenditure_le a b c hd
  constructor
  · exact sub_nonneg.mpr (hweak.trans hupper)
  · rintro ⟨i, s, t, hr, haPos⟩
    have ht : a i s t * D.income i t < a i s t * dot (D.price t) (x i s) :=
      mul_lt_mul_of_pos_left (hx.2.1 i s t hr) haPos
    have hst : (∑ t, a i s t * D.income i t) <
        ∑ t, a i s t * dot (D.price t) (x i s) :=
      Finset.sum_lt_sum (fun t _ => hp i s t) ⟨t, Finset.mem_univ t, ht⟩
    have hit : (∑ s, ∑ t, a i s t * D.income i t) <
        ∑ s, ∑ t, a i s t * dot (D.price t) (x i s) :=
      Finset.sum_lt_sum (fun s _ => hs i s) ⟨s, Finset.mem_univ s, hst⟩
    have hall := Finset.sum_lt_sum (fun i _ => hi i) ⟨i, Finset.mem_univ i, hit⟩
    exact sub_pos.mpr (hall.trans_le hupper)

/-- Joint GARP implies a finite disjunction of fully observable dual tests. -/
theorem hasOrdinalDualCondition_of_hasGARPAllocation [Fintype I] [Fintype T]
    {D : MarketData L I T} (h : HasGARPAllocation D) : HasOrdinalDualCondition D := by
  obtain ⟨r, x, hx⟩ := (hasGARPAllocation_iff_hasOrdinalAllocation D).mp h
  exact ⟨r, hx.ordinalDualCondition⟩

/-- Observable dual certificates are necessary for ordinary utility-maximizing
equilibrium. The utility bridge is the only place positive prices are needed. -/
theorem hasOrdinalDualCondition_of_hasIncreasingEquilibriumRationalization
    [Fintype I] [Fintype T] {D : MarketData L I T}
    (hp : ∀ t k, 0 < D.price t k) (h : HasIncreasingEquilibriumRationalization D) :
    HasOrdinalDualCondition D :=
  hasOrdinalDualCondition_of_hasGARPAllocation
    (hasGARPAllocation_of_hasIncreasingEquilibriumRationalization D hp h)

end MathEconLib.RevealedPreference.Equilibrium
