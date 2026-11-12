/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLib.RevealedPreference.EquilibriumElimination

/-!
# Welfare consequences of finite revealed equilibrium

A joint Afriat certificate supports the same observed allocation as a maximizer
of weighted utility. Each household has one fixed Afriat utility across observations;
the positive welfare weight at an observation is the reciprocal of its Afriat
multiplier there. The supporting inequality, rather than differentiability or
interior consumption, proves this claim. Resource feasibility allows free disposal.
Strictly positive weights then exclude an improvement for some household without
a loss for another. This is a classical welfare consequence of the equilibrium
characterization, not a new criterion equating Pareto efficiency alone with GARE.
Weights may vary across observations and depend on utility normalization; the
result identifies neither interpersonal cardinal comparisons nor fixed welfare weights.

## References

Takashi Negishi (1960), *Welfare Economics and Existence of an Equilibrium for a
Competitive Economy*, Metroeconomica **12**(2–3), 92–97.
[DOI: 10.1111/j.1467-999X.1960.tb00275.x](https://doi.org/10.1111/j.1467-999X.1960.tb00275.x).
The module formalizes the finite Afriat supporting-plane welfare implication.
It does not formalize Negishi's equilibrium existence argument.
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace MathEconLib.RevealedPreference.Equilibrium

variable {L : ℕ} {I T : Type*}

/-- Nonnegative household allocations using at most the available resources. -/
def resourceFeasibleSet [Fintype I] (w : Bundle L) : Set (I → Bundle L) :=
  {x | (∀ i, Nonnegative (x i)) ∧ ∑ i, x i ≤ w}

/-- The weighted sum of the specified cardinal utility representations. Weight
positivity is imposed by theorems needing it, not by this definition. -/
def weightedWelfare [Fintype I] (u : I → Utility L) (α : I → ℝ)
    (x : I → Bundle L) : ℝ :=
  ∑ i, α i * u i (x i)

/-- A resource-feasible allocation admitting no feasible weak improvement for all
households with a strict improvement for at least one household. -/
def ParetoEfficient [Fintype I] (w : Bundle L) (u : I → Utility L)
    (x : I → Bundle L) : Prop :=
  x ∈ resourceFeasibleSet w ∧
    ∀ y ∈ resourceFeasibleSet w, (∀ i, u i (x i) ≤ u i (y i)) →
      ¬ ∃ i, u i (x i) < u i (y i)

/-- Clearing and nonnegative consumption imply resource feasibility. -/
theorem AllocationFeasible.mem_resourceFeasibleSet [Fintype I]
    {D : MarketData L I T} {x : I → T → Bundle L}
    (hx : AllocationFeasible D x) (t : T) :
    (fun i => x i t) ∈ resourceFeasibleSet (D.resources t) :=
  ⟨fun i => hx.nonneg i t, (hx.clearing t).le⟩

/-- Household supporting inequalities at a common nonnegative resource price
sum to weighted welfare maximization. Feasibility of the candidate is separate,
as in Mathlib's `IsMaxOn`; market clearing is the hypothesis used in this proof. -/
theorem isMaxOn_weightedWelfare_of_support [Fintype I]
    (w p : Bundle L) (u : I → Utility L) (α : I → ℝ) (x : I → Bundle L)
    (hp : Nonnegative p) (hclearing : ∑ i, x i = w)
    (hsupport : ∀ i y, Nonnegative y →
      α i * u i y ≤ α i * u i (x i) + dot p y - dot p (x i)) :
    IsMaxOn (weightedWelfare u α) (resourceFeasibleSet w) x := by
  apply isMaxOn_iff.mpr
  intro y hy
  have hsum := Finset.sum_le_sum (fun i (_hi : i ∈ Finset.univ) =>
    hsupport i (y i) (hy.1 i))
  have hdot_sum (z : I → Bundle L) : ∑ i, dot p (z i) = dot p (∑ i, z i) := by
    simp only [dot, dotProduct, Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_comm
  have hresource : dot p (∑ i, y i) ≤ dot p w := by
    apply Finset.sum_le_sum
    intro k _hk
    exact mul_le_mul_of_nonneg_left (hy.2 k) (hp k)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, hdot_sum, hclearing] at hsum
  dsimp [weightedWelfare]
  linarith

/-- Strictly positive welfare weights rule out every Pareto improvement.
Neither concavity nor monotonicity is needed for this implication. -/
theorem paretoEfficient_of_isMaxOn_weightedWelfare [Fintype I]
    (w : Bundle L) (u : I → Utility L) (α : I → ℝ) (x : I → Bundle L)
    (hα : ∀ i, 0 < α i) (hx : x ∈ resourceFeasibleSet w)
    (hmax : IsMaxOn (weightedWelfare u α) (resourceFeasibleSet w) x) :
    ParetoEfficient w u x := by
  refine ⟨hx, ?_⟩
  intro y hy hweak hstrict
  obtain ⟨j, hj⟩ := hstrict
  have hlt : weightedWelfare u α x < weightedWelfare u α y := by
    apply Finset.sum_lt_sum
    · intro i _hi
      exact mul_le_mul_of_nonneg_left (hweak i) (hα i).le
    · exact ⟨j, Finset.mem_univ j, mul_lt_mul_of_pos_left hj (hα j)⟩
  exact (not_lt_of_ge (isMaxOn_iff.mp hmax y hy)) hlt

/-- Reciprocal Afriat multipliers scale each household's supporting plane to the
same observed price. No positivity of consumption or income is required. -/
theorem afriatUtility_reciprocal_support [Fintype T] [Nonempty T]
    (U lam : T → ℝ) (p q : T → Bundle L)
    (hpos : PositiveMultipliers lam) (hA : AfriatInequalities U lam p q)
    (t : T) (y : Bundle L) :
    (lam t)⁻¹ * globalAfriatUtility U lam p q y ≤
      (lam t)⁻¹ * globalAfriatUtility U lam p q (q t) + dot (p t) y - dot (p t) (q t) := by
  have h := mul_le_mul_of_nonneg_left
    (globalAfriatUtility_le_support U lam p q t y) (inv_pos.mpr (hpos t)).le
  rw [globalAfriatUtility_eq_observed U lam p q hA t]
  unfold globalAfriatSupport at h
  simpa only [mul_add, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt (hpos t)), one_mul,
    add_sub_assoc] using h

/-- The supplied joint Afriat allocation maximizes weighted welfare, with the
reciprocal positive multipliers as weights, and is Pareto efficient. -/
theorem afriatAllocation_weightedWelfare_paretoEfficient
    [Fintype I] [Fintype T] [Nonempty T]
    (D : MarketData L I T) (hp : ∀ t, Nonnegative (D.price t))
    (x : I → T → Bundle L) (U lam : I → T → ℝ)
    (hx : AllocationFeasible D x)
    (hcert : ∀ i, PositiveMultipliers (lam i) ∧
      AfriatInequalities (U i) (lam i) D.price (x i)) (t : T) :
    let u := fun i => globalAfriatUtility (U i) (lam i) D.price (x i)
    let α := fun i => (lam i t)⁻¹
    (∀ i, 0 < α i) ∧
      IsMaxOn (weightedWelfare u α) (resourceFeasibleSet (D.resources t)) (fun i => x i t) ∧
      ParetoEfficient (D.resources t) u (fun i => x i t) := by
  dsimp only
  have hα : ∀ i, 0 < (lam i t)⁻¹ := fun i => inv_pos.mpr ((hcert i).1 t)
  have hmax := isMaxOn_weightedWelfare_of_support (D.resources t) (D.price t)
    (fun i => globalAfriatUtility (U i) (lam i) D.price (x i))
    (fun i => (lam i t)⁻¹) (fun i => x i t) (hp t) (hx.clearing t)
    (fun i y _hy => afriatUtility_reciprocal_support (U i) (lam i) D.price (x i)
      (hcert i).1 (hcert i).2 t y)
  exact ⟨hα, hmax, paretoEfficient_of_isMaxOn_weightedWelfare _ _ _ _ hα
    (hx.mem_resourceFeasibleSet t) hmax⟩

/-- A supplied GARP allocation admits fixed regular utilities and positive,
possibly observation-dependent welfare weights supporting that same allocation. -/
theorem exists_regularUtility_weightedWelfare_paretoEfficient_of_garpAllocation
    [Fintype I] [Finite T] [Nonempty T]
    (D : MarketData L I T) (hp : ∀ t k, 0 < D.price t k)
    (x : I → T → Bundle L) (hx : AllocationFeasible D x)
    (hG : ∀ i, GraphGARP D.price (x i)) :
    ∃ (u : I → Utility L) (α : I → T → ℝ),
      (∀ i, Continuous (u i) ∧ ConcaveOn ℝ Set.univ (u i) ∧ StrictlyIncreasing (u i)) ∧
      UtilityMaximizes D x u ∧
      ∀ t, (∀ i, 0 < α i t) ∧
        IsMaxOn (weightedWelfare u (fun i => α i t))
          (resourceFeasibleSet (D.resources t)) (fun i => x i t) ∧
        ParetoEfficient (D.resources t) u (fun i => x i t) := by
  classical
  let := Fintype.ofFinite T
  have hcert := fun i => (graphGARP_iff_exists_afriatInequalities D.price (x i)).mp (hG i)
  choose U lam hpos hA using hcert
  let u := fun i => globalAfriatUtility (U i) (lam i) D.price (x i)
  refine ⟨u, (fun i t => (lam i t)⁻¹), ?_, ?_, ?_⟩
  · intro i
    exact ⟨globalAfriatUtility_continuous _ _ _ _, globalAfriatUtility_concaveOn _ _ _ _,
      globalAfriatUtility_strictlyIncreasing _ _ _ _ hp (hpos i)⟩
  · apply (utilityMaximizes_iff_forall_utilityRationalizes D hp x hx u).mpr
    intro i
    exact globalAfriatUtility_rationalizes (consumerDataset D hp x hx i) (U i) (lam i)
      (hA i) (hpos i)
  · intro t
    exact afriatAllocation_weightedWelfare_paretoEfficient D (fun t k => (hp t k).le)
      x U lam hx (fun i => ⟨hpos i, hA i⟩) t

/-- GARE supplies a jointly feasible allocation, fixed regular household utilities,
and observation-specific positive weights proving weighted welfare maximization
and Pareto efficiency at every observed resource vector. -/
theorem exists_regularUtility_weightedWelfare_paretoEfficient_of_gare
    [Fintype I] [Fintype T] [Nonempty T]
    (D : MarketData L I T) (hp : ∀ t k, 0 < D.price t k) (h : GARE D) :
    ∃ (x : I → T → Bundle L) (u : I → Utility L) (α : I → T → ℝ),
      AllocationFeasible D x ∧
      (∀ i, Continuous (u i) ∧ ConcaveOn ℝ Set.univ (u i) ∧ StrictlyIncreasing (u i)) ∧
      UtilityMaximizes D x u ∧
      ∀ t, (∀ i, 0 < α i t) ∧
        IsMaxOn (weightedWelfare u (fun i => α i t))
          (resourceFeasibleSet (D.resources t)) (fun i => x i t) ∧
        ParetoEfficient (D.resources t) u (fun i => x i t) := by
  obtain ⟨x, hx, hG⟩ := (hasGARPAllocation_iff_gare D).mpr h
  obtain ⟨u, α, hreg, hmax, hwelfare⟩ :=
    exists_regularUtility_weightedWelfare_paretoEfficient_of_garpAllocation D hp x hx hG
  exact ⟨x, u, α, hx, hreg, hmax, hwelfare⟩

end MathEconLib.RevealedPreference.Equilibrium
