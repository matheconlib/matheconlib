/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.GameTheory.Strategic.OutcomeIncentives
public import MathEconLib.Mechanism.Core.Utility

/-!
# Deterministic mechanism incentives with explicit comparisons

The mechanism supplies physical outcomes and signed transfer vectors. Supplied comparisons
evaluate these consequences at the full true type profile, held fixed under action deviations.
Intended strategies may use different type and action carriers. Direct truth is the identity
strategy. The predicates use full product action domains and require no prior, private values,
completeness, or numerical utility representation.

## Main definitions

* `Mechanism.IsDSICWith`: intended actions are dominant under the supplied comparisons.
* `Mechanism.IsExPostICWith`: intended play is Nash at every true type profile.

## Main statements

* `Mechanism.IsDSICWith.isExPostICWith`: dominance implies ex-post IC.
* `Mechanism.isDSICWith_iff_isDominant_of_representation`: exact utility representations recover
  the existing dominance predicate.
* `Mechanism.isExPostICWith_iff_isNash_of_representation`: exact representations recover Nash.

## Tags

mechanism design, dominance, ex-post incentives, comparisons
-/

@[expose] public section

open MathEconLib.GameTheory

namespace MathEconLib.Mechanism

universe uI uT uA uO uV

variable {I : Type uI} {T : I → Type uT} {A : I → Type uA} {O : Type uO}
  {V : Type uV} [DecidableEq I]

/-- Intended play is dominant under comparisons of complete mechanism consequences.
`R i θ c d` means that agent `i` weakly prefers `d` to `c` at the fixed true profile `θ`. -/
def IsDSICWith (M : Mechanism I A O)
    (R : I → Profile T → (O × (I → ℝ)) → (O × (I → ℝ)) → Prop)
    (σ : (i : I) → T i → A i) : Prop :=
  M.toOutcomeGame.IsDominantStrategyWith R σ

/-- Intended play is Nash at every true profile under the supplied consequence comparisons.
Opponents follow their intended actions here, rather than arbitrary actions as in dominance. -/
def IsExPostICWith (M : Mechanism I A O)
    (R : I → Profile T → (O × (I → ℝ)) → (O × (I → ℝ)) → Prop)
    (σ : (i : I) → T i → A i) : Prop :=
  M.toOutcomeGame.IsExPostNashWith R σ

/-- Dominance compares every action profile with replacement of one's own action by intended play.
The true profile stays fixed when either the physical outcome or transfers change. -/
theorem isDSICWith_iff (M : Mechanism I A O)
    (R : I → Profile T → (O × (I → ℝ)) → (O × (I → ℝ)) → Prop)
    (σ : (i : I) → T i → A i) :
    M.IsDSICWith R σ ↔ ∀ θ i a,
      R i θ (M.outcome a, fun j ↦ M.transfer j a)
        (M.outcome (Function.update a i (σ i (θ i))),
          fun j ↦ M.transfer j (Function.update a i (σ i (θ i)))) :=
  M.toOutcomeGame.isDominantStrategyWith_iff R σ

/-- Ex-post IC compares each unilateral deviation with intended play at the same true profile. -/
theorem isExPostICWith_iff (M : Mechanism I A O)
    (R : I → Profile T → (O × (I → ℝ)) → (O × (I → ℝ)) → Prop)
    (σ : (i : I) → T i → A i) :
    M.IsExPostICWith R σ ↔ ∀ θ i ai,
      R i θ (M.outcome (Function.update (fun j ↦ σ j (θ j)) i ai),
          fun j ↦ M.transfer j (Function.update (fun k ↦ σ k (θ k)) i ai))
        (M.outcome (fun j ↦ σ j (θ j)), fun j ↦ M.transfer j (fun k ↦ σ k (θ k))) :=
  M.toOutcomeGame.isExPostNashWith_iff R σ

/-- Dominant intended play gives ex-post IC without private values or order assumptions. -/
theorem IsDSICWith.isExPostICWith {M : Mechanism I A O}
    {R : I → Profile T → (O × (I → ℝ)) → (O × (I → ℝ)) → Prop}
    {σ : (i : I) → T i → A i} (h : M.IsDSICWith R σ) : M.IsExPostICWith R σ :=
  OutcomeGame.IsDominantStrategyWith.isExPostNashWith h

/-- Exact representation by supplied utilities recovers weak dominance in each fixed-type game.
Only `LE V` is needed; the comparison predicate itself requires no numerical representation. -/
theorem isDSICWith_iff_isDominant_of_representation [LE V] (M : Mechanism I A O)
    (R : I → Profile T → (O × (I → ℝ)) → (O × (I → ℝ)) → Prop)
    (u : I → Profile T → (O × (I → ℝ)) → V)
    (hrep : ∀ i θ c d, R i θ c d ↔ u i θ c ≤ u i θ d)
    (σ : (i : I) → T i → A i) :
    M.IsDSICWith R σ ↔ ∀ θ i,
      StrategicGame.Strategy.IsDominant (G := M.toStrategicGame u θ) (σ i (θ i)) :=
  M.toOutcomeGame.isDominantStrategyWith_iff_isDominant_of_representation R u hrep σ

/-- Exact utility representation recovers Nash at every fixed true profile. -/
theorem isExPostICWith_iff_isNash_of_representation [LE V] (M : Mechanism I A O)
    (R : I → Profile T → (O × (I → ℝ)) → (O × (I → ℝ)) → Prop)
    (u : I → Profile T → (O × (I → ℝ)) → V)
    (hrep : ∀ i θ c d, R i θ c d ↔ u i θ c ≤ u i θ d)
    (σ : (i : I) → T i → A i) :
    M.IsExPostICWith R σ ↔ ∀ θ,
      (M.toStrategicGame u θ).IsNash (fun i ↦ σ i (θ i)) :=
  M.toOutcomeGame.isExPostNashWith_iff_isNash_of_representation R u hrep σ

end MathEconLib.Mechanism

end
