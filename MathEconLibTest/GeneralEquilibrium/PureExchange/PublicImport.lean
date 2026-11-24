/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

import MathEconLib.GeneralEquilibrium.PureExchange

/-!
# Pure-exchange public API contracts

These checks import only the public topic umbrella. They pin full-budget demand, the
constitutive equilibrium conditions, and existence from complete preference primitives
with separate closed contours, ordinary convexity, and strong monotonicity.
-/

set_option linter.privateModule false

open scoped BigOperators
open MathEconLib.Preferences MathEconLib.RevealedPreference
open MathEconLib.GeneralEquilibrium.PureExchange

example {L : ℕ} (e p : Bundle L) (x : Orthant L) :
    x ∈ budgetSet e p ↔ dot p x.val ≤ dot p e := Iff.rfl

example {L : ℕ} (P : CompletePreference (Orthant L)) (e p : Bundle L) (x : Orthant L) :
    x ∈ demand P e p ↔
      dot p x.val ≤ dot p e ∧ ∀ y : Orthant L, dot p y.val ≤ dot p e → P.le y x := Iff.rfl

example {L : ℕ} {I : Type*} [Fintype I]
    (e : I → Bundle L) (P : I → CompletePreference (Orthant L))
    (p : Bundle L) (x : I → Orthant L) :
    IsWalrasianEquilibrium e P p x ↔
      (∀ i, Nonnegative (e i)) ∧ Nonnegative p ∧ p ≠ 0 ∧
      (∀ i, x i ∈ demand (P i) (e i) p) ∧ (∑ i, (x i).val) = ∑ i, e i :=
  isWalrasianEquilibrium_iff e P p x

-- Feasibility is weak affordability; normalization and budget exhaustion are not fields.
example {L : ℕ} {I : Type*} [Fintype I]
    (e : I → Bundle L) (P : I → CompletePreference (Orthant L))
    (p : Bundle L) (x : I → Orthant L) :
    IsWalrasianEquilibrium e P p x ↔
      (∀ i, Nonnegative (e i)) ∧ Nonnegative p ∧ p ≠ 0 ∧
      (∀ i, dot p (x i).val ≤ dot p (e i)) ∧
      (∀ i (y : Orthant L), dot p y.val ≤ dot p (e i) → (P i).le y (x i)) ∧
      (∑ i, (x i).val) = ∑ i, e i := by
  constructor
  · intro h
    exact ⟨h.endowment_nonneg, h.price_nonneg, h.price_ne_zero,
      h.budget_feasible, h.optimal, h.clearing⟩
  · rintro ⟨he, hp, hp0, hb, ho, hc⟩
    exact ⟨he, hp, hp0, hb, ho, hc⟩

-- Expanding regularity protects the primitive-preference scope, with no Nonempty I premise.
example {L : ℕ} (hL : 0 < L) {I : Type*} [Fintype I]
    (e : I → Bundle L) (P : I → CompletePreference (Orthant L))
    (he : ∀ i k, 0 < e i k)
    (hupper : ∀ i x, IsClosed {y | (P i).le x y})
    (hlower : ∀ i x, IsClosed {y | (P i).le y x})
    (hconv : ∀ i x, Convex ℝ
      {y : Bundle L | ∃ hy : Nonnegative y, (P i).le x ⟨y, hy⟩})
    (hmono : ∀ i {x y : Orthant L}, x.val < y.val → (P i).le x y ∧ ¬ (P i).le y x) :
    ∃ (p : Bundle L) (x : I → Orthant L),
      IsWalrasianEquilibrium e P p x ∧ (∑ k, p k) = 1 ∧
      (∀ k, 0 < p k) ∧ (∀ i, dot p (x i).val = dot p (e i)) := by
  have hP : ∀ i, PreferenceRegularity (P i) := fun i =>
    { closed_upper := hupper i
      closed_lower := hlower i
      convex_upper := hconv i
      strong_mono := hmono i }
  exact exists_walrasianEquilibrium hL e P he hP

-- The empty-household case obtains positive normalized prices through the public theorem.
example (e : Fin 0 → Bundle 2) (P : Fin 0 → CompletePreference (Orthant 2)) :
    ∃ (p : Bundle 2) (x : Fin 0 → Orthant 2),
      IsWalrasianEquilibrium e P p x ∧ (∑ k, p k) = 1 ∧
      (∀ k, 0 < p k) ∧ (∀ i, dot p (x i).val = dot p (e i)) :=
  exists_walrasianEquilibrium (by decide) e P (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)

-- Zero goods cannot support even the unnormalized equilibrium predicate.
example {I : Type*} [Fintype I] (e : I → Bundle 0)
    (P : I → CompletePreference (Orthant 0)) (p : Bundle 0) (x : I → Orthant 0) :
    ¬ IsWalrasianEquilibrium e P p x := by
  intro h
  exact h.price_ne_zero (Subsingleton.elim _ _)
