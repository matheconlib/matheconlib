/-
Copyright (c) 2026 Ruiz Chen, Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiz Chen, Bo Cowgill
-/
module

public import MathEconLib.Auction.Basic
public import Mathlib

/-! # Affiliation (Section 7)

This file formalizes the definitional layer of Section 7 on affiliation, the
positive-dependence condition of Milgrom–Weber.

It contains three things:

* **Def 7.2** — the `Affiliated` predicate on weights `f : (Fin n → ℝ) → ℝ`:
  for all signal profiles `x` and `y`,
  `f (x ⊔ y) * f (x ⊓ y) ≥ f x * f y`, where `⊔`/`⊓` are the pointwise
  (componentwise max/min) lattice operations on `Fin n → ℝ`.
* **Remark 6** — the independence knife-edge: if `f` factors as a product of its
  per-coordinate factors, then the affiliation inequality holds with equality
  everywhere (`factors_affiliation_eq`), and hence `f` is affiliated
  (`factors_affiliated`). Independence is the boundary (knife-edge) case of the
  affiliation cone when a corresponding probability model is supplied.
* **Def 7.1** — the signal/value environment `SignalValueEnv`, carrying the signal
  bounds, the bidders' value functions, and their regularity (nonnegativity,
  continuity, monotonicity, and strict monotonicity in the bidder's own signal),
  together with the `IsPrivateValues` predicate isolating the private-values case.

Affiliation and factorization here are algebraic. `SignalValueEnv.f` is a nonnegative weight
function supported on the declared box; no reference measure, measurability,
normalization or probability law is supplied. Even zero weights are allowed.
`Factors` and the legacy name `HasIndependentSignals` assert only product
factorization, not probabilistic independence.

For probability semantics, separately supply a joint probability law and identify
`f` with its mass function or with a measurable density relative to a specified
reference measure. A density must have total mass one, or positive finite mass
followed by explicit normalization. Independence additionally requires a product
law with the corresponding probability marginals (and a product reference measure
for a density factorization). Restricting factorized weights to a nonproduct
finite support can introduce dependence. The finite conditional-average files
normalize weights on each conditioning set; those averages do not automatically
describe conditioning a separately supplied continuous signal law.
-/

namespace MathEconLib

@[expose] public section

open Finset

namespace Auction.Affiliation

/-! ### Def 7.2 — the affiliation predicate -/

/-- **Def 7.2** (affiliation). Weights `f : (Fin n → ℝ) → ℝ` are *affiliated*
when, for every pair of signal profiles `x` and `y`,
`f (x ⊔ y) * f (x ⊓ y) ≥ f x * f y`.

Here `⊔` and `⊓` are the pointwise lattice operations on `Fin n → ℝ` from
Mathlib's `Pi.lattice`, so `(x ⊔ y) i = max (x i) (y i)` and
`(x ⊓ y) i = min (x i) (y i)`, matching the notes' componentwise `∨`/`∧`.

The predicate is purely the algebraic inequality: it assumes neither positivity
nor normalization, and does not itself provide a probability law. -/
def Affiliated {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x y : Fin n → ℝ, f (x ⊔ y) * f (x ⊓ y) ≥ f x * f y

/-! ### Remark 6 — the independence knife-edge -/

/-- The factorization predicate used in Remark 6: `f` is the product of its
per-coordinate factors `g i`, i.e. `f x = ∏ i, g i (x i)` for every profile `x`.
There are no sign, measurability or normalization assumptions on the factors.
Probabilistic independence requires a separately supplied product probability
model linked to these weights, as described in the module documentation. -/
def Factors {n : ℕ} (f : (Fin n → ℝ) → ℝ) (g : Fin n → ℝ → ℝ) : Prop :=
  ∀ x, f x = ∏ i, g i (x i)

/-- Per-coordinate knife-edge fact: for any real `a`, `b` and any `h : ℝ → ℝ`,
`h (a ⊔ b) * h (a ⊓ b) = h a * h b`, since `{a ⊔ b, a ⊓ b} = {a, b}` as a multiset
(case split on `a ≤ b`). -/
theorem mul_sup_inf_eq (h : ℝ → ℝ) (a b : ℝ) :
    h (a ⊔ b) * h (a ⊓ b) = h a * h b := by
  rcases le_total a b with hab | hab
  · rw [sup_of_le_right hab, inf_of_le_left hab, mul_comm]
  · rw [sup_of_le_left hab, inf_of_le_right hab]

/-- **Remark 6** (equality form, the knife-edge proper). If `f` factors as a product
of its per-coordinate factors, then the affiliation inequality of Def 7.2 holds
with *equality* everywhere:
`f (x ⊔ y) * f (x ⊓ y) = f x * f y` for all `x`, `y`.

This is "Theorem 7.2 holds with equality": factorization sits on the boundary of the
affiliation cone. No positivity is needed. -/
theorem factors_affiliation_eq {n : ℕ} {f : (Fin n → ℝ) → ℝ} {g : Fin n → ℝ → ℝ}
    (hf : Factors f g) :
    ∀ x y : Fin n → ℝ, f (x ⊔ y) * f (x ⊓ y) = f x * f y := by
  intro x y
  rw [hf, hf, hf, hf, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [Pi.sup_apply, Pi.inf_apply]
  exact mul_sup_inf_eq (g i) (x i) (y i)

/-- **Remark 6** (corollary). Weights that factor as a product of their
per-coordinate factors are affiliated: the `≥` of Def 7.2 follows from the
equality of `factors_affiliation_eq` via `ge_of_eq`. This is an algebraic result;
no probability normalization is required. -/
theorem factors_affiliated {n : ℕ} {f : (Fin n → ℝ) → ℝ} {g : Fin n → ℝ → ℝ}
    (hf : Factors f g) : Affiliated f := by
  intro x y
  exact ge_of_eq (factors_affiliation_eq hf x y)

/-! ### Def 7.1 — the signal/value environment -/

/-- **Def 7.1** (signal/value environment). An `n`-bidder model in which a signal
profile is `X : Fin n → ℝ` (coordinate `i` is bidder `i`'s own signal `Xᵢ`,
the others being the rivals' signals `X₋ᵢ`), and `v i X` is bidder `i`'s value
given the full profile `X`.

The fields record the regularity of the value functions from the notes:
nonnegativity (`v_nonneg`), continuity (`v_continuous`), monotonicity in the
product/pointwise order (`v_mono`, "nondecreasing"), and strict monotonicity in the
bidder's own signal with the rivals held fixed (`v_strictMono_own`). -/
structure SignalValueEnv (n : ℕ) where
  /-- Lower signal bound `x`. -/
  x_lo : ℝ
  /-- Upper signal bound `x̄`. -/
  x_hi : ℝ
  /-- The signal bounds form a nonempty interval. -/
  x_lo_le_hi : x_lo ≤ x_hi
  /-- Raw signal weights on profiles `X = (X₁,…,Xₙ)`, without measurability,
  normalization or a supplied probability law. -/
  f : (Fin n → ℝ) → ℝ
  /-- The signal weights are nonnegative. -/
  f_nonneg : ∀ X, 0 ≤ f X
  /-- The signal weights are supported on the box `[x_lo, x_hi]ⁿ`: they vanish off it.
  This is what makes the declared signal bounds load-bearing. -/
  f_support : ∀ X : Fin n → ℝ, (∃ i, X i ∉ Set.Icc x_lo x_hi) → f X = 0
  /-- Bidder `i`'s value given the full signal profile `X`. -/
  v : Fin n → (Fin n → ℝ) → ℝ
  /-- Values are nonnegative (`vᵢ : ⋯ → ℝ_{≥0}`). -/
  v_nonneg : ∀ i X, 0 ≤ v i X
  /-- Values are continuous in the profile. -/
  v_continuous : ∀ i, Continuous (v i)
  /-- Values are nondecreasing in the product (pointwise) order on profiles. -/
  v_mono : ∀ i, Monotone (v i)
  /-- Values are strictly increasing in the bidder's own signal, rivals held fixed. -/
  v_strictMono_own : ∀ i (X : Fin n → ℝ), StrictMono (fun t => v i (Function.update X i t))

/-- **Remark 5** (private-values special case). Bidder `i`'s value depends only on
its own signal `Xᵢ`: whenever two profiles agree in coordinate `i`, the values
agree. Equivalently, `v i` factors through coordinate `i`. -/
def IsPrivateValues {n : ℕ} (E : SignalValueEnv n) : Prop :=
  ∀ i X X', X i = X' i → E.v i X = E.v i X'

/-- The realized value of bidder `i` at profile `X` (a convenience abbreviation;
the own signal is `X i` definitionally). -/
def SignalValueEnv.value {n : ℕ} (E : SignalValueEnv n) (i : Fin n) (X : Fin n → ℝ) : ℝ :=
  E.v i X

/- **Symmetric model** (future work). The notes' symmetric variant posits a single
value map `u` with `v i (Xᵢ, X₋ᵢ) = u (Xᵢ, X₋ᵢ)` and `u` symmetric in the rival
coordinates. A faithful Lean rendering carries a permutation-invariance hypothesis
restricted to permutations fixing `i` (or models the rivals as a `Multiset ℝ`);
this is left to the analytic layer and not required by the Def 7.1 / Def 7.2 /
Remark 6 scope formalized here. -/

/-! ### Welding Def 7.1 to Def 7.2 / Remark 6 -/

/-- The environment's raw signal weights satisfy `Affiliated` (Def 7.2). -/
def HasAffiliatedSignals {n : ℕ} (E : SignalValueEnv n) : Prop := Affiliated E.f

/-- Algebraic factorization of the signal weights into per-coordinate functions.
The name is retained for compatibility; a probability law and its marginals are
not supplied by this predicate. See `Factors` for the probability interpretation. -/
def HasIndependentSignals {n : ℕ} (E : SignalValueEnv n) : Prop := ∃ g, Factors E.f g

/-- Remark 6, environment form. Factorized signal weights are affiliated
(`factors_affiliated`), without requiring a probability interpretation. -/
theorem HasIndependentSignals.hasAffiliatedSignals {n : ℕ} {E : SignalValueEnv n}
    (h : HasIndependentSignals E) : HasAffiliatedSignals E := by
  obtain ⟨g, hg⟩ := h
  exact factors_affiliated hg

/-- Private values (`IsPrivateValues`) together with algebraically factorized signal weights
(`HasIndependentSignals`). The conventional IPV name is retained; probabilistic independence
requires the additional probability model described in the module documentation.
Affiliation constrains weights, while private values constrain value maps. -/
def IsIPV {n : ℕ} (E : SignalValueEnv n) : Prop := IsPrivateValues E ∧ HasIndependentSignals E

/-- The factorization half of `IsIPV` yields affiliation of the signal weights;
the private-values condition is not needed. -/
theorem IsIPV.hasAffiliatedSignals {n : ℕ} {E : SignalValueEnv n}
    (h : IsIPV E) : HasAffiliatedSignals E :=
  h.2.hasAffiliatedSignals

end Auction.Affiliation

end

end MathEconLib
