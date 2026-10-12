module

public import MathEconLib.Auction.Basic
public import Mathlib

/-! # Affiliation

This file defines affiliation, the positive-dependence condition of Milgrom–Weber,
and its relation to independent signals.

It contains three things:

* The `Affiliated` predicate on a joint density `f : (Fin n → ℝ) → ℝ`:
  for all signal profiles `x` and `y`,
  `f (x ⊔ y) * f (x ⊓ y) ≥ f x * f y`, where `⊔`/`⊓` are the pointwise
  (componentwise max/min) lattice operations on `Fin n → ℝ`.
* Equality for product densities: if `f` factors as a product of its
  per-coordinate factors, then the affiliation inequality holds with equality
  everywhere (`factors_affiliation_eq`), and hence `f` is affiliated
  (`factors_affiliated`). Independence is the boundary (knife-edge) case of the
  affiliation cone.
* The signal/value environment `SignalValueEnv`, carrying the signal
  bounds, the bidders' value functions, and their regularity (nonnegativity,
  continuity, monotonicity, and strict monotonicity in the bidder's own signal),
  together with the `IsPrivateValues` predicate isolating the private-values case.
-/

namespace MathEconLib

@[expose] public section

open Finset

namespace Auction.Affiliation

/-! ### The affiliation predicate -/

/-- A joint density `f : (Fin n → ℝ) → ℝ` is *affiliated*
when, for every pair of signal profiles `x` and `y`,
`f (x ⊔ y) * f (x ⊓ y) ≥ f x * f y`.

Here `⊔` and `⊓` are the pointwise lattice operations on `Fin n → ℝ` from
Mathlib's `Pi.lattice`, so `(x ⊔ y) i = max (x i) (y i)` and
`(x ⊓ y) i = min (x i) (y i)`.

The predicate is purely the algebraic inequality (positivity-free); that `f` is a
genuine density is carried separately by the downstream analytic layer. -/
def Affiliated {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x y : Fin n → ℝ, f (x ⊔ y) * f (x ⊓ y) ≥ f x * f y

/-! ### Equality for product densities -/

/-- The factorization predicate: `f` is the product of its
per-coordinate factors `g i`, i.e. `f x = ∏ i, g i (x i)` for every profile `x`.
This encodes (mutual) independence of the signals. -/
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

/-- If `f` factors as a product
of its per-coordinate factors, then the affiliation inequality holds
with *equality* everywhere:
`f (x ⊔ y) * f (x ⊓ y) = f x * f y` for all `x`, `y`.

For a product density, independence makes the affiliation inequality an equality.
No positivity is needed for this algebraic identity. -/
theorem factors_affiliation_eq {n : ℕ} {f : (Fin n → ℝ) → ℝ} {g : Fin n → ℝ → ℝ}
    (hf : Factors f g) :
    ∀ x y : Fin n → ℝ, f (x ⊔ y) * f (x ⊓ y) = f x * f y := by
  intro x y
  rw [hf, hf, hf, hf, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [Pi.sup_apply, Pi.inf_apply]
  exact mul_sup_inf_eq (g i) (x i) (y i)

/-- A density that factors as a product of its
per-coordinate factors is affiliated: the affiliation inequality follows from the
equality of `factors_affiliation_eq` via `ge_of_eq`. Independent private values
therefore give an independent special case of affiliation. -/
theorem factors_affiliated {n : ℕ} {f : (Fin n → ℝ) → ℝ} {g : Fin n → ℝ → ℝ}
    (hf : Factors f g) : Affiliated f := by
  intro x y
  exact ge_of_eq (factors_affiliation_eq hf x y)

/-! ### The signal/value environment -/

/-- An `n`-bidder signal/value model in which a signal
profile is `X : Fin n → ℝ` (coordinate `i` is bidder `i`'s own signal `Xᵢ`,
the others being the rivals' signals `X₋ᵢ`), and `v i X` is bidder `i`'s value
given the full profile `X`.

The fields record the regularity of the value functions:
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
  /-- The joint density of the signal profile `X = (X₁,…,Xₙ)`. -/
  f : (Fin n → ℝ) → ℝ
  /-- The signal density is nonnegative. -/
  f_nonneg : ∀ X, 0 ≤ f X
  /-- The signal density is supported on the box `[x_lo, x_hi]ⁿ`: it vanishes off it.
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

/-- The private-values special case: bidder `i`'s value depends only on
its own signal `Xᵢ`: whenever two profiles agree in coordinate `i`, the values
agree. Equivalently, `v i` factors through coordinate `i`. -/
def IsPrivateValues {n : ℕ} (E : SignalValueEnv n) : Prop :=
  ∀ i X X', X i = X' i → E.v i X = E.v i X'

/-- The realized value of bidder `i` at profile `X` (a convenience abbreviation;
the own signal is `X i` definitionally). -/
def SignalValueEnv.value {n : ℕ} (E : SignalValueEnv n) (i : Fin n) (X : Fin n → ℝ) : ℝ :=
  E.v i X

/- **Symmetric model** (future work). A symmetric variant would posit a single
value map `u` with `v i (Xᵢ, X₋ᵢ) = u (Xᵢ, X₋ᵢ)` and `u` symmetric in the rival
coordinates. A faithful Lean rendering carries a permutation-invariance hypothesis
restricted to permutations fixing `i` (or models the rivals as a `Multiset ℝ`);
this is left to the analytic layer and is not required for the affiliation and
independence results formalized here. -/

/-! ### Affiliation and independence in the signal/value environment -/

/-- The environment's signals are affiliated when their joint density is `Affiliated`. -/
def HasAffiliatedSignals {n : ℕ} (E : SignalValueEnv n) : Prop := Affiliated E.f

/-- The environment's signals are independent when the joint density factors as a product of
per-coordinate marginals. -/
def HasIndependentSignals {n : ℕ} (E : SignalValueEnv n) : Prop := ∃ g, Factors E.f g

/-- Independent signals are affiliated: the independent signal
structure sits on the boundary of the affiliation cone (`factors_affiliated`). -/
theorem HasIndependentSignals.hasAffiliatedSignals {n : ℕ} {E : SignalValueEnv n}
    (h : HasIndependentSignals E) : HasAffiliatedSignals E := by
  obtain ⟨g, hg⟩ := h
  exact factors_affiliated hg

/-- The independent private values (IPV) environment: private values (`IsPrivateValues`,
values depend only on own signal) together with independent signals. Affiliation and the
private-values restriction are ORTHOGONAL — affiliation constrains the signal density, private
values constrain the value maps — so IPV bundles both conditions. -/
def IsIPV {n : ℕ} (E : SignalValueEnv n) : Prop := IsPrivateValues E ∧ HasIndependentSignals E

/-- The IPV environment is the independent special (boundary) case of affiliation: its signals are
affiliated. Note it is the INDEPENDENCE half (not private values) that yields affiliation. -/
theorem IsIPV.hasAffiliatedSignals {n : ℕ} {E : SignalValueEnv n}
    (h : IsIPV E) : HasAffiliatedSignals E :=
  h.2.hasAffiliatedSignals

end Auction.Affiliation

end

end MathEconLib
