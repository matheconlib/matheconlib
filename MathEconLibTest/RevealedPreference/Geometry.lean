/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

import MathEconLib.RevealedPreference.AfriatGeometry

/-!
# Independent Afriat geometry clients

This architectural regression deliberately imports the geometry module alone.
Envelope interpolation and halfspace maximization do not depend on GARP, positive
prices, or nonnegative observed choices. Strict increase adds positive prices.
-/

set_option linter.privateModule false

assert_not_exists MathEconLib.RevealedPreference.GraphGARP

open MathEconLib.RevealedPreference

example {L : ℕ} {T : Type*} [Fintype T] [Nonempty T]
    (U lam : T → ℝ) (p q : T → Bundle L) :
    Continuous (globalAfriatUtility U lam p q) ∧
      ConcaveOn ℝ Set.univ (globalAfriatUtility U lam p q) :=
  ⟨globalAfriatUtility_continuous U lam p q, globalAfriatUtility_concaveOn U lam p q⟩

example {L : ℕ} {T : Type*} [Fintype T] [Nonempty T]
    (U lam : T → ℝ) (p q : T → Bundle L)
    (hA : AfriatInequalities U lam p q) (t : T) :
    globalAfriatUtility U lam p q (q t) = U t :=
  globalAfriatUtility_eq_observed U lam p q hA t

example {L : ℕ} {T : Type*} [Fintype T] [Nonempty T]
    (U lam : T → ℝ) (p q : T → Bundle L)
    (hA : AfriatInequalities U lam p q) (t : T) (hlam : 0 ≤ lam t)
    {y : Bundle L} (hy : dot (p t) y ≤ dot (p t) (q t)) :
    globalAfriatUtility U lam p q y ≤ globalAfriatUtility U lam p q (q t) :=
  globalAfriatUtility_le_observed_of_dot_le U lam p q hA t hlam hy

example {L : ℕ} {T : Type*} [Fintype T] [Nonempty T]
    (U lam : T → ℝ) (p q : T → Bundle L)
    (hA : AfriatInequalities U lam p q) (t : T) (hlam : 0 < lam t)
    {y : Bundle L} (hy : dot (p t) y < dot (p t) (q t)) :
    globalAfriatUtility U lam p q y < globalAfriatUtility U lam p q (q t) :=
  globalAfriatUtility_lt_observed_of_dot_lt U lam p q hA t hlam hy

example {L : ℕ} {T : Type*} [Fintype T] [Nonempty T]
    (U lam : T → ℝ) (p q : T → Bundle L)
    (hp : ∀ t i, 0 < p t i) (hpos : PositiveMultipliers lam) :
    StrictMono (globalAfriatUtility U lam p q) :=
  strictlyIncreasing_iff_strictMono.mp
    (globalAfriatUtility_strictlyIncreasing U lam p q hp hpos)
