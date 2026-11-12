/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

import MathEconLib.RevealedPreference.AfriatGeometry

/-!
# Geometry-only monotonicity clients

These clients use nonnegative multipliers, including zero, and constrain only the
selected observation for a single support. No GARP or Reny rationalization API is imported.
-/

set_option linter.privateModule false

assert_not_exists MathEconLib.RevealedPreference.GraphGARP
assert_not_exists MathEconLib.RevealedPreference.RenyRationalizes

open MathEconLib.RevealedPreference

-- A support requires no restrictions on any other observation.
example {L : ℕ} {T : Type*} (U lam : T → ℝ) (p q : T → Bundle L) (t : T)
    (hp : Nonnegative (p t)) (hlam : 0 ≤ lam t) :
    Monotone (globalAfriatSupport U lam p q t) :=
  globalAfriatSupport_monotone U lam p q t hp hlam

-- A zero multiplier is accepted without a strict-positivity hypothesis.
example {L : ℕ} {T : Type*} (U : T → ℝ) (p q : T → Bundle L) (t : T)
    (hp : Nonnegative (p t)) :
    Monotone (globalAfriatSupport U (fun _ => 0) p q t) :=
  globalAfriatSupport_monotone U (fun _ => 0) p q t hp le_rfl

example {L : ℕ} {T : Type*} [Fintype T] [Nonempty T]
    (U lam : T → ℝ) (p q : T → Bundle L)
    (hp : ∀ t, Nonnegative (p t)) (hlam : ∀ t, 0 ≤ lam t) :
    Monotone (globalAfriatUtility U lam p q) :=
  globalAfriatUtility_monotone U lam p q hp hlam

-- The envelope client also instantiates every multiplier at zero.
example {L : ℕ} {T : Type*} [Fintype T] [Nonempty T]
    (U : T → ℝ) (p q : T → Bundle L) (hp : ∀ t, Nonnegative (p t)) :
    Monotone (globalAfriatUtility U (fun _ => 0) p q) :=
  globalAfriatUtility_monotone U (fun _ => 0) p q hp (fun _ => le_rfl)

#print axioms globalAfriatSupport_monotone
#print axioms globalAfriatUtility_monotone
