/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import MathEconLib.Preferences.Basic
public import MathEconLib.Preferences.Complete
public import MathEconLib.Preferences.Refinement
public import MathEconLib.Preferences.Representation.Basic
public import MathEconLib.Preferences.Representation.Finite

/-!
# Preferences and ordinal utility

This module collects MathEconLib's preference layer: preferences over arbitrary alternatives,
complete preferences, and their ordinal utility representations. Preferences need not be complete,
and utilities may take values in any preorder.

## Main topics

* Preferences: `Preference`, strict preference, indifference, and the correspondence with
  preorders.
* Complete preferences: `CompletePreference`, total preorders, and linear orders.
* Ordinal utility: `Preference.IsRepresentedBy`, preferences determined by utilities, and the link
  between greatest alternatives on a menu and utility maximization.
* Finite alternatives: natural-number representations of complete preferences.

## Notation

The following notation is scoped to `MathEconLib.Preferences`.

* `x ≼[R] y` — `y` is weakly preferred to `x`.
* `x ≺[R] y` — `y` is strictly preferred to `x`.
* `x ~[R] y` — `x` and `y` are indifferent.

Larger utilities are better: a utility `u` represents `R` when `x ≼[R] y ↔ u x ≤ u y`.

## Tags

preference, complete preference, ordinal utility, finite representation
-/
