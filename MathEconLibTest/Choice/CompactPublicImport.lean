/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
import MathEconLib.Choice

/-!
# Public compact-attainment interface

Import only the choice umbrella and pin compact attainment with closed upper contours,
without a separation axiom.
-/

open MathEconLib.Choice MathEconLib.Preferences

example {X : Type*} [TopologicalSpace X]
    (R : CompletePreference X) {S : Set X} (hS : IsCompact S) (hne : S.Nonempty)
    (hclosed : ∀ x ∈ S, IsClosed {y | R.le x y}) :
    (maximizers R.toPreference S).Nonempty :=
  maximizers_nonempty_of_isCompact R hS hne hclosed
