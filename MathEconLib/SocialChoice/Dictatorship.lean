/-
Copyright (c) 2026 Ritik Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ritik Jain
-/
module

public import MathEconLib.SocialChoice.Basic

/-!
# Dictatorship

A rule with a dictator is Pareto and IIA on every domain (Osborne and Rubinstein, Section 20.3).

## Main statements

* `IsDictator.isPareto`: a rule with a dictator satisfies the Pareto property.
* `IsDictator.isIIA`: a rule with a dictator is independent of irrelevant alternatives.
-/

@[expose] public section

namespace MathEconLib.SocialChoice

open MathEconLib.Preferences

universe u v

variable {N : Type u} {X : Type v} {D : Set (Profile N fun _ => X)}
  {F : SocialWelfareFunction D} {i : N}

/-- A rule with a dictator satisfies the Pareto property. -/
theorem IsDictator.isPareto (h : IsDictator F i) : IsPareto F :=
  fun P x y hxy => by rw [h P]; exact hxy i

/-- A rule with a dictator is independent of irrelevant alternatives. -/
theorem IsDictator.isIIA (h : IsDictator F i) : IsIIA F :=
  fun P Q x y hxy => by rw [h P, h Q]; exact (hxy i).1

end MathEconLib.SocialChoice
