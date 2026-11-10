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

* `IsDictatorOn.isParetoOn`: a rule with a dictator satisfies the Pareto property.
* `IsDictatorOn.isIIAOn`: a rule with a dictator is independent of irrelevant alternatives.
-/

@[expose] public section

namespace MathEconLib.SocialChoice

open MathEconLib.Preferences

universe u v

variable {N : Type u} {X : Type v} {F : SocialWelfareFunction N X} {D : Set (Profile N fun _ => X)}
  {i : N}

/-- A rule with a dictator satisfies the Pareto property. -/
theorem IsDictatorOn.isParetoOn (h : IsDictatorOn F D i) : IsParetoOn F D :=
  fun _ hP x y hxy => by rw [h hP]; exact hxy i

/-- A rule with a dictator is independent of irrelevant alternatives. -/
theorem IsDictatorOn.isIIAOn (h : IsDictatorOn F D i) : IsIIAOn F D :=
  fun _ hP _ hQ x y hxy => by rw [h hP, h hQ]; exact (hxy i).1

end MathEconLib.SocialChoice
