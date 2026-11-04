/-
Copyright (c) 2026 Ritik Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ritik Jain
-/
module

public import MathEconLib.SocialChoice.Basic

/-!
# Dictatorship

A dictator for `F` on a domain `D` is an agent whose relation is the social relation at every
profile of `D` (`IsDictatorOn`).

## Main statements

* `IsDictatorOn.isParetoOn`, `IsDictatorOn.isIIAOn`: a rule with a dictator on `D` satisfies the
  Pareto property and independence of irrelevant alternatives on `D`, for every `D` (the easy half
  of Arrow's theorem).

## Implementation notes

Osborne and Rubinstein's societies are finite; neither statement here needs finiteness.

## References

Martin J. Osborne and Ariel Rubinstein (2023), *Models in Microeconomic Theory*, expanded second
edition, Open Book Publishers, Section 20.3 and Proposition 20.1.
[DOI: 10.11647/OBP.0361](https://doi.org/10.11647/OBP.0361).

## Tags

dictator, social welfare function, Pareto, independence of irrelevant alternatives
-/

@[expose] public section

namespace MathEconLib.SocialChoice

open MathEconLib.Preference

universe u v

variable {N : Type u} {X : Type v} {F : SocialWelfareFunction N X} {D : Set (Profile N X)}
  {i : N}

/-- A rule with a dictator satisfies the Pareto property. -/
theorem IsDictatorOn.isParetoOn (h : IsDictatorOn F D i) : IsParetoOn F D :=
  fun _ hP x y hxy => by rw [h hP]; exact hxy i

/-- A rule with a dictator is independent of irrelevant alternatives. -/
theorem IsDictatorOn.isIIAOn (h : IsDictatorOn F D i) : IsIIAOn F D :=
  fun _ hP _ hQ x y hxy => by rw [h hP, h hQ]; exact (hxy i).1

end MathEconLib.SocialChoice
