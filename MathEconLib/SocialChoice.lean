/-
Copyright (c) 2026 Ritik Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ritik Jain
-/
module

public import MathEconLib.SocialChoice.Arrow
public import MathEconLib.SocialChoice.Basic
public import MathEconLib.SocialChoice.Defs
public import MathEconLib.SocialChoice.Dictatorship
public import MathEconLib.SocialChoice.Majority
public import MathEconLib.SocialChoice.May

/-!
# Social choice

This module collects MathEconLib's social choice layer: social welfare functions on a domain of
preference profiles, their axioms, majority rule, and the theorems of Arrow and May. The theorems
take strict individual rankings as inputs (`linearProfiles N X`); society's preference may have
ties.

## Main topics

* Social welfare functions: `SocialWelfareFunction D`, a complete preference of society at each
  profile in `D`, with the Pareto, IIA, anonymity, neutrality and positive responsiveness axioms.
* Arrow's impossibility theorem: a Pareto, IIA social welfare function on linear profiles with
  three alternatives is dictatorial.
* Majority rule: the relation `majority P`, which need not be transitive (the Condorcet paradox).
* May's theorem: with two alternatives, the anonymous, neutral, positively responsive social
  welfare functions on linear profiles are majority rule, ties included.

## Tags

social choice, social welfare function, Arrow's theorem, May's theorem, majority rule, Condorcet
paradox
-/
