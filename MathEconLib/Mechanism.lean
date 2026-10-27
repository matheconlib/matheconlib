/-
Copyright (c) 2026 Ruiz Chen, Scott Duke Kominers, Daniel Lyng, Jujian Zhang,
Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiz Chen, Scott Duke Kominers, Daniel Lyng, Jujian Zhang, Bo Cowgill
-/
module

public import MathEconLib.Mechanism.Auctions.AllPurchase.Spec
public import MathEconLib.Mechanism.Core.Bayesian
public import MathEconLib.Mechanism.Core.BayesianIC
public import MathEconLib.Mechanism.Core.SolutionConcepts
public import MathEconLib.Mechanism.Core.Strategic

/-!
# Mechanisms, incentives, and induced games

Mechanisms assign outcomes and signed monetary transfers to action profiles without specifying
preferences. Quasilinear environments evaluate outcomes at true type profiles and add the signed
transfer to outcome value. The incentive, participation and welfare APIs here use that utility
model; incentive compatibility as an economic concept does not require quasilinearity. Budget
balance and revenue accounting depend only on transfers. All-purchase specifications describe
allocation and payment rules for auctions in which every agent pays.

Direct mechanisms induce strategic games in which dominant-strategy incentive compatibility is
equivalent to dominance of truthful reporting. Mechanisms also induce Bayesian games whose payoffs
evaluate the same utility at the realized true type profile. Fixing those types recovers the
strategic utility game. Action translation commutes with both induced-game constructions.
Quasilinear conditional Bayesian IC permits correlated types, interdependent values and
multidimensional type spaces. Its full-space pointwise version implies truthful Bayesian Nash
equilibrium under the stated analytic hypotheses.

## Main definitions

* `Mechanism`: Outcome and signed-transfer rules for dependent action profiles.
* `QuasilinearEnvironment`: Values at true type profiles and quasilinear utility.
* `DirectMechanism.IsDSIC`: Quasilinear dominant-strategy IC without a type prior.
* `DirectMechanism.Quasilinear.IsBICOn`: Quasilinear conditional Bayesian IC on declared type/report
  sets.
* `QuasilinearEnvironment.utilityGame`: The strategic game induced at a fixed true type profile.
* `Mechanism.inducedBayesianGame`: The Bayesian game with the mechanism's quasilinear utility.
* `AllPurchaseSpec`: Allocation and payment requirements for an all-purchase auction.

## Main statements

* `DirectMechanism.isDSIC_iff_isDominant`: Truthful dominance characterizes incentive compatibility.
* `DirectMechanism.IsDSIC.isNash`: Incentive compatibility gives a truthful Nash equilibrium.
* `DirectMechanism.Quasilinear.IsBIC.isBNE`: Full-space pointwise BIC gives a truthful Bayesian
  equilibrium.
* `Mechanism.inducedBayesianGame_comap`: Translating mechanism actions translates its Bayesian game.

## Tags

mechanism design, quasilinear utility, incentive compatibility, dominant strategies, strategic
games, bayesian games, all-purchase auctions
-/
