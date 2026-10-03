/-
Copyright (c) 2026 Ruiz Chen, Scott Duke Kominers, Daniel Lyng, Jujian Zhang. All rights reserved.
Released under license as described in the file LICENSE.
Authors: Ruiz Chen, Scott Duke Kominers, Daniel Lyng, Jujian Zhang
-/
module

public import MathEconLib.Mechanism.Auctions.AllPurchase.Spec
public import MathEconLib.Mechanism.Core.Bayesian
public import MathEconLib.Mechanism.Core.SolutionConcepts
public import MathEconLib.Mechanism.Core.Strategic

/-!
# Mechanisms, incentives, and induced games

Mechanisms assign outcomes and signed transfers to action profiles. Quasilinear environments
evaluate these outcomes at true type profiles and support prior-free notions of incentive
compatibility, individual rationality, efficiency, and budget balance. All-purchase specifications
describe allocation and payment rules for auctions in which every agent pays.

Direct mechanisms induce strategic games in which dominant-strategy incentive compatibility is
equivalent to dominance of truthful reporting. Mechanisms also induce Bayesian games whose payoffs
evaluate the same utility at the realized true type profile. Fixing those types recovers the
strategic utility game. Action translation commutes with both induced-game constructions.

## Main definitions

* `Mechanism`: Outcome and signed-transfer rules for dependent action profiles.
* `QuasilinearEnvironment`: Values at true type profiles and quasilinear utility.
* `DirectMechanism.IsDSIC`: Dominant-strategy incentive compatibility without a type prior.
* `QuasilinearEnvironment.utilityGame`: The strategic game induced at a fixed true type profile.
* `Mechanism.inducedBayesianGame`: The Bayesian game with the mechanism's quasilinear utility.
* `AllPurchaseSpec`: Allocation and payment requirements for an all-purchase auction.

## Main statements

* `DirectMechanism.isDSIC_iff_isDominant`: Truthful dominance characterizes incentive compatibility.
* `DirectMechanism.IsDSIC.isNash`: Incentive compatibility gives a truthful Nash equilibrium.
* `Mechanism.inducedBayesianGame_comap`: Translating mechanism actions translates its Bayesian game.

## Tags

mechanism design, quasilinear utility, incentive compatibility, dominant strategies, strategic
games, bayesian games, all-purchase auctions
-/
