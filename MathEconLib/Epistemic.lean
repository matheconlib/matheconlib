/-
Copyright (c) 2026 Ben Eltschig, Jujian Zhang, Ruiz Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig, Jujian Zhang, Ruiz Chen
-/
module

public import MathEconLib.Epistemic.Agreement
public import MathEconLib.Epistemic.CommonBelief
public import MathEconLib.Epistemic.Posterior

/-!
# Knowledge and belief under information partitions

Agents share a measurable state space and each has an information partition and a prior.
`Posterior` defines an agent's posterior probability of an event at a state. `Agreement` proves
Aumann's agreement theorem: posteriors that are common knowledge are equal under a common prior.
`CommonBelief` defines `p`-belief, evident belief and common `p`-belief, and proves that
posteriors that are common `p`-belief differ by at most `2 * (1 - p)`.

Information partitions are Mathlib's `Setoid.Partitions`; the general facts about them used here
are in `MathEconLib.ForMathlib.Order.SetoidPartition` and
`MathEconLib.ForMathlib.MeasureTheory.SetoidPartition`.
-/
