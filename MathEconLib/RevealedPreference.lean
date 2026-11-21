/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLib.RevealedPreference.Afriat
public import MathEconLib.RevealedPreference.AfriatGeometry
public import MathEconLib.RevealedPreference.Basic
public import MathEconLib.RevealedPreference.Choice
public import MathEconLib.RevealedPreference.Equilibrium
public import MathEconLib.RevealedPreference.EquilibriumAlternative
public import MathEconLib.RevealedPreference.EquilibriumAxiom
public import MathEconLib.RevealedPreference.EquilibriumBounds
public import MathEconLib.RevealedPreference.EquilibriumElimination
public import MathEconLib.RevealedPreference.EquilibriumWelfare
public import MathEconLib.RevealedPreference.GARP
public import MathEconLib.RevealedPreference.LocalNonsatiation

/-!
# Finite revealed preference

Afriat's theorem connects GARP, positive-multiplier Afriat inequalities, and a continuous,
concave, strictly increasing utility rationalization of finite observations. The rationalizing
utility is an explicit finite lower envelope of affine functions. The choice interface embeds
observed utility maximization in the library's existing `ChoiceFunction` API.

`AfriatGeometry` contains the certificate definitions and affine-envelope construction,
independently of GARP. `GARP` constructs certificates from the revealed-preference graph;
`Afriat` combines these ingredients into the economic equivalences.

`Equilibrium` applies finite Afriat consumer by consumer to latent market-clearing
allocations, characterizing exchange-equilibrium rationalization by joint certificates.
`LocalNonsatiation` supplies ordinary utility-maximization necessity and budget exhaustion.
`EquilibriumElimination` characterizes the same market observations by a finite ordinal
disjunction of fully eliminated observable inequalities, using the generic mixed
weak/strict elimination in `ForMathlib.LinearInequalities`. `EquilibriumWelfare`
retains the certified allocation and proves the classical reciprocal-multiplier
welfare maximization and Pareto-efficiency implication.

See the leaf modules for hypotheses, sources, and proof provenance, and
`MathEconLibExamples.RevealedPreference` for checked applications.
-/
