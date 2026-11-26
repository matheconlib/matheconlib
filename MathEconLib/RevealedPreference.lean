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
public import MathEconLib.RevealedPreference.GARP
public import MathEconLib.RevealedPreference.WGARP

/-!
# Finite revealed preference

Afriat's theorem connects GARP, positive-multiplier Afriat inequalities, and a continuous,
concave, strictly increasing utility rationalization of finite observations. The rationalizing
utility is an explicit finite lower envelope of affine functions. The choice interface embeds
observed utility maximization in the library's existing `ChoiceFunction` API.

`AfriatGeometry` contains the certificate definitions and affine-envelope construction,
independently of GARP. `GARP` constructs certificates from the revealed-preference graph;
`Afriat` combines these ingredients into the economic equivalences.

`WGARP` reuses finite Afriat on each pair of observations to characterize WGARP by
continuous, strictly increasing, sign-asymmetric numerical preferences and finite
coherent coalitional multi-utility. Its choice interface accommodates cyclic preferences.

See the leaf modules for hypotheses, sources, and proof provenance, and
`MathEconLibExamples.RevealedPreference` for checked applications.
-/
