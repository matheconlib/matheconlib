/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLib.RevealedPreference.Afriat
public import MathEconLib.RevealedPreference.Basic
public import MathEconLib.RevealedPreference.Choice
public import MathEconLib.RevealedPreference.GARP

/-!
# Finite revealed preference

Afriat's theorem connects GARP, positive-multiplier Afriat inequalities, and a continuous,
concave, strictly increasing utility rationalization of finite observations. The rationalizing
utility is an explicit finite lower envelope of affine functions. The choice interface embeds
observed utility maximization in the library's existing `ChoiceFunction` API.

See the leaf modules for hypotheses, sources, and proof provenance, and
`MathEconLibExamples.RevealedPreference` for checked applications.
-/
