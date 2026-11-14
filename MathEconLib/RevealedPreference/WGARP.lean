/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLib.RevealedPreference.WGARP.Basic
public import MathEconLib.RevealedPreference.WGARP.Pairwise
public import MathEconLib.RevealedPreference.WGARP.FiniteCMU
public import MathEconLib.RevealedPreference.WGARP.Characterization
public import MathEconLib.RevealedPreference.WGARP.Choice

/-!
# Finite WGARP rationalization

For finite consumer data, WGARP is equivalent to rationalization by a
continuous, strictly increasing, sign-asymmetric numerical preference, and to
rationalization by a finite coherent coalitional multi-utility (CMU) function.
The construction applies the existing finite Afriat theorem to each observation
pair and combines the resulting utilities through finite minima and maxima.

`Basic` defines WGARP and numerical preference rationalization; `Pairwise` relates
WGARP to GARP on two observations. `FiniteCMU` supplies finite coalition evaluation,
`Characterization` assembles the rationalizer, and `Choice` expresses observed
membership using the existing choice-function API. These preferences may be cyclic.

See `docs/WGARP.md` for the exact scope and source attribution.
-/
