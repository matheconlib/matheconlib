/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
module

public import MathEconLib.Matching.Classical.Marriage.DeferredAcceptance
public import MathEconLib.Matching.Classical.Marriage.DeferredAcceptanceComputable
public import MathEconLib.Matching.Classical.Marriage.DeferredAcceptanceFixedPoints
public import MathEconLib.Matching.Classical.Marriage.FixedPointConvergence
public import MathEconLib.Matching.Classical.Marriage.LoneWolf
public import MathEconLib.Matching.Classical.Marriage.StableOrder

/-!
# The classical marriage market

Public entry point for the marriage model, realized as an instance
in the matching with contracts framework. Men are sellers, women are buyers,
and contracts are pairs `M × W`. Preferences are orders on optional partners,
with `none` representing the outside option. No global preference order is
installed on bare `PEquiv`.

The components separate basic economic definitions and direct classical facts,
preferences and their induced choice, the embedding into contracts, stable
existence, the symmetric extrema, fixed-point convergence, lone wolf results,
and the stable-matching lattice. `Marriage.DeferredAcceptance` develops the
direct proposal algorithm; `Marriage.DeferredAcceptanceFixedPoints` relates
its terminal outputs to the contracts fixed points; and
`Marriage.DeferredAcceptanceComputable` supplies executable algorithms.
-/

@[expose] public section

