/-
Copyright (c) 2026 Frederik Glitzner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frederik Glitzner
-/
module

public import MathEconLib.Matching.Classical.Roommates.Basic
public import MathEconLib.Matching.Classical.Roommates.NonExistence

/-!
# The stable roommates problem

Public entry point for the one-sided roommates model. Agents rank all agents,
including themselves; an agent's own position is its outside option. Matchings
are involutions, with fixed points as unmatched agents.

`Roommates.Basic` defines markets, matchings, and stability.
`Roommates.NonExistence` shows that, unlike in the marriage market, a stable
matching need not exist.
-/

@[expose] public section
