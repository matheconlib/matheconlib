/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Logic.Function.Basic

/-!
# Dependent profiles

A profile assigns one input to each agent, allowing different agents to have different input types.
The type `I` indexes agents, and `X i` is the type of inputs for agent `i`, such as private types,
reports, or actions.

## Main definitions

* `Auctionlib.Mechanism.Profile`: a dependent profile containing one input for every agent.

## Tags

profiles, agents, mechanism design
-/

@[expose] public section

universe uI uX

namespace Auctionlib.Mechanism

/-- A dependent profile assigning one value of type `X i` to every agent `i : I`. -/
abbrev Profile {I : Type uI} (X : I → Type uX) := ∀ i, X i

end Auctionlib.Mechanism

end
