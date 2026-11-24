/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Choice.Maximizers
public import MathEconLib.Welfare.Pareto

/-!
# Unanimous choice and Pareto efficiency

A unanimous choice maximizer is at least as good as every feasible alternative for every agent.
When agents disagree, an efficient alternative can be incomparable with another feasible one.
-/

@[expose] public section

namespace MathEconLib.Welfare

open Preferences

/-- A greatest feasible outcome for the unanimous preference is Pareto efficient. -/
theorem isParetoEfficient_of_mem_maximizers {I X : Type*} {R : I → Preference X}
    {F : Set X} {x : X} (hx : x ∈ Choice.maximizers (unanimousPreference R) F) :
    IsParetoEfficient R F x := by
  let := (unanimousPreference R).toPreorder
  exact IsGreatest.maximal (show IsGreatest F x from hx)

end MathEconLib.Welfare
