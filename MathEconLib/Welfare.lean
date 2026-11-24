/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Welfare.Choice
public import MathEconLib.Welfare.Pareto
public import MathEconLib.Welfare.Representation
public import MathEconLib.Welfare.Transport

/-!
# Ordinal Pareto efficiency

Choose the agents whose preferences count and the set of feasible outcomes. Use
`IsParetoEfficient` to exclude improvements that benefit someone with everyone weakly better
off. Use `IsWeaklyParetoEfficient` to exclude improvements that strictly benefit everyone.
Both predicates require the candidate to be feasible.
-/
