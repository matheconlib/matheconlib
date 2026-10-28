/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
module

import MathEconLib.Choice.Conditions
import MathEconLib.Choice.Matching.Completion
import MathEconLib.Choice.Matching.WeakSubstitutability
import Lean

/-!
General and matching conditions, including completion and substitutable
completability, must be available without preference constructors or a market.
The shared predicates retain their canonical ChoiceFunction names.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for entry in env.header.modules do
    if (`MathEconLib.Choice.Induced).isPrefixOf entry.module then
      logError m!"Choice conditions import preference constructors through {entry.module}."
    if (`MathEconLib.Matching).isPrefixOf entry.module then
      logError m!"Choice conditions import the matching layer through {entry.module}."

#check MathEconLib.Choice.ChoiceFunction.IsCompletionOf
#check MathEconLib.Choice.ChoiceFunction.SubstitutablyCompletable
#check MathEconLib.Choice.ChoiceFunction.HasConsistentSubstitutableCompletion

#check MathEconLib.Choice.ChoiceFunction.Substitutable
#check MathEconLib.Choice.ChoiceFunction.Chernoff
#check MathEconLib.Choice.ChoiceFunction.Consistent
#check MathEconLib.Choice.ChoiceFunction.SizeMonotone
#check MathEconLib.Choice.ChoiceFunction.UnitDemand
#check MathEconLib.Choice.ChoiceFunction.FiniteValued
#check MathEconLib.Choice.ChoiceFunction.PathIndependent
#check MathEconLib.Choice.ChoiceFunction.Fresh
#check MathEconLib.Choice.ChoiceFunction.UnilaterallySubstitutable
#check MathEconLib.Choice.ChoiceFunction.BilaterallySubstitutable
