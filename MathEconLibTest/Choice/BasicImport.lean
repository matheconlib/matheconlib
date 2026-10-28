/-
Copyright (c) 2026 Scott Duke Kominers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Duke Kominers
-/
module

import MathEconLib.Choice.Basic
import Lean

/-!
The choice-function primitives must remain available without importing
optional conditions, preference constructions, or matching markets.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for entry in env.header.modules do
    if (`MathEconLib.Choice).isPrefixOf entry.module &&
        entry.module != `MathEconLib.Choice.Basic then
      logError m!"Choice.Basic imports an optional choice module: {entry.module}."
    if (`MathEconLib.Matching).isPrefixOf entry.module then
      logError m!"Choice.Basic imports the matching layer through {entry.module}."
  for name in #[`MathEconLib.Choice.ChoiceFunction.Consistent,
      `MathEconLib.Choice.ChoiceFunction.Substitutable,
      `MathEconLib.Choice.ChoiceFunction.SizeMonotone,
      `MathEconLib.Choice.ChoiceFunction.UnitDemand,
      `MathEconLib.Choice.ChoiceFunction.FiniteValued,
      `MathEconLib.Choice.ChoiceFunction.PathIndependent,
      `MathEconLib.Choice.ChoiceFunction.Chernoff] do
    if env.contains name then
      logError m!"Optional condition {name} is defined by Choice.Basic."
