import MathEconLib.Choice.Conditions.WithPartners.Basic
import Lean

/-!
Conditions involving matching partners, including completion and substitutable
completability, must be available without preference constructors or a market.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for entry in env.header.modules do
    if (`MathEconLib.Choice.Induced).isPrefixOf entry.module then
      logError m!"Partner conditions import preference constructors through {entry.module}."
    if (`MathEconLib.Matching).isPrefixOf entry.module then
      logError m!"Partner conditions import the matching layer through {entry.module}."

#check MathEconLib.Choice.ChoiceFunction.IsCompletionOf
#check MathEconLib.Choice.ChoiceFunction.SubstitutablyCompletable
#check MathEconLib.Choice.ChoiceFunction.HasConsistentSubstitutableCompletion
