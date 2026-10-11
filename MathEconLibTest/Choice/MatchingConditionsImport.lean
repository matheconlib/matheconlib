import MathEconLib.Choice.Conditions.Matching.Completion
import MathEconLib.Choice.Conditions.Matching.FiniteValued
import MathEconLib.Choice.Conditions.Matching.IrrelevanceOfRejectedContracts
import MathEconLib.Choice.Conditions.Matching.LawOfAggregateDemand
import MathEconLib.Choice.Conditions.Matching.PathIndependence
import MathEconLib.Choice.Conditions.Matching.Substitutability
import MathEconLib.Choice.Conditions.Matching.UnitDemand
import MathEconLib.Choice.Conditions.Matching.WeakSubstitutability
import Lean

/-!
Matching condition topic imports, including completion and substitutable
completability, must be available without preference constructors or a market.
The shared predicates retain their canonical ChoiceFunction names.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for entry in env.header.modules do
    if (`MathEconLib.Choice.Induced).isPrefixOf entry.module then
      logError m!"Matching condition topics import preference constructors through {entry.module}."
    if (`MathEconLib.Matching).isPrefixOf entry.module then
      logError m!"Matching condition topics import the matching layer through {entry.module}."

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
