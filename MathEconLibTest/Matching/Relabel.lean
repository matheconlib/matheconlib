/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLib
import MathEconLibExamples.Matching.NamedMarriage

/-!
Public-API checks for relabeling preferences and partial assignments. The named worked example
supplies the end-to-end application. These laws also apply to infinite carriers and arbitrary
outside-option positions; no rank-profile or universal-acceptability assumption is introduced.
-/

namespace MathEconLibTest.Matching.Relabel

open MathEconLib.Matching

variable {M W M' W' M'' W'' : Type*}

example (μ : M ≃. W) : μ.relabel (Equiv.refl M) (Equiv.refl W) = μ :=
  PEquiv.relabel_refl μ

example (mkt : MarriageMarket M W) :
    mkt.relabel (Equiv.refl M) (Equiv.refl W) = mkt := mkt.relabel_refl

example (μ : M ≃. W) (eM : M ≃ M') (eW : W ≃ W')
    (fM : M' ≃ M'') (fW : W' ≃ W'') :
    (μ.relabel eM eW).relabel fM fW = μ.relabel (eM.trans fM) (eW.trans fW) :=
  μ.relabel_trans eM eW fM fW

example (mkt : MarriageMarket M W) (eM : M ≃ M') (eW : W ≃ W')
    (fM : M' ≃ M'') (fW : W' ≃ W'') :
    (mkt.relabel eM eW).relabel fM fW = mkt.relabel (eM.trans fM) (eW.trans fW) :=
  mkt.relabel_trans eM eW fM fW

example (eM : M ≃ M') (eW : W ≃ W') : (⊥ : M ≃. W).relabel eM eW = ⊥ := by
  ext m
  simp

example (mkt : MarriageMarket M W) (μ : M ≃. W) (eM : M ≃ M') (eW : W ≃ W') :
    (mkt.relabel eM eW).IsStableMatching (μ.relabel eM eW) ↔ mkt.IsStableMatching μ :=
  mkt.isStableMatching_relabel μ eM eW

example : MathEconLibExamples.Matching.NamedMarriage.market.IsStableMatching
    MathEconLibExamples.Matching.NamedMarriage.outcome :=
  MathEconLibExamples.Matching.NamedMarriage.outcome_stable

#print axioms MarriageMarket.isStableMatching_relabel
#print axioms MarriageMarket.relabel_trans
#print axioms PEquiv.relabel_trans
#print axioms MathEconLibExamples.Matching.NamedMarriage.outcome_stable

end MathEconLibTest.Matching.Relabel
