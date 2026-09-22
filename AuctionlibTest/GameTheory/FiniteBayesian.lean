/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Auctionlib.GameTheory.Strategic.Bayesian.FiniteMeasurable

/-!
# Finite Bayesian equilibrium examples

An asymmetric game has different finite type spaces and infinite action spaces for its players. The
examples distinguish positive-probability and null types, identify the same equilibrium under
finite and measurable priors, and show the direction of equilibrium transport under action maps.

## Main definitions

* `asymmetric`: a two-player game with different finite type spaces and infinite action spaces.
* `prior`: a common prior concentrated at the lowest type profile.
* `original` and `restriction`: a one-player game and a restriction to a suboptimal action.

## Main statements

* `asymmetric_isBNEFin`: best responses on positive-probability types form an equilibrium.
* `original_isBNEFin_comapActions`, `original_not_isBNEFin_mapPureStrategy`: restricting actions
  need not preserve equilibrium in the reverse direction.

## Tags

bayesian game, finite types, null types, equilibrium, action restriction
-/

@[expose] public noncomputable section

open Auctionlib.GameTheory Auctionlib.Probability Function MeasureTheory

namespace AuctionlibTest.FiniteBayesian

/-- Player `true` has two types, and player `false` has three. -/
def Theta (i : Bool) := Fin (if i then 2 else 3)

/-- Player `true` chooses a natural number, and player `false` chooses an integer. -/
def Action (i : Bool) := if i then ℕ else ℤ

/-- Each player has finitely many types. -/
instance (i : Bool) : Fintype (Theta i) := by cases i <;> dsimp [Theta] <;> infer_instance

/-- Equality of each player's types is decidable. -/
instance (i : Bool) : DecidableEq (Theta i) := by cases i <;> dsimp [Theta] <;> infer_instance

/-- Equality of each player's actions is decidable. -/
instance (i : Bool) : DecidableEq (Action i) := by cases i <;> dsimp [Action] <;> infer_instance

/-- Every subset of a player's type space is measurable. -/
instance (i : Bool) : MeasurableSpace (Theta i) := ⊤

/-- Every singleton type is measurable. -/
instance (i : Bool) : MeasurableSingletonClass (Theta i) := ⟨fun _ ↦ trivial⟩

/-- Every subset of a player's action space is measurable. -/
instance (i : Bool) : MeasurableSpace (Action i) := ⊤

/-- The type profile assigning zero to each player. -/
def thetaZero (i : Bool) : Theta i := ⟨0, by cases i <;> decide⟩

/-- The action zero in each player's action space. -/
def zeroAction (i : Bool) : Action i := by cases i <;> dsimp [Action] <;> exact 0

/-- Each player earns one from its zero action and zero otherwise. -/
def asymmetric : BayesianGame Bool Theta Action ℝ where
  payoff i a _ := if a i = zeroAction i then 1 else 0

/-- The common prior is degenerate at the lowest types. -/
def prior : FinDist (∀ i, Theta i) := FinDist.pure thetaZero

/-- All types choose their player's payoff-maximizing action. -/
def strategy : asymmetric.PureStrategy := fun i _ ↦ zeroAction i

/-- Each player's zero type has marginal probability one. -/
example (i : Bool) : prior.marginalD i (thetaZero i) = 1 := by simp [prior]

/-- A null type has no finite interim incentive constraint. -/
example (a : Action true) :
    asymmetric.interimPayoffActionFin prior true ⟨1, by decide⟩ a strategy = 0 := by
  apply asymmetric.interimPayoffActionFin_eq_zero_of_marginal_not_pos
  have hn : thetaZero true ≠ (⟨1, by decide⟩ : Theta true) := by
    intro h
    have hv := congrArg Fin.val h
    norm_num [thetaZero] at hv
  change ¬ 0 < (FinDist.pure thetaZero).marginalD true ⟨1, by decide⟩
  rw [FinDist.marginalD_pure, if_neg hn]
  exact lt_irrefl 0

/-- Both players maximize payoff at the only positive-probability type. -/
theorem asymmetric_isBNEFin : asymmetric.IsBNEFin prior strategy := by
  rw [asymmetric.isBNEFin_iff]
  intro i t hp a
  have ht : thetaZero i = t := by
    by_contra h
    simp [prior, h] at hp
  subst t
  rw [show prior = FinDist.pure thetaZero from rfl]
  rw [asymmetric.interimPayoffActionFin_pure, asymmetric.interimPayoffActionFin_pure]
  simp only [asymmetric, update_self, strategy]
  split_ifs <;> norm_num

/-- The same profile satisfies the measurable equilibrium definition. -/
example : asymmetric.IsBNE prior.toMeasure (asymmetric.toMeasurableStrategy strategy) :=
  (asymmetric.isBNEFin_iff_isBNE prior strategy).mp asymmetric_isBNEFin

/-- Finite and integral ex-ante payoffs agree for heterogeneous infinite action spaces. -/
example (i : Bool) : asymmetric.exAntePayoffFin prior i strategy =
    asymmetric.exAntePayoff prior.toMeasure i (asymmetric.toMeasurableStrategy strategy) :=
  asymmetric.exAntePayoffFin_eq_exAntePayoff prior i strategy

/-- A many-to-one action map preserves equilibrium in the pullback direction. -/
example (s : (asymmetric.comapActions (fun i (_ : Bool) ↦ zeroAction i)).PureStrategy) :
    (asymmetric.comapActions (fun i (_ : Bool) ↦ zeroAction i)).IsBNEFin prior s := by
  apply asymmetric.isBNEFin_comapActions
  exact asymmetric_isBNEFin

/-- A one-player game strictly prefers zero to every other natural number. -/
def original : BayesianGame Unit (fun _ ↦ Unit) (fun _ ↦ ℕ) ℝ where
  payoff _ a _ := if a () = 0 then 1 else 0

/-- A restricted action map makes only the suboptimal action available. -/
def restriction : ∀ _ : Unit, Bool → ℕ := fun _ _ ↦ 1

/-- Restriction is noninjective. -/
example : restriction () false = restriction () true := rfl

/-- Choosing `false` is an equilibrium when both restricted actions give the same payoff. -/
theorem original_isBNEFin_comapActions : (original.comapActions restriction).IsBNEFin
    (FinDist.pure (fun _ ↦ ())) (fun _ _ ↦ false) := by
  rw [BayesianGame.isBNEFin_iff]
  intro i t _ a
  cases i
  cases t
  rw [BayesianGame.interimPayoffActionFin_pure, BayesianGame.interimPayoffActionFin_pure]
  simp [original, BayesianGame.comapActions, restriction]

/-- An equilibrium in the restricted game need not be an equilibrium in the original game. -/
theorem original_not_isBNEFin_mapPureStrategy : ¬ original.IsBNEFin (FinDist.pure (fun _ ↦ ()))
    (original.mapPureStrategy restriction (fun _ _ ↦ false)) := by
  intro h
  have hc := (original.isBNEFin_iff _ _).mp h () () (by simp) 0
  rw [original.interimPayoffActionFin_pure, original.interimPayoffActionFin_pure] at hc
  norm_num [original, BayesianGame.mapPureStrategy, restriction] at hc

end AuctionlibTest.FiniteBayesian
