/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import MathEconLib.GameTheory.Strategic.Existence
public import Mathlib.Data.Set.BooleanAlgebra

/-!
# Nash equilibrium with ordered payoffs

These examples illustrate how Nash equilibrium depends on the order structure of payoffs. In a
natural-valued game, the action with the larger payoff is a Nash equilibrium. With set-valued
payoffs ordered by inclusion, singleton payoffs can be incomparable, so the absence of a strictly
profitable deviation does not imply the weak payoff inequalities required for Nash equilibrium.

A continuous game whose actions and payoffs are strictly positive real numbers has a pure Nash
equilibrium by the ordered-payoff existence theorem, without requiring a distinguished zero payoff.

## Main definitions

* `ordinalGame`: Natural-valued payoffs for two actions.
* `incomparableGame`: Singleton-set payoffs ordered by inclusion.
* `Positive.Action`, `Positive.Payoff`, and `Positive.game`: A continuous game with actions and
  payoffs in the strictly positive reals.

## Main statements

* `ordinalGame_isNash`: The action with the larger natural payoff is a Nash equilibrium.
* `incomparableGame_not_lt`: No action strictly improves on choosing `false`.
* `incomparableGame_not_isNash`: Incomparability prevents the required weak payoff inequality.
* `Positive.exists_isNash`: The positive-payoff game has a pure Nash equilibrium.

## Tags

nash equilibrium, ordered payoff, partial order, incomparable payoffs
-/

@[expose] public section

open MathEconLib.GameTheory

namespace MathEconLibTest.GameTheory.OrderedPayoffs

/-- Choosing `true` yields one, and choosing `false` yields zero. -/
def ordinalGame : StrategicGame Unit (fun _ => Bool) ℕ where
  payoff _ a := if a () then 1 else 0

/-- The action with payoff one weakly dominates both actions. -/
theorem ordinalGame_isNash : ordinalGame.IsNash (fun _ => true) := by
  rw [StrategicGame.isNash_iff]
  intro i b
  cases i
  cases b <;> simp [ordinalGame]

/-- A player's payoff is the singleton containing their chosen action, ordered by inclusion. -/
def incomparableGame : StrategicGame Unit (fun _ => Bool) (Set Bool) where
  payoff _ a := {a ()}

/-- Neither action strictly improves on the singleton payoff from choosing `false`. -/
theorem incomparableGame_not_lt (b : Bool) :
    ¬ incomparableGame.payoff () (fun _ => false) <
      incomparableGame.payoff () (Function.update (fun _ => false) () b) := by
  cases b
  · simp [incomparableGame]
  · intro h
    have hmem := h.le (by simp [incomparableGame] :
      false ∈ incomparableGame.payoff () (fun _ => false))
    simp [incomparableGame] at hmem

/-- The alternative singleton is not below the incumbent singleton, so the profile is not Nash. -/
theorem incomparableGame_not_isNash : ¬ incomparableGame.IsNash (fun _ => false) := by
  rw [StrategicGame.isNash_iff]
  intro h
  have hmem := h () true (by simp [incomparableGame] :
    true ∈ incomparableGame.payoff () (Function.update (fun _ => false) () true))
  simp [incomparableGame] at hmem

namespace Positive

/-- A player chooses an action between one and two. -/
abbrev Action := Set.Icc (1 : ℝ) 2

/-- Payoffs are strictly positive real numbers, with their inherited order. -/
abbrev Payoff := Set.Ioi (0 : ℝ)

/-- The action itself is the player's strictly positive payoff. -/
def game : StrategicGame Unit (fun _ => Action) Payoff where
  payoff _ a := ⟨(a ()).val, lt_of_lt_of_le zero_lt_one (a ()).property.1⟩

/-- Payoff varies continuously with the player's action. -/
instance : game.Continuous where
  continuous_payoff _ :=
    (continuous_subtype_val.comp (continuous_apply ())).subtype_mk _

/-- Pure existence applies to positive payoffs without supplying a zero payoff. -/
theorem exists_isNash : ∃ a, game.IsNash a := by
  have ha_nonempty : Nonempty Action := ⟨⟨1, by norm_num⟩⟩
  refine game.exists_isNash_of_quasiconcaveOn
    (fun _ => Homeomorph.refl Action) (fun _ => convex_Icc 1 2) ?_
  intro a i r
  have hsuperlevel :
      {x ∈ Set.Icc (1 : ℝ) 2 |
        r ≤ Subtype.val.extend
          ((fun s => game.payoff i (Function.update a i s)) ∘
            (Homeomorph.refl Action).symm) (fun _ => game.payoff i a) x} =
      Set.Icc (1 : ℝ) 2 ∩ Set.Ici (r : ℝ) := by
    ext x
    by_cases hx : x ∈ Set.Icc (1 : ℝ) 2
    · have hextend := Subtype.val_injective.extend_apply
        ((fun s => game.payoff i (Function.update a i s)) ∘
          (Homeomorph.refl Action).symm) (fun _ => game.payoff i a) ⟨x, hx⟩
      cases i
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Ici, hx, true_and]
      rw [hextend]
      simp only [Function.comp_apply, Homeomorph.refl_symm, Homeomorph.refl_apply,
        game, Function.update_self]
      rfl
    · simp only [Set.mem_setOf_eq, Set.mem_inter_iff, hx, false_and]
  change Convex ℝ _
  rw [hsuperlevel]
  exact (convex_Icc 1 2).inter (convex_Ici (r : ℝ))

end Positive

end MathEconLibTest.GameTheory.OrderedPayoffs

end
