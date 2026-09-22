/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Auctionlib.GameTheory.Equilibrium.Problem

/-!
# Strategic games and Nash equilibrium

A strategic game assigns a real payoff to each player at each action profile. Nash equilibrium
rules out profitable unilateral changes. Dominance compares actions against all opponents' choices;
strict Nash equilibrium requires losses from every unilateral change, while strong Nash equilibrium
rules out deviations that strictly benefit every player who changes their action.

## Main definitions

* `StrategicGame`, `StrategicGame.nashProblem`, and `StrategicGame.IsNash`.
* `StrategicGame.Strategy`, with the preorder of weak dominance.
* `StrategicGame.Strategy.IsDominant` and `StrategicGame.Strategy.IsStrictlyDominant`.
* `StrategicGame.IsStrictNash` and `StrategicGame.IsStrongNash`.

## Main statements

* `StrategicGame.isNash_iff` gives the unilateral payoff inequalities.
* `StrategicGame.isNash_iff_of_actionEquiv`: Payoff-preserving relabelings preserve Nash
  equilibrium.
* `StrategicGame.isNash_of_isDominant`: dominant strategy profiles are Nash equilibria.
* `StrategicGame.IsStrictNash.isNash` and `StrategicGame.IsStrongNash.isNash`: strict and strong
  Nash equilibria are Nash equilibria.

## Tags

strategic games, nash equilibrium, dominance
-/

@[expose] public section

namespace Auctionlib.GameTheory

/-- A strategic game assigns each player a real payoff at every action profile. -/
structure StrategicGame (I : Type*) (A : I → Type*) where
  /-- Each player's payoff at each action profile. -/
  payoff : I → (∀ i, A i) → ℝ

variable {ι : Type*} {A : ι → Type*}

namespace StrategicGame

/-- The equilibrium problem in which a player may replace only their own action. -/
def nashProblem [DecidableEq ι] (G : StrategicGame ι A) : EquilibriumProblem (∀ i, A i) ι where
  deviation i a a' := ∃ s, a' = Function.update a i s
  value := G.payoff

/-- No player can improve their payoff by changing only their own action. -/
def IsNash [DecidableEq ι] (G : StrategicGame ι A) (a : ∀ i, A i) : Prop :=
  G.nashProblem.IsEquilibrium a

/-- A profile is a Nash equilibrium exactly when no unilateral action change raises payoff. -/
@[simp] lemma isNash_iff [DecidableEq ι] (G : StrategicGame ι A) (a : ∀ i, A i) :
    G.IsNash a ↔ ∀ i s, G.payoff i (Function.update a i s) ≤ G.payoff i a := by
  constructor
  · intro h i s
    exact h i _ ⟨s, rfl⟩
  · intro h i a' hd
    obtain ⟨s, hs⟩ := hd
    change G.payoff i a' ≤ G.payoff i a
    rw [hs]
    exact h i s

/-- Relabeling each player's actions by a payoff-preserving equivalence preserves Nash
equilibrium. -/
lemma isNash_iff_of_actionEquiv [DecidableEq ι] {B : ι → Type*}
    (G : StrategicGame ι A) (H : StrategicGame ι B) (e : ∀ i, A i ≃ B i)
    (hpayoff : ∀ i a, G.payoff i a = H.payoff i (fun j ↦ e j (a j))) (a : ∀ i, A i) :
    G.IsNash a ↔ H.IsNash (fun i ↦ e i (a i)) := by
  simp only [isNash_iff, hpayoff]
  have hupdate (i : ι) (s : A i) :
      (fun j ↦ e j (Function.update a i s j)) =
        Function.update (fun j ↦ e j (a j)) i (e i s) :=
    funext (Function.apply_update (fun j ↦ e j) a i s)
  simp_rw [hupdate]
  constructor
  · intro h i b
    simpa only [Equiv.apply_symm_apply] using h i ((e i).symm b)
  · intro h i s
    exact h i (e i s)

section Strategies

-- The game parameter identifies the payoff function used by the strategy preorder.
set_option linter.unusedVariables false in
/-- The pure strategies of player `i`, ordered by weak dominance in the game `G`. -/
def Strategy (G : StrategicGame ι A) (i : ι) := A i

namespace Strategy

/-- One strategy is below another when the latter weakly improves payoff at every opponent
profile. -/
instance (G : StrategicGame ι A) (i : ι) : LE (G.Strategy i) where
  le s s' := ∀ (a a' : (i : ι) → A i), a i = s → a' i = s' → (∀ j ≠ i, a j = a' j) →
    G.payoff i a ≤ G.payoff i a'

/-- Weak dominance compares profiles in which only the player's own action may differ. -/
protected lemma le_def {G : StrategicGame ι A} {i : ι} {s s' : G.Strategy i} :
    s ≤ s' ↔ ∀ (a a' : (i : ι) → A i), a i = s → a' i = s' → (∀ j ≠ i, a j = a' j) →
      G.payoff i a ≤ G.payoff i a' :=
  Iff.rfl

/-- Weak dominance compares a profile with the profile obtained by replacing the player's action. -/
protected lemma le_iff [DecidableEq ι] {G : StrategicGame ι A} {i : ι}
    {s s' : G.Strategy i} :
    s ≤ s' ↔ ∀ (a a' : (i : ι) → A i), a i = s → a' = Function.update a i s' →
      G.payoff i a ≤ G.payoff i a' := by
  simp only [Strategy.le_def, Function.eq_update_iff, and_imp, eq_comm]

/-- Weak dominance is the payoff inequality for both actions at every opponent profile. -/
protected lemma le_iff' [DecidableEq ι] {G : StrategicGame ι A} {i : ι}
    {s s' : G.Strategy i} :
    s ≤ s' ↔ ∀ a : (i : ι) → A i, G.payoff i (Function.update a i s) ≤
      G.payoff i (Function.update a i s') := by
  rw [Strategy.le_iff]
  refine ⟨fun h a ↦ h _ _ (by simp) (by simp), fun h a a' ha ha' ↦ ?_⟩
  rw [Function.eq_update_self_iff.2 ha, ha']
  exact h a

/-- Weak dominance is a reflexive and transitive relation on pure strategies. -/
instance (G : StrategicGame ι A) (i : ι) : Preorder (G.Strategy i) where
  le_refl s a a' hai hai' h := Eq.le <| by congr; grind
  le_trans s s' s'' := by
    classical
    simp_rw [Strategy.le_iff']
    grind

/-- The strict part of the weak-dominance preorder requires weak improvement at every opponent
profile and strict improvement at some opponent profile. -/
protected lemma lt_iff [DecidableEq ι] {G : StrategicGame ι A} (i : ι)
    {s s' : G.Strategy i} :
    s < s' ↔ s ≤ s' ∧ ∃ a : (i : ι) → A i, G.payoff i (Function.update a i s) <
      G.payoff i (Function.update a i s') := by
  refine lt_iff_le_not_ge.trans <| and_congr_right fun h ↦ ?_
  simp only [Strategy.le_iff', not_forall, lt_iff_le_not_ge, Strategy.le_iff'.1 h, true_and]

/-- A weakly dominant strategy weakly improves payoff over every strategy at every opponent
profile. -/
def IsDominant {G : StrategicGame ι A} {i : ι} (s : G.Strategy i) :=
  IsTop s

/-- A strategy above every other strategy in the strict part of the weak-dominance preorder: for
each alternative, payoff weakly improves at every opponent profile and strictly improves at some
opponent profile. The profile giving strict improvement may depend on the alternative. -/
def IsStrictlyDominant {G : StrategicGame ι A} {i : ι} (s : G.Strategy i) :=
  ∀ s' ≠ s, s' < s

/-- A strategy above every alternative in the strict weak-dominance order is weakly dominant. -/
lemma IsStrictlyDominant.isDominant {G : StrategicGame ι A} {i : ι}
    {s : G.Strategy i} (hs : s.IsStrictlyDominant) : s.IsDominant := by
  intro s'
  by_cases h : s' = s
  · exact h.le
  · exact (hs _ h).le

end Strategy

end Strategies

section Equilibria

/-- A strict Nash equilibrium makes every unilateral change to a different action strictly reduce
the deviating player's payoff. -/
def IsStrictNash [DecidableEq ι] (G : StrategicGame ι A)
    (a : (i : ι) → A i) :=
  ∀ i, ∀ s ≠ a i, G.payoff i (Function.update a i s) < G.payoff i a

/-- Every strict Nash equilibrium is a Nash equilibrium. -/
lemma IsStrictNash.isNash [DecidableEq ι] {G : StrategicGame ι A} {a : (i : ι) → A i}
    (ha : G.IsStrictNash a) : G.IsNash a := by
  rw [isNash_iff]
  intro i s
  by_cases h : s = a i
  · simp [h]
  · exact (ha i s h).le

/-- A profile of weakly dominant strategies is a Nash equilibrium. -/
lemma isNash_of_isDominant [DecidableEq ι] {G : StrategicGame ι A}
    {a : (i : ι) → A i} (ha : ∀ i, Strategy.IsDominant (G := G) (a i)) :
    G.IsNash a :=
  (isNash_iff G a).2 fun i s ↦ ha i s _ _ (by simp) rfl (by grind)

/-- A strong Nash equilibrium makes every different action profile leave at least one player who
changed their action no better off. Thus no coalition can change its actions and strictly benefit
every member. -/
def IsStrongNash (G : StrategicGame ι A)
    (a : (i : ι) → A i) :=
  ∀ a' ≠ a, ∃ i, a i ≠ a' i ∧ G.payoff i a' ≤ G.payoff i a

/-- Every strong Nash equilibrium is a Nash equilibrium. -/
lemma IsStrongNash.isNash [DecidableEq ι] {G : StrategicGame ι A} {a : (i : ι) → A i}
    (ha : G.IsStrongNash a) : G.IsNash a := by
  rw [isNash_iff]
  intro i s
  by_cases h : s = a i
  · simp [h]
  · have ⟨j, hj, hj'⟩ := ha (Function.update a i s) (by simp [h])
    replace hj : j = i := by grind
    rwa [hj] at hj'

end Equilibria

end StrategicGame

end Auctionlib.GameTheory
