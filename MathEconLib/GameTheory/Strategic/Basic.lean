/-
Copyright (c) 2026 Ben Eltschig, Daniel Lyng. All rights reserved.
Released under license as described in the file LICENSE.
Authors: Ben Eltschig, Daniel Lyng
-/
module

public import MathEconLib.GameTheory.Equilibrium.Problem
public import Mathlib.Order.Max

/-!
# Strategic games and Nash equilibrium

A strategic game assigns a payoff to each player at each action profile. Nash equilibrium requires
an incumbent payoff weakly above every unilateral deviation's payoff. Dominance compares actions
against all opponents' choices; strict Nash equilibrium requires losses from every unilateral
change, while strong Nash equilibrium requires each changed profile to leave some changing player
weakly worse off. Strict dominance requires strict improvement at every opponent profile, whereas
being strictly above every alternative in the dominance preorder allows ties at some profiles. For
partially ordered payoffs, Nash equilibrium also excludes unilateral deviations with incomparable
payoffs, and strong Nash equilibrium requires a weakly worse-off changing player even when some
payoffs are incomparable. Their usual characterizations by the absence of strictly profitable
deviations require a linear order.

Action maps give a strategic game on new action spaces by evaluating payoffs at the translated
actions. Identity maps preserve the game; successive action translations compose pointwise. Every
unilateral deviation translates to a unilateral deviation, so a profile is a Nash equilibrium in
the translated game whenever its image is a Nash equilibrium in the original game.

## Main definitions

* `StrategicGame`, `StrategicGame.nashProblem`, and `StrategicGame.IsNash`.
* `StrategicGame.comapActions`: The game obtained by translating each player's action.
* `StrategicGame.comapActionsComorphism`: Action translation between Nash equilibrium problems.
* `StrategicGame.Strategy`, with the preorder of weak dominance.
* `StrategicGame.Strategy.IsDominant`, `StrategicGame.Strategy.IsStrictOrderDominant`, and
  `StrategicGame.Strategy.IsStrictlyDominant`.
* `StrategicGame.IsStrictNash` and `StrategicGame.IsStrongNash`.

## Main statements

* `StrategicGame.comapActions_id` and `StrategicGame.comapActions_comp`: Identity action maps
  preserve the game; successive action translations compose.
* `StrategicGame.isNash_iff` gives the unilateral payoff inequalities.
* `StrategicGame.IsNash.comapActions`: Nash equilibrium pulls back along action translations.
* `StrategicGame.isNash_iff_of_actionEquiv`: Payoff-preserving relabelings preserve Nash
  equilibrium.
* `StrategicGame.isNash_iff_not_lt` and `StrategicGame.isStrongNash_iff_not_lt`: For linearly
  ordered payoffs, Nash and strong Nash equilibria exclude strictly profitable deviations.
* `StrategicGame.isNash_of_isDominant`: Dominant strategy profiles are Nash equilibria.
* `StrategicGame.isStrictNash_of_isStrictlyDominant`: Strictly dominant strategy profiles are
  strict Nash equilibria.
* `StrategicGame.IsStrictNash.isNash` and `StrategicGame.IsStrongNash.isNash`: Strict and strong
  Nash equilibria are Nash equilibria.

## Tags

strategic games, nash equilibrium, dominance
-/

@[expose] public section

namespace MathEconLib.GameTheory

/-- A strategic game assigns each player a payoff at every action profile. -/
structure StrategicGame (I : Type*) (A : I → Type*) (V : Type*) where
  /-- Each player's payoff at each action profile. -/
  payoff : I → (∀ i, A i) → V

variable {ι : Type*} {A : ι → Type*} {V : Type*}

namespace StrategicGame

/-- The strategic game in which each player's action is translated by `κ` before the original
game's payoffs are evaluated. -/
@[simps] def comapActions {B : ι → Type*} (G : StrategicGame ι A V)
    (κ : (i : ι) → B i → A i) : StrategicGame ι B V where
  payoff i b := G.payoff i (fun j ↦ κ j (b j))

/-- Translating actions by the identity preserves the game. -/
@[simp] lemma comapActions_id (G : StrategicGame ι A V) :
    G.comapActions (fun _ ↦ id) = G := rfl

/-- Successive action translations agree with their composition. -/
lemma comapActions_comp {B : ι → Type*} {C : ι → Type*} (G : StrategicGame ι A V)
    (κ : (i : ι) → B i → A i) (τ : (i : ι) → C i → B i) :
    (G.comapActions κ).comapActions τ = G.comapActions (fun i ↦ κ i ∘ τ i) := rfl

/-- The equilibrium problem in which a player may replace only their own action. -/
def nashProblem [DecidableEq ι] (G : StrategicGame ι A V) : EquilibriumProblem (∀ i, A i) ι V where
  deviation i a a' := ∃ s, a' = Function.update a i s
  value := G.payoff

/-- Action translation maps unilateral deviations to unilateral deviations and preserves each
player's payoff. -/
def comapActionsComorphism [DecidableEq ι] {B : ι → Type*} (G : StrategicGame ι A V)
    (κ : (i : ι) → B i → A i) :
    GameComorphism (G.comapActions κ).nashProblem G.nashProblem where
  toFun b := fun i ↦ κ i (b i)
  deviatorMap := id
  deviation_maps i b b' hb := by
    obtain ⟨s, rfl⟩ := hb
    exact ⟨κ i s, funext (Function.apply_update κ b i s)⟩
  value_eq _ _ := rfl

/-- Every unilateral deviation gives the player a payoff at most their incumbent payoff. -/
def IsNash [LE V] [DecidableEq ι] (G : StrategicGame ι A V) (a : ∀ i, A i) : Prop :=
  G.nashProblem.IsEquilibrium a

/-- A profile is a Nash equilibrium in the game with translated actions if its image is a Nash
equilibrium in the original game. The action maps need not be injective or surjective. -/
theorem IsNash.comapActions [LE V] [DecidableEq ι] {B : ι → Type*}
    {G : StrategicGame ι A V} (κ : (i : ι) → B i → A i) {b : (i : ι) → B i}
    (h : G.IsNash (fun i ↦ κ i (b i))) : (G.comapActions κ).IsNash b :=
  (G.comapActionsComorphism κ).pullback h

/-- Nash equilibrium is equivalent to the unilateral payoff inequalities. -/
@[simp] lemma isNash_iff [LE V] [DecidableEq ι] (G : StrategicGame ι A V) (a : ∀ i, A i) :
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
lemma isNash_iff_of_actionEquiv [LE V] [DecidableEq ι] {B : ι → Type*}
    (G : StrategicGame ι A V) (H : StrategicGame ι B V) (e : ∀ i, A i ≃ B i)
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

/-- Nash equilibrium excludes strictly profitable unilateral deviations. -/
lemma IsNash.not_lt [Preorder V] [DecidableEq ι] {G : StrategicGame ι A V}
    {a : ∀ i, A i} (ha : G.IsNash a) (i : ι) (s : A i) :
    ¬ G.payoff i a < G.payoff i (Function.update a i s) :=
  not_lt_of_ge ((isNash_iff G a).1 ha i s)

/-- For linearly ordered payoffs, Nash equilibrium is absence of strict unilateral improvement. -/
lemma isNash_iff_not_lt [LinearOrder V] [DecidableEq ι] (G : StrategicGame ι A V)
    (a : ∀ i, A i) :
    G.IsNash a ↔ ∀ i s, ¬ G.payoff i a < G.payoff i (Function.update a i s) := by
  simp only [isNash_iff, not_lt]

section Strategies

-- The game parameter identifies the payoff function used by the strategy preorder.
set_option linter.unusedVariables false in
/-- The pure strategies of player `i`, ordered by weak dominance in the game `G`. -/
def Strategy (G : StrategicGame ι A V) (i : ι) := A i

namespace Strategy

variable [LE V]

/-- One strategy is below another when the latter weakly improves payoff at every opponent
profile. -/
instance (G : StrategicGame ι A V) (i : ι) : LE (G.Strategy i) where
  le s s' := ∀ (a a' : (i : ι) → A i), a i = s → a' i = s' → (∀ j ≠ i, a j = a' j) →
    G.payoff i a ≤ G.payoff i a'

/-- Weak dominance compares profiles in which only the player's own action may differ. -/
protected lemma le_def {G : StrategicGame ι A V} {i : ι} {s s' : G.Strategy i} :
    s ≤ s' ↔ ∀ (a a' : (i : ι) → A i), a i = s → a' i = s' → (∀ j ≠ i, a j = a' j) →
      G.payoff i a ≤ G.payoff i a' :=
  Iff.rfl

/-- Weak dominance compares a profile with the profile obtained by replacing the player's action. -/
protected lemma le_iff [DecidableEq ι] {G : StrategicGame ι A V} {i : ι}
    {s s' : G.Strategy i} :
    s ≤ s' ↔ ∀ (a a' : (i : ι) → A i), a i = s → a' = Function.update a i s' →
      G.payoff i a ≤ G.payoff i a' := by
  simp only [Strategy.le_def, Function.eq_update_iff, and_imp, eq_comm]

/-- Weak dominance is the payoff inequality for both actions at every opponent profile. -/
protected lemma le_iff' [DecidableEq ι] {G : StrategicGame ι A V} {i : ι}
    {s s' : G.Strategy i} :
    s ≤ s' ↔ ∀ a : (i : ι) → A i, G.payoff i (Function.update a i s) ≤
      G.payoff i (Function.update a i s') := by
  rw [Strategy.le_iff]
  refine ⟨fun h a ↦ h _ _ (by simp) (by simp), fun h a a' ha ha' ↦ ?_⟩
  rw [Function.eq_update_self_iff.2 ha, ha']
  exact h a

/-- A weakly dominant strategy weakly improves payoff over every strategy at every opponent
profile. -/
def IsDominant {G : StrategicGame ι A V} {i : ι} (s : G.Strategy i) :=
  IsTop s

end Strategy

namespace Strategy

variable [Preorder V]

/-- Weak dominance is a reflexive and transitive relation on pure strategies. -/
instance (G : StrategicGame ι A V) (i : ι) : Preorder (G.Strategy i) where
  le_refl s a a' hai hai' h := Eq.le <| by congr; grind
  le_trans s s' s'' := by
    classical
    simp_rw [Strategy.le_iff']
    grind

/-- The strict part of the weak-dominance preorder requires weak improvement at every opponent
profile and strict improvement at some opponent profile. -/
protected lemma lt_iff [DecidableEq ι] {G : StrategicGame ι A V} (i : ι)
    {s s' : G.Strategy i} :
    s < s' ↔ s ≤ s' ∧ ∃ a : (i : ι) → A i, G.payoff i (Function.update a i s) <
      G.payoff i (Function.update a i s') := by
  refine lt_iff_le_not_ge.trans <| and_congr_right fun h ↦ ?_
  simp only [Strategy.le_iff', not_forall, lt_iff_le_not_ge, Strategy.le_iff'.1 h, true_and]

/-- A strategy above every other strategy in the strict part of the weak-dominance preorder: For
each alternative, payoff weakly improves at every opponent profile and strictly improves at some
opponent profile. The profile giving strict improvement may depend on the alternative. -/
def IsStrictOrderDominant {G : StrategicGame ι A V} {i : ι} (s : G.Strategy i) :=
  ∀ s' ≠ s, s' < s

/-- A strategy above every alternative in the strict part of the weak-dominance preorder is weakly
dominant. -/
lemma IsStrictOrderDominant.isDominant {G : StrategicGame ι A V} {i : ι}
    {s : G.Strategy i} (hs : s.IsStrictOrderDominant) : s.IsDominant := by
  intro s'
  by_cases h : s' = s
  · exact h.le
  · exact (hs _ h).le

end Strategy

namespace Strategy

/-- A strictly dominant strategy gives strictly greater payoff than every distinct alternative at
every opponent profile. -/
def IsStrictlyDominant [LT V] [DecidableEq ι] {G : StrategicGame ι A V} {i : ι}
    (s : G.Strategy i) : Prop :=
  ∀ s' ≠ s, ∀ a : (j : ι) → A j,
    G.payoff i (Function.update a i s') < G.payoff i (Function.update a i s)

/-- Every strictly dominant strategy is weakly dominant. -/
lemma IsStrictlyDominant.isDominant [Preorder V] [DecidableEq ι]
    {G : StrategicGame ι A V} {i : ι} {s : G.Strategy i}
    (hs : s.IsStrictlyDominant) : s.IsDominant := by
  intro s'
  rw [Strategy.le_iff']
  intro a
  by_cases h : s' = s
  · subst s'
    exact le_rfl
  · exact (hs s' h a).le

/-- With a nonempty action-profile space, a strictly dominant strategy is strictly above every
distinct alternative in the weak-dominance preorder. -/
lemma IsStrictlyDominant.isStrictOrderDominant [Preorder V] [DecidableEq ι]
    [Nonempty ((j : ι) → A j)] {G : StrategicGame ι A V} {i : ι} {s : G.Strategy i}
    (hs : s.IsStrictlyDominant) : s.IsStrictOrderDominant := by
  obtain ⟨a⟩ := ‹Nonempty ((j : ι) → A j)›
  intro s' h
  rw [Strategy.lt_iff i]
  exact ⟨hs.isDominant s', ⟨a, hs s' h a⟩⟩

end Strategy

end Strategies

section Equilibria

/-- A strict Nash equilibrium makes every unilateral change to a different action strictly reduce
the deviating player's payoff. -/
def IsStrictNash [LT V] [DecidableEq ι] (G : StrategicGame ι A V)
    (a : (i : ι) → A i) :=
  ∀ i, ∀ s ≠ a i, G.payoff i (Function.update a i s) < G.payoff i a

/-- A profile of strictly dominant strategies is a strict Nash equilibrium. -/
lemma isStrictNash_of_isStrictlyDominant [LT V] [DecidableEq ι]
    {G : StrategicGame ι A V} {a : (i : ι) → A i}
    (ha : ∀ i, Strategy.IsStrictlyDominant (G := G) (a i)) : G.IsStrictNash a := by
  intro i s h
  simpa only [Function.update_eq_self] using ha i s h a

/-- Every strict Nash equilibrium is a Nash equilibrium. -/
lemma IsStrictNash.isNash [Preorder V] [DecidableEq ι] {G : StrategicGame ι A V} {a : (i : ι) → A i}
    (ha : G.IsStrictNash a) : G.IsNash a := by
  rw [isNash_iff]
  intro i s
  by_cases h : s = a i
  · simp [h]
  · exact (ha i s h).le

/-- A profile of weakly dominant strategies is a Nash equilibrium. -/
lemma isNash_of_isDominant [LE V] [DecidableEq ι] {G : StrategicGame ι A V}
    {a : (i : ι) → A i} (ha : ∀ i, Strategy.IsDominant (G := G) (a i)) :
    G.IsNash a :=
  (isNash_iff G a).2 fun i s ↦ ha i s _ _ (by simp) rfl (by grind)

/-- A strong Nash equilibrium makes every different action profile leave at least one player who
changed their action weakly worse off. With a linear order, this is equivalent to the absence of
deviations that strictly benefit every changing player. With a partial order, it excludes
deviations for which no changing player's payoff is at most their incumbent payoff. -/
def IsStrongNash [LE V] (G : StrategicGame ι A V)
    (a : (i : ι) → A i) :=
  ∀ a' ≠ a, ∃ i, a i ≠ a' i ∧ G.payoff i a' ≤ G.payoff i a

/-- For linearly ordered payoffs, strong Nash equilibrium excludes every different action profile
that strictly benefits all players who change their actions. -/
lemma isStrongNash_iff_not_lt [LinearOrder V] (G : StrategicGame ι A V)
    (a : (i : ι) → A i) :
    G.IsStrongNash a ↔ ∀ a' ≠ a, ¬ ∀ i, a i ≠ a' i → G.payoff i a < G.payoff i a' := by
  simp only [IsStrongNash, not_forall, not_lt, exists_prop]

/-- Every strong Nash equilibrium is a Nash equilibrium. -/
lemma IsStrongNash.isNash [Preorder V] [DecidableEq ι] {G : StrategicGame ι A V} {a : (i : ι) → A i}
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

end MathEconLib.GameTheory
