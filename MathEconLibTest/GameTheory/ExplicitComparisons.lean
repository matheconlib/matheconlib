/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib

/-!
# Public comparison API and ordered compatibility

These clients import only the public library umbrella. They pin representation across
independent consequence universes without order instances, and check that explicit preferences
can disagree with the ambient numerical order. Worked examples live in the examples library.
-/

@[expose] public section

open MathEconLib.GameTheory

namespace MathEconLibTest.GameTheory.ExplicitComparisons

universe u v w x y z

variable {S : Type u} {I : Type v} {X : Type w} {V : Type x}

example (P : EquilibriumProblem S I X) (R : I → X → X → Prop) (i : I) (s : S) :
    P.IsOptimalWith R i s ↔ ∀ t, P.deviation i s t → R i (P.value i t) (P.value i s) :=
  P.isOptimalWith_iff R i s

example (P : EquilibriumProblem S I X) (R : I → X → X → Prop) (s : S) :
    P.IsEquilibriumWith R s ↔
      ∀ i t, P.deviation i s t → R i (P.value i t) (P.value i s) :=
  P.isEquilibriumWith_iff R s

example [LE X] (P : EquilibriumProblem S I X) (s : S) :
    P.IsEquilibriumWith (fun _ x y ↦ x ≤ y) s ↔ P.IsEquilibrium s :=
  P.isEquilibriumWith_le_iff s

example (P : EquilibriumProblem S I X) (Q : EquilibriumProblem S I V)
    (R : I → X → X → Prop) (R' : I → V → V → Prop)
    (hdev : ∀ i s t, P.deviation i s t ↔ Q.deviation i s t)
    (hcmp : ∀ i s t, P.deviation i s t →
      (R i (P.value i t) (P.value i s) ↔ R' i (Q.value i t) (Q.value i s))) (s : S) :
    P.IsEquilibriumWith R s ↔ Q.IsEquilibriumWith R' s :=
  P.isEquilibriumWith_iff_of_comparisons Q R R' (hdev := hdev) (hcmp := hcmp) s

example (P : EquilibriumProblem S I X) (Q : EquilibriumProblem S I V)
    (R : I → X → X → Prop) (R' : I → V → V → Prop) (i : I)
    (hdev : ∀ s t, P.deviation i s t ↔ Q.deviation i s t)
    (hcmp : ∀ s t, P.deviation i s t →
      (R i (P.value i t) (P.value i s) ↔ R' i (Q.value i t) (Q.value i s))) (s : S) :
    P.IsOptimalWith R i s ↔ Q.IsOptimalWith R' i s :=
  P.isOptimalWith_iff_of_comparisons Q R R' i (hdev := hdev) (hcmp := hcmp) s

example (P : EquilibriumProblem S I X) (R : I → X → X → Prop) (s : S)
    (hcmp : ∀ i t, P.deviation i s t →
      R i (P.value i t) (P.value i s) ∨ R i (P.value i s) (P.value i t)) :
    P.IsEquilibriumWith R s ↔ ∀ i t, P.deviation i s t →
      ¬ (R i (P.value i s) (P.value i t) ∧ ¬ R i (P.value i t) (P.value i s)) :=
  P.isEquilibriumWith_iff_no_strictImprovement R s hcmp

/-- Numerical consequences do not force the supplied comparison to be the ambient order. -/
def naturalProblem : EquilibriumProblem Nat Unit Nat where
  deviation _ _ _ := True
  value _ n := n

example : naturalProblem.IsEquilibriumWith (fun _ x y ↦ y ≤ x) 0 :=
  fun _ n _ ↦ Nat.zero_le n

example : ¬ naturalProblem.IsEquilibrium 0 :=
  fun h ↦ (by decide : ¬ (1 : Nat) ≤ 0) (h () 1 trivial)

/-! Ordered recovery also recovers both existing transport routes with only an `LE` instance. -/

example {T : Type y} {J : Type z} [LE X]
    (P : EquilibriumProblem S I X) (Q : EquilibriumProblem T J X)
    (f : GameMorphism P Q) {s : S} (h : P.IsEquilibrium s) :
    Q.IsEquilibrium (f.toFun s) :=
  (Q.isEquilibriumWith_le_iff (f.toFun s)).1
    (f.transportWith (fun _ x y ↦ x ≤ y) (fun _ x y ↦ x ≤ y)
      (fun _ _ _ _ hxy ↦ hxy) ((P.isEquilibriumWith_le_iff s).2 h))

example {T : Type y} {J : Type z} [LE X]
    (P : EquilibriumProblem S I X) (Q : EquilibriumProblem T J X)
    (f : GameComorphism P Q) {s : S} (h : Q.IsEquilibrium (f.toFun s)) :
    P.IsEquilibrium s :=
  (P.isEquilibriumWith_le_iff s).1
    (f.pullbackWith (fun _ x y ↦ x ≤ y) (fun _ x y ↦ x ≤ y)
      (fun _ _ _ _ hxy ↦ hxy) ((Q.isEquilibriumWith_le_iff (f.toFun s)).2 h))

/-! Two players use different comparisons; transport selects the player named `true`. -/

/-- The second player evaluates the natural action; the first always receives zero. -/
def indexedProblem : EquilibriumProblem Nat Bool Nat where
  deviation _ _ _ := True
  value i n := if i then n else 0

/-- The active player minimizes its reward, while the constant-payoff player compares equality. -/
def indexedComparison (i : Bool) (x y : Nat) : Prop := if i then y ≤ x else x = y

/-- Zero is optimal for the active player, and the other player is indifferent. -/
theorem indexed_zero_isEquilibriumWith :
    indexedProblem.IsEquilibriumWith indexedComparison 0 := by
  intro i n _
  cases i <;> simp [indexedComparison, indexedProblem]

example : naturalProblem.IsEquilibriumWith (fun _ x y ↦ y ≤ x ∨ x = 0) 0 := by
  let f : GameMorphism indexedProblem naturalProblem := {
    toFun := id
    deviatorMap := fun _ ↦ true
    deviation_lifts := fun _ _ t _ ↦ ⟨t, trivial, rfl⟩
    value_eq := fun _ _ ↦ rfl }
  apply f.transportWith indexedComparison (fun _ x y ↦ y ≤ x ∨ x = 0)
  · intro _ _ _ _ h
    exact Or.inl h
  · exact indexed_zero_isEquilibriumWith

example : naturalProblem.IsEquilibriumWith (fun _ x y ↦ y ≤ x ∨ x = 0) 0 := by
  let f : GameComorphism naturalProblem indexedProblem := {
    toFun := id
    deviatorMap := fun _ ↦ true
    deviation_maps := fun _ _ _ _ ↦ trivial
    value_eq := fun _ _ ↦ rfl }
  apply f.pullbackWith (fun _ x y ↦ y ≤ x ∨ x = 0) indexedComparison
  · intro _ _ _ _ h
    exact Or.inl h
  · exact indexed_zero_isEquilibriumWith

/-! Comparability is needed only on admissible pairs, without global order or reflexivity. -/

/-- Only the successor is an admissible deviation. -/
def successorProblem : EquilibriumProblem Nat Unit Nat where
  deviation _ s t := t = s + 1
  value _ n := n

example (s : Nat) :
    successorProblem.IsEquilibriumWith (fun _ x y ↦ x = y + 1) s ↔
      ∀ i t, successorProblem.deviation i s t →
        ¬ (s = t + 1 ∧ ¬ t = s + 1) :=
  successorProblem.isEquilibriumWith_iff_no_strictImprovement
    (fun _ x y ↦ x = y + 1) s (fun _ _ ht ↦ Or.inl ht)

example : ¬ ((0 : Nat) = 3 + 1 ∨ (3 : Nat) = 0 + 1) := by decide

end MathEconLibTest.GameTheory.ExplicitComparisons

end
