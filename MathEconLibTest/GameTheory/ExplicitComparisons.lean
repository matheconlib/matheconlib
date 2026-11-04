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

universe u v w x

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

end MathEconLibTest.GameTheory.ExplicitComparisons

end
