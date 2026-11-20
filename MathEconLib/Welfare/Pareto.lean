/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Preferences.Basic
public import Mathlib.Order.Minimal

/-!
# Ordinal Pareto efficiency

Choose the agents whose preferences count and the set of feasible outcomes. A Pareto improvement
makes every agent weakly better off and some agent strictly better off. Weak Pareto efficiency
rules out a feasible alternative that makes every agent strictly better off.

The arguments of both improvement relations run from the original outcome to the proposed one.
-/

@[expose] public section

namespace MathEconLib.Welfare

open Preferences

variable {I X : Type*} (R : I → Preference X)

/-- Compare outcomes by requiring every agent to weakly prefer the second. -/
def unanimousPreference : Preference X :=
  (Preference.ofPreorder (@Pi.preorder I (fun _ ↦ X) fun i ↦ (R i).toPreorder)).comap
    (fun x _ ↦ x)

@[simp]
theorem unanimousPreference_le_iff (x y : X) :
    (unanimousPreference R).le x y ↔ ∀ i, (R i).le x y := Iff.rfl

/-- Moving from `x` to `y` makes everyone weakly better off and someone strictly better off. -/
def ParetoImprovement (x y : X) : Prop :=
  (unanimousPreference R).le x y ∧ ∃ i, (R i).lt x y

/-- Every agent strictly prefers `y` to `x`. -/
def UnanimousStrictImprovement (x y : X) : Prop :=
  ∀ i, (R i).lt x y

/-- A Pareto improvement is a strict comparison under the unanimous preference. -/
theorem unanimousPreference_lt_iff (x y : X) :
    (unanimousPreference R).lt x y ↔ ParetoImprovement R x y :=
  @Pi.lt_def I (fun _ ↦ X) (fun i ↦ (R i).toPreorder) (fun _ ↦ x) (fun _ ↦ y)

/-- A feasible outcome for which no feasible alternative is a Pareto improvement. -/
def IsParetoEfficient (F : Set X) (x : X) : Prop :=
  letI := (unanimousPreference R).toPreorder
  Maximal (· ∈ F) x

/-- A feasible outcome for which no feasible alternative makes everyone strictly better off. -/
def IsWeaklyParetoEfficient (F : Set X) (x : X) : Prop :=
  x ∈ F ∧ ∀ y ∈ F, ¬ UnanimousStrictImprovement R x y

/-- Pareto efficiency is maximality in the unanimous preorder on the feasible set. -/
theorem isParetoEfficient_iff_maximal (F : Set X) (x : X) :
    IsParetoEfficient R F x ↔
      letI := (unanimousPreference R).toPreorder
      Maximal (· ∈ F) x := Iff.rfl

/-- Test Pareto efficiency by ruling out a strict gain for someone with no losses for others. -/
theorem isParetoEfficient_iff (F : Set X) (x : X) :
    IsParetoEfficient R F x ↔ x ∈ F ∧ ∀ y ∈ F, ¬ ParetoImprovement R x y := by
  let := (unanimousPreference R).toPreorder
  change Maximal (· ∈ F) x ↔ _
  rw [maximal_iff_forall_gt]
  apply and_congr_right'
  constructor
  · intro h y hy hxy
    exact h ((unanimousPreference_lt_iff R x y).mpr hxy) hy
  · intro h y hxy hy
    exact h y hy ((unanimousPreference_lt_iff R x y).mp hxy)

/-- To prove weak efficiency, establish feasibility and rule out a strict gain for everyone. -/
theorem isWeaklyParetoEfficient_iff (F : Set X) (x : X) :
    IsWeaklyParetoEfficient R F x ↔ x ∈ F ∧ ∀ y ∈ F, ¬ UnanimousStrictImprovement R x y :=
  Iff.rfl

variable {R} {F : Set X} {x y : X}

theorem UnanimousStrictImprovement.paretoImprovement [Nonempty I]
    (h : UnanimousStrictImprovement R x y) : ParetoImprovement R x y :=
  ⟨fun i ↦ (h i).1, ‹Nonempty I›.elim fun i ↦ ⟨i, h i⟩⟩

theorem IsParetoEfficient.isWeaklyParetoEfficient [Nonempty I] (hx : IsParetoEfficient R F x) :
    IsWeaklyParetoEfficient R F x := by
  obtain ⟨hx, h⟩ := (isParetoEfficient_iff R F x).mp hx
  exact ⟨hx, fun y hy hxy ↦ h y hy hxy.paretoImprovement⟩

variable (R F x)

/-- With no agents, no one can witness a strict gain. -/
@[simp]
theorem isParetoEfficient_iff_mem_of_isEmpty [IsEmpty I] :
    IsParetoEfficient R F x ↔ x ∈ F := by
  rw [isParetoEfficient_iff]
  exact ⟨And.left, fun hx ↦ ⟨hx, fun _ _ ⟨_, i, _⟩ ↦ isEmptyElim i⟩⟩

/-- With no agents, even staying at a feasible outcome vacuously improves every agent strictly. -/
@[simp]
theorem not_isWeaklyParetoEfficient_of_isEmpty [IsEmpty I] : ¬ IsWeaklyParetoEfficient R F x :=
  fun hx ↦ hx.2 x hx.1 fun i ↦ isEmptyElim i

end MathEconLib.Welfare
