/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLib.ForMathlib.Order.Refinement

/-!
# Greatest elements under tie-breaking

These clients import only the general order module. Explicit order arguments prevent an ambient
instance from replacing the original or refined order. The concrete tests use infinite sets.
-/

namespace MathEconLibTest.Order.Refinement

open MathEconLib.Order

example {α β : Type*} [LinearOrder β] (pref : Preorder α) (complete : Std.Total pref.le)
    (priority : α ↪ β) {S : Set α} {a : α} :
    @IsGreatest α (tieBreakOrder pref complete priority).toLE S a ↔
      @IsGreatest α pref.toLE S a ∧
        ∀ b, @IsGreatest α pref.toLE S b → priority b ≤ priority a :=
  isGreatest_tieBreakOrder_iff pref complete priority

example {α β : Type*} [LinearOrder β] (pref : Preorder α) (complete : Std.Total pref.le)
    (priority : α ↪ β) (S : Set α) :
    (∃ a, @IsGreatest α (tieBreakOrder pref complete priority).toLE S a) ↔
      ∃ p, IsGreatest (priority '' {a | @IsGreatest α pref.toLE S a}) p :=
  exists_isGreatest_tieBreakOrder_iff pref complete priority S

example {α β : Type*} [LinearOrder β] (pref : Preorder α) (complete : Std.Total pref.le)
    (priority : α ↪ β) :
    ¬∃ a, @IsGreatest α (tieBreakOrder pref complete priority).toLE ∅ a :=
  fun ⟨_, ha⟩ ↦ ha.1

/-- All natural numbers are tied in the original preorder. -/
@[instance_reducible] def tied : Preorder ℕ := Preorder.lift fun _ : ℕ ↦ (0 : ℕ)

theorem tied_total : Std.Total tied.le :=
  ⟨fun _ _ ↦ Or.inl (show (0 : ℕ) ≤ 0 from le_rfl)⟩

/-- The same numeric code, ordered in reverse, has well-founded strict improvement. -/
def reversedPriority : ℕ ↪ ℕᵒᵈ where
  toFun := OrderDual.toDual
  inj' := fun _ _ h ↦ h

/-- Infinite original greatest-element sets can still attain after refinement. -/
theorem tied_reversed_attains :
    ∃ a, @IsGreatest ℕ (tieBreakOrder tied tied_total reversedPriority).toLE Set.univ a :=
  exists_isGreatest_tieBreakOrder_of_wellFoundedGT tied tied_total reversedPriority
    ⟨0, Set.mem_univ _, fun _ _ ↦ (show (0 : ℕ) ≤ 0 from le_rfl)⟩

/-- Reversing priorities makes zero greatest within the infinite original tie. -/
theorem tied_reversed_zero :
    @IsGreatest ℕ (tieBreakOrder tied tied_total reversedPriority).toLE Set.univ 0 :=
  (isGreatest_tieBreakOrder_iff tied tied_total reversedPriority).mpr
    ⟨⟨Set.mem_univ _, fun _ _ ↦ (show (0 : ℕ) ≤ 0 from le_rfl)⟩,
      fun b _ ↦ Nat.zero_le b⟩

/-- Increasing priorities leave the infinite original tie without a greatest refinement. -/
theorem tied_increasing_unattained :
    ¬∃ a, @IsGreatest ℕ
      (tieBreakOrder tied tied_total (Function.Embedding.refl ℕ)).toLE Set.univ a := by
  exact fun ⟨a, ha⟩ ↦ Nat.not_succ_le_self a
    (((isGreatest_tieBreakOrder_iff tied tied_total (Function.Embedding.refl ℕ)).mp ha).2
      (a + 1) ⟨Set.mem_univ _, fun _ _ ↦ (show (0 : ℕ) ≤ 0 from le_rfl)⟩)

/-- Well-founded priorities still cannot create an original greatest natural number. -/
theorem increasing_reversed_unattained :
    ¬∃ a, @IsGreatest ℕ (tieBreakOrder (inferInstance : Preorder ℕ)
      ⟨le_total⟩ reversedPriority).toLE Set.univ a := by
  exact fun h ↦
    let ⟨a, ha⟩ := (exists_isGreatest_tieBreakOrder_iff_of_wellFoundedGT
      (inferInstance : Preorder ℕ) ⟨le_total⟩ reversedPriority Set.univ).mp h
    Nat.not_succ_le_self a (ha.2 (Set.mem_univ (a + 1)))

/-- Zero is the unique original greatest element of this infinite preorder. -/
@[instance_reducible] def peaked : Preorder ℕ :=
  Preorder.lift fun n : ℕ ↦ if n = 0 then (1 : ℕ) else 0

theorem peaked_total : Std.Total peaked.le :=
  ⟨fun a b ↦ le_total (if a = 0 then (1 : ℕ) else 0) (if b = 0 then 1 else 0)⟩

theorem peaked_greatest_finite : {a | @IsGreatest ℕ peaked.toLE Set.univ a}.Finite := by
  apply (Set.finite_singleton (0 : ℕ)).subset
  exact fun a ha ↦ Set.mem_singleton_iff.mpr <| Classical.byContradiction fun hn ↦
    (by decide : ¬ (1 : ℕ) ≤ 0)
      ((ite_eq_right hn : (if a = 0 then (1 : ℕ) else 0) = 0) ▸
        (show (1 : ℕ) ≤ (if a = 0 then 1 else 0) from
          ha.2 (Set.mem_univ 0)))

/-- Finite original attainment suffices even on an infinite set with unbounded priorities. -/
theorem peaked_increasing_attains :
    ∃ a, @IsGreatest ℕ
      (tieBreakOrder peaked peaked_total (Function.Embedding.refl ℕ)).toLE Set.univ a := by
  apply exists_isGreatest_tieBreakOrder_of_finite peaked peaked_total
    (Function.Embedding.refl ℕ) peaked_greatest_finite
  refine ⟨0, Set.mem_univ _, fun n _ ↦ ?_⟩
  change (if n = 0 then (1 : ℕ) else 0) ≤ 1
  split <;> decide

#print axioms MathEconLib.Order.isGreatest_tieBreakOrder_iff
#print axioms MathEconLib.Order.exists_isGreatest_tieBreakOrder_iff
#print axioms MathEconLib.Order.exists_isGreatest_tieBreakOrder_of_finite
#print axioms MathEconLib.Order.exists_isGreatest_tieBreakOrder_of_wellFoundedGT
#print axioms MathEconLib.Order.exists_isGreatest_tieBreakOrder_iff_of_wellFoundedGT
#print axioms tied_reversed_attains
#print axioms tied_reversed_zero
#print axioms tied_increasing_unattained
#print axioms increasing_reversed_unattained
#print axioms peaked_increasing_attains

end MathEconLibTest.Order.Refinement
