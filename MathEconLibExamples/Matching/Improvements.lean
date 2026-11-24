/-
Copyright (c) 2026 Ayan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ayan
-/
module

public import MathEconLib.Matching.Classical.Marriage.Improvements

/-!
# Fixed-menu choice under unambiguous improvements

`NewlyAcceptable` applies both local choice theorems when a rival becomes newly acceptable.
`BelowOutside` and `Overtaken` show that both comparisons are needed in general. The proposer
must stay above the outside option and the rivals on the menu. A rival outside the menu can
pass him without changing the choice. These examples concern selection from a fixed menu.
-/

@[expose] public section

namespace MathEconLibExamples.Matching.Improvements

open MathEconLib.Matching MarriageMarket

/-! ## Preferences given by ranks -/

/-- Ranks on `Option Bool`: `none` gets `n`, `some false` gets `f`, `some true` gets `t`. -/
def rank (n f t : ℕ) : Option Bool → ℕ
  | none => n
  | some false => f
  | some true => t

/-- The linear order on `Option Bool` induced by an injective rank; larger rank is better. -/
abbrev order (n f t : ℕ) (h : Function.Injective (rank n f t)) : LinearOrder (Option Bool) :=
  LinearOrder.lift' (rank n f t) h

theorem order_lt {n f t : ℕ} {h : Function.Injective (rank n f t)} {a b : Option Bool} :
    (order n f t h).lt a b ↔ rank n f t a < rank n f t b :=
  Iff.rfl

theorem order_le {n f t : ℕ} {h : Function.Injective (rank n f t)} {a b : Option Bool} :
    (order n f t h).le a b ↔ rank n f t a ≤ rank n f t b :=
  Iff.rfl

/-! ## One receiver and two proposers

The receiver is `()`. The distinguished proposer is `true` and his rival is `false`. -/

/-- A market with proposers `Bool` and the single receiver `()`, who ranks proposers by `ord`.
Each proposer prefers the receiver to the outside option. -/
def market (ord : LinearOrder (Option Bool)) : MarriageMarket Bool Unit where
  prefM _ := LinearOrder.lift' (fun o : Option Unit => o.isSome.toNat) (by decide)
  prefW _ := ord

/-- The receiver selects `true` from the menu of both proposers exactly when she ranks him above
the outside option and above his rival. -/
theorem true_mem_inducedChoiceW_univ_iff (ord : LinearOrder (Option Bool)) :
    (true, ()) ∈ (market ord).inducedChoiceW () Set.univ ↔
      ord.le none (some true) ∧ ord.le (some false) (some true) := by
  rw [(market ord).mem_inducedChoiceW_iff]
  constructor
  · rintro ⟨-, hn, hb⟩
    exact ⟨hn, hb false (Set.mem_univ _)⟩
  · rintro ⟨hn, hf⟩
    refine ⟨Set.mem_univ _, hn, fun m' _ => ?_⟩
    cases m'
    · exact hf
    · exact ord.le_refl _

namespace NewlyAcceptable

/-- `some false < none < some true`: the rival is unacceptable. -/
abbrev oldOrder : LinearOrder (Option Bool) := order 1 0 2 (by decide)

/-- `none < some false < some true`: the rival has become acceptable. -/
abbrev newOrder : LinearOrder (Option Bool) := order 0 1 2 (by decide)

theorem isUnambiguousImprovement : IsUnambiguousImprovement newOrder oldOrder true := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [order_lt] <;> decide

theorem not_acceptableW_old : ¬ (market oldOrder).AcceptableW () false := by
  change ¬ rank 1 0 2 none < rank 1 0 2 (some false)
  decide

theorem acceptableW_new : (market newOrder).AcceptableW () false := by
  change rank 0 1 2 none < rank 0 1 2 (some false)
  decide

/-- Before the change, the receiver selects `true` from the menu of both proposers. -/
theorem mem_inducedChoiceW_old : (true, ()) ∈ (market oldOrder).inducedChoiceW () Set.univ := by
  rw [true_mem_inducedChoiceW_univ_iff]
  simp only [order_le]
  decide

/-- After the change she still selects `true`, by the fixed-menu result, although the menu
contains the newly acceptable rival. -/
theorem mem_inducedChoiceW_new : (true, ()) ∈ (market newOrder).inducedChoiceW () Set.univ :=
  (market oldOrder).mem_inducedChoiceW_of_forall_lt_some (market newOrder)
    isUnambiguousImprovement.lt_some_of_lt_some mem_inducedChoiceW_old

/-- The finite selector agrees, by the `bestW` form of the result. -/
theorem bestW_new : (market newOrder).bestW () Set.univ = some true :=
  (market oldOrder).bestW_eq_some_of_forall_lt_some (market newOrder)
    isUnambiguousImprovement.lt_some_of_lt_some
    (((market oldOrder).mem_inducedChoiceW.mp mem_inducedChoiceW_old).2).symm

end NewlyAcceptable

namespace BelowOutside

/-- `some false < none < some true`. -/
abbrev oldOrder : LinearOrder (Option Bool) := order 1 0 2 (by decide)

/-- `some false < some true < none`: `true` has become unacceptable. -/
abbrev newOrder : LinearOrder (Option Bool) := order 2 0 1 (by decide)

/-- The change keeps the advantage of `true` over his rival and satisfies the second and third
clauses of the relation. -/
theorem other_clauses :
    (oldOrder.lt (some false) (some true) → newOrder.lt (some false) (some true)) ∧
      (∀ ⦃m' m'' : Bool⦄, m' ≠ true → m'' ≠ true →
        (oldOrder.lt (some m'') (some m') ↔ newOrder.lt (some m'') (some m'))) ∧
      ∀ ⦃m' : Bool⦄, m' ≠ true → oldOrder.lt none (some m') → newOrder.lt none (some m') := by
  simp only [order_lt]
  decide

theorem mem_inducedChoiceW_old : (true, ()) ∈ (market oldOrder).inducedChoiceW () Set.univ := by
  rw [true_mem_inducedChoiceW_univ_iff]
  simp only [order_le]
  decide

/-- The receiver no longer selects `true`. -/
theorem not_mem_inducedChoiceW_new :
    (true, ()) ∉ (market newOrder).inducedChoiceW () Set.univ := by
  rw [true_mem_inducedChoiceW_univ_iff]
  simp only [order_le]
  decide

end BelowOutside

namespace Overtaken

/-- `none < some false < some true`. -/
abbrev oldOrder : LinearOrder (Option Bool) := order 0 1 2 (by decide)

/-- `none < some true < some false`: the rival has passed `true`. -/
abbrev newOrder : LinearOrder (Option Bool) := order 0 2 1 (by decide)

/-- The change keeps the advantage of `true` over the outside option and satisfies the second and
third clauses of the relation. -/
theorem other_clauses :
    (oldOrder.lt none (some true) → newOrder.lt none (some true)) ∧
      (∀ ⦃m' m'' : Bool⦄, m' ≠ true → m'' ≠ true →
        (oldOrder.lt (some m'') (some m') ↔ newOrder.lt (some m'') (some m'))) ∧
      ∀ ⦃m' : Bool⦄, m' ≠ true → oldOrder.lt none (some m') → newOrder.lt none (some m') := by
  simp only [order_lt]
  decide

theorem mem_inducedChoiceW_old : (true, ()) ∈ (market oldOrder).inducedChoiceW () Set.univ := by
  rw [true_mem_inducedChoiceW_univ_iff]
  simp only [order_le]
  decide

/-- The receiver no longer selects `true`. -/
theorem not_mem_inducedChoiceW_new :
    (true, ()) ∉ (market newOrder).inducedChoiceW () Set.univ := by
  rw [true_mem_inducedChoiceW_univ_iff]
  simp only [order_le]
  decide

/-- When the rival is absent, the receiver still selects `true` under both rankings. -/
theorem mem_inducedChoiceW_singleton_old_and_new :
    (true, ()) ∈ (market oldOrder).inducedChoiceW () {(true, ())} ∧
    (true, ()) ∈ (market newOrder).inducedChoiceW () {(true, ())} := by
  have choose (ord : LinearOrder (Option Bool)) (ha : ord.le none (some true)) :
      (true, ()) ∈ (market ord).inducedChoiceW () {(true, ())} := by
    apply (market ord).mem_inducedChoiceW_iff.mpr
    refine ⟨by simp, ha, ?_⟩
    intro m hm
    have he : (m, ()) = (true, ()) := Set.mem_singleton_iff.mp hm
    have hfirst : m = true := congrArg Prod.fst he
    subst m
    exact ord.le_refl _
  exact ⟨choose oldOrder (by decide), choose newOrder (by decide)⟩

end Overtaken

end MathEconLibExamples.Matching.Improvements
