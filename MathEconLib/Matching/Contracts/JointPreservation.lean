/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Choice.Matching.PathIndependentEnvelope
public import MathEconLib.Matching.Contracts.Completion

/-!
# Joint preservation of stable outcomes under completion

Each target outcome imposes rejections on the buyer choices. For a contract that
the seller would take in place of their assignment, the buyer must reject it
when it is added to the buyer's part of the outcome. Substitutability extends
this rejection to every larger menu. Restrict the substitute envelope by all
these rejections, then take its greatest path-independent minorant.

The resulting buyer profile is a completion exactly when one substitutable IRC
completion preserves every target. When it exists it is the greatest such
profile, and its stable set is the intersection of the stable sets of all
preserving profiles. The original buyers need neither IRC nor substitutability.
-/

@[expose] public section

namespace MathEconLib.Matching.Market

open MathEconLib.Choice

variable {B S X : Type*} (M : Market B S X)

private theorem buyerSide_insert {b : B} {x : X} {A : Set X} (hb : M.buyer x = b) :
    M.buyerSide b (insert x A) = insert x (M.buyerSide b A) := by
  ext z
  simp only [mem_buyerSide, Set.mem_insert_iff]
  constructor
  · rintro ⟨rfl | hz, hzb⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨hz, hzb⟩
  · rintro (rfl | ⟨hz, hzb⟩)
    · exact ⟨Or.inl rfl, hb⟩
    · exact ⟨Or.inr hz, hzb⟩

private theorem choiceB_insert_buyerSide {b : B} {x : X} {A : Set X}
    (hcons : (M.choiceB b).Consistent) (hb : M.buyer x = b) :
    M.choiceB b (insert x (M.buyerSide b A)) = M.choiceB b (insert x A) := by
  rw [← M.buyerSide_insert hb, M.choiceB_buyerSide hcons]

/-- Restrict the substitute envelope by the singleton rejections required by
the target outcomes, including at every superset of each rejection menu. -/
def jointPreservationEnvelope (targets : Set (Set X)) (b : B) : ChoiceFunction X where
  toFun Y := {x | x ∈ (M.choiceB b).substituteEnvelope M.seller Y ∧
    ¬ ∃ A ∈ targets, M.buyer x = b ∧ x ∉ A ∧
      x ∈ M.choiceS (M.seller x) (insert x A) ∧ insert x (M.buyerSide b A) ⊆ Y}
  choose_subset := fun Y _ hx => ((M.choiceB b).substituteEnvelope M.seller).choose_subset Y hx.1

/-- The target rejections persist when the menu grows. -/
theorem jointPreservationEnvelope_substitutable (targets : Set (Set X)) (b : B) :
    (M.jointPreservationEnvelope targets b).Substitutable := by
  apply ChoiceFunction.substitutable_iff_chernoff.mpr
  intro Y Z hYZ x hx
  have hsub := ChoiceFunction.substituteEnvelope_substitutable M.seller (M.choiceB b)
  refine ⟨hsub.mem_of_subset hYZ hx.1.1 hx.2, ?_⟩
  rintro ⟨A, hA, hb, hxA, hxS, hmenu⟩
  exact hx.1.2 ⟨A, hA, hb, hxA, hxS, hmenu.trans hYZ⟩

/-- The canonical candidate for a joint preserving completion. -/
def jointPreservationChoices (targets : Set (Set X)) (b : B) : ChoiceFunction X :=
  (M.jointPreservationEnvelope targets b).pathIndependentMinorant

theorem jointPreservationChoices_pathIndependent (targets : Set (Set X)) (b : B) :
    (M.jointPreservationChoices targets b).PathIndependent :=
  ChoiceFunction.pathIndependentMinorant_pathIndependent _

/-- Substitutable IRC buyer completions preserving every target allocation. -/
def preservingBuyerCompletions (targets : Set (Set X)) : Set (B → ChoiceFunction X) :=
  {D | ∃ (hcomp : ∀ b, (M.choiceB b).IsCompletionOf M.seller (D b))
      (hsub : ∀ b, (D b).Substitutable),
    (∀ b, (D b).Consistent) ∧
      ∀ A ∈ targets, (M.withBuyerCompletions D hcomp hsub).Stable A}

private theorem le_jointPreservationEnvelope {targets : Set (Set X)}
    {D : B → ChoiceFunction X} (hD : D ∈ M.preservingBuyerCompletions targets) (b : B) :
    D b ≤ M.jointPreservationEnvelope targets b := by
  obtain ⟨hcomp, hsub, hcons, hstable⟩ := hD
  let N := M.withBuyerCompletions D hcomp hsub
  intro Y x hx
  refine ⟨(hcomp b).le_substituteEnvelope (hsub b) Y hx, ?_⟩
  rintro ⟨A, hA, hb, hxA, hxS, hmenu⟩
  have hxD : x ∈ D b (insert x (M.buyerSide b A)) :=
    (hsub b).mem_of_subset hmenu hx (Set.mem_insert x _)
  have hlocal : D b (insert x (M.buyerSide b A)) = D b (insert x A) :=
    N.choiceB_insert_buyerSide (hcons b) hb
  have hxN : x ∈ N.choiceB (N.buyer x) (insert x A) := by
    change x ∈ D (M.buyer x) (insert x A)
    rwa [hb, ← hlocal]
  exact (hstable A hA).2 {x} (N.blocks_singleton_iff.mpr ⟨hxA, hxN, hxS⟩)

private theorem le_jointPreservationChoices {targets : Set (Set X)}
    {D : B → ChoiceFunction X} (hD : D ∈ M.preservingBuyerCompletions targets) :
    D ≤ M.jointPreservationChoices targets := by
  intro b
  have hpath : (D b).PathIndependent := by
    obtain ⟨_, hsub, hcons, _⟩ := hD
    exact (hsub b).pathIndependent (hcons b)
  exact ChoiceFunction.le_pathIndependentMinorant hpath (M.le_jointPreservationEnvelope hD b)

private theorem jointPreservationChoices_isCompletionOf {targets : Set (Set X)}
    {D : B → ChoiceFunction X} (hD : D ∈ M.preservingBuyerCompletions targets) (b : B) :
    (M.choiceB b).IsCompletionOf M.seller (M.jointPreservationChoices targets b) := by
  have hbound := M.le_jointPreservationEnvelope hD b
  obtain ⟨hcomp, hsub, hcons, _⟩ := hD
  exact ChoiceFunction.pathIndependentMinorant_isCompletionOf_of_le_substituteEnvelope
    (fun _ _ hx => hx.1) (hcomp b) ((hsub b).pathIndependent (hcons b)) hbound

/-- When the canonical choices complete the original choices, they are the
greatest substitutable IRC completion profile preserving the targets. -/
theorem isGreatest_jointPreservationChoices {targets : Set (Set X)}
    (hunit : M.SellersUnitDemand) (hSsub : ∀ s, (M.choiceS s).Substitutable)
    (hIR : ∀ A ∈ targets, M.IndRational A)
    (hcomp : ∀ b, (M.choiceB b).IsCompletionOf M.seller (M.jointPreservationChoices targets b)) :
    IsGreatest (M.preservingBuyerCompletions targets) (M.jointPreservationChoices targets) := by
  let D := M.jointPreservationChoices targets
  have hsub : ∀ b, (D b).Substitutable :=
    fun b => (M.jointPreservationChoices_pathIndependent targets b).substitutable
  have hcons : ∀ b, (D b).Consistent :=
    fun b => (M.jointPreservationChoices_pathIndependent targets b).consistent
  let N := M.withBuyerCompletions D hcomp hsub
  refine ⟨⟨hcomp, hsub, hcons, ?_⟩, fun _ h => M.le_jointPreservationChoices h⟩
  intro A hA
  have hfeas := (hIR A hA).manyToOneFeasible M hunit
  apply PairwiseStable.stable_of_substitutable N ⟨hsub, hSsub⟩
  refine ⟨(M.indRational_withBuyerCompletions_iff D hcomp hsub hfeas).mpr (hIR A hA), ?_⟩
  intro x hx
  obtain ⟨hxA, hxB, hxS⟩ := N.blocks_singleton_iff.mp hx
  have hlocal : N.choiceB (M.buyer x) (insert x (M.buyerSide (M.buyer x) A)) =
      N.choiceB (M.buyer x) (insert x A) :=
    N.choiceB_insert_buyerSide (hcons (M.buyer x)) rfl
  have hxD : x ∈ D (M.buyer x) (insert x (M.buyerSide (M.buyer x) A)) := by
    change x ∈ N.choiceB (M.buyer x) _
    rwa [hlocal]
  have hxE := ChoiceFunction.pathIndependentMinorant_le
    (M.jointPreservationEnvelope targets (M.buyer x)) _ hxD
  exact hxE.2 ⟨A, hA, rfl, hxA, hxS, Set.Subset.rfl⟩

/-- A single substitutable IRC completion preserves the targets exactly when
each canonical choice rule passes the completion test. Target individual
rationality suffices, in particular when the targets were originally stable. -/
theorem preservingBuyerCompletions_nonempty_iff {targets : Set (Set X)}
    (hunit : M.SellersUnitDemand) (hSsub : ∀ s, (M.choiceS s).Substitutable)
    (hIR : ∀ A ∈ targets, M.IndRational A) :
    (M.preservingBuyerCompletions targets).Nonempty ↔
      ∀ b, (M.choiceB b).IsCompletionOf M.seller (M.jointPreservationChoices targets b) :=
  ⟨fun ⟨_, h⟩ => M.jointPreservationChoices_isCompletionOf h,
    fun h => ⟨_, (M.isGreatest_jointPreservationChoices hunit hSsub hIR h).1⟩⟩

/-- Stability under the greatest preserving completion is stability under
every preserving completion. The statement uses the original target family
only to specify which completions are being compared. -/
theorem stable_withJointPreservationChoices_iff {targets : Set (Set X)}
    (hunit : M.SellersUnitDemand) (hSsub : ∀ s, (M.choiceS s).Substitutable)
    (hIR : ∀ A ∈ targets, M.IndRational A)
    (hcomp : ∀ b, (M.choiceB b).IsCompletionOf M.seller (M.jointPreservationChoices targets b))
    {A : Set X} :
    (M.withBuyerCompletions (M.jointPreservationChoices targets) hcomp
      (fun b => (M.jointPreservationChoices_pathIndependent targets b).substitutable)).Stable A ↔
      ∀ (D : B → ChoiceFunction X)
        (hDcomp : ∀ b, (M.choiceB b).IsCompletionOf M.seller (D b))
        (hDsub : ∀ b, (D b).Substitutable),
        D ∈ M.preservingBuyerCompletions targets →
          (M.withBuyerCompletions D hDcomp hDsub).Stable A := by
  let P := M.jointPreservationChoices targets
  let hPsub := fun b => (M.jointPreservationChoices_pathIndependent targets b).substitutable
  have hP := M.isGreatest_jointPreservationChoices hunit hSsub hIR hcomp
  constructor
  · intro hA D hDcomp hDsub hD
    have hDP := hP.2 hD
    have hfeas : M.ManyToOneFeasible A :=
      Stable.manyToOneFeasible (M.withBuyerCompletions P hcomp hPsub) hunit hA
    have hAIR := (M.indRational_withBuyerCompletions_iff P hcomp hPsub hfeas).mp hA.1
    refine ⟨(M.indRational_withBuyerCompletions_iff D hDcomp hDsub hfeas).mpr hAIR, ?_⟩
    rintro Z ⟨hne, hdisj, hB, hS⟩
    exact hA.2 Z ⟨hne, hdisj, fun b x hx => hDP b _ (hB b hx), hS⟩
  · exact fun h => h P hcomp hPsub hP.1

end MathEconLib.Matching.Market
