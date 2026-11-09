/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Matching.Contracts.CumulativeOffer.Basic
public import MathEconLib.Matching.Contracts.ManyToOne
public import MathEconLib.Preferences.Refinement

/-!
# Attainment on cumulative-offer proposal menus

The full unoffered own-contract menu includes contracts the seller would decline.
The outside option is always feasible in the induced option choice. With a priority
that ranks it first within its indifference class, it is optimal exactly when no
strictly acceptable contract remains. This characterizes terminality for unheld
sellers and leaves eligibility and relational admissibility unchanged.

## Main definitions

`unofferedOwnMenu` retains the full own-contract menu before acceptability filtering.

## Main statements

`mem_tieBreak_optionChoice_iff` identifies refined proposals.
`Eligible.exists_validSingleton_of_hasBundleOptimum` supplies a valid step under attainment.
`Eligible.not_hasBundleOptimum_of_optionChoice_eq_empty` diagnoses nonattainment.
-/

@[expose] public section

namespace MathEconLib.Matching.CumulativeOffer.CumulativeOfferProcess

open MathEconLib.Choice MathEconLib.Choice.ChoiceFunction MathEconLib.Preferences

variable {B S X U : Type*} (P : CumulativeOfferProcess B S X)

/-- All unoffered own contracts, before filtering for strict acceptability. -/
def unofferedOwnMenu (A : Set X) (s : S) : Set (P.Own s) :=
  Subtype.val ⁻¹' Aᶜ

/-- A finite own menu attains under any strict order, even if the carrier is infinite. -/
theorem hasBundleOptimum_unofferedOwnMenu_of_finite {s : S} (R : LinearOrder (Option (P.Own s)))
    {A : Set X} (hfin : (P.unofferedOwnMenu A s).Finite) :
    HasBundleOptimum R optionBundle (P.unofferedOwnMenu A s) :=
  hasBundleOptimum_optionBundle_of_finite R hfin

/-- The process's own menu is the market's restriction of the global unoffered menu. -/
theorem hasSellerOptimum_compl_iff
    (R : ∀ s, LinearOrder (Option (P.Own s))) (A : Set X) (s : S) :
    Market.HasSellerOptimum P.seller R s Aᶜ ↔
      HasBundleOptimum (R s) optionBundle (P.unofferedOwnMenu A s) :=
  Iff.rfl

/-- Giving the outside option priority at indifference preserves strict acceptability. -/
theorem tieBreak_some_le_none_iff [LinearOrder U] {s : S}
    (priority : Option (P.Own s) ↪ U)
    (hnone : ∀ x, priority (some x) ≤ priority none) (x : P.Own s) :
    ((P.pref s).tieBreak priority).le (some x) none ↔ (P.pref s).le (some x) none :=
  ⟨(P.pref s).le_of_tieBreak_le priority,
    fun h ↦ ((P.pref s).tieBreak_le_iff priority _ _).mpr ⟨h, fun _ ↦ hnone x⟩⟩

/-- The outside option is optimal exactly when no strictly acceptable contract remains. -/
theorem outsideOptionOptimal_tieBreak_iff [LinearOrder U] (A : Set X) (s : S)
    (priority : Option (P.Own s) ↪ U) (hnone : ∀ x, priority (some x) ≤ priority none) :
    OutsideOptionOptimal ((P.pref s).tieBreak priority) (P.unofferedOwnMenu A s) ↔
      ¬ (P.remaining A s).Nonempty := by
  constructor
  · rintro h ⟨x, hx, hacc⟩
    exact hacc.2 ((P.tieBreak_some_le_none_iff priority hnone x).mp (h x hx))
  · intro h x hx
    apply (P.tieBreak_some_le_none_iff priority hnone x).mpr
    by_contra hle
    exact h ⟨x, hx, (P.pref s).not_le.mp hle⟩

/-- At termination every unheld seller prefers the outside option to its unoffered contracts. -/
theorem terminal_iff_sellerDeclines [LinearOrder U]
    (priority : ∀ s, Option (P.Own s) ↪ U)
    (hnone : ∀ s x, priority s (some x) ≤ priority s none) (A : Set X) :
    P.Terminal A ↔ ∀ s, P.NoHeldContract A s →
      Market.SellerDeclines P.seller (fun t ↦ (P.pref t).tieBreak (priority t)) s Aᶜ := by
  constructor
  · intro h s hu
    exact (P.outsideOptionOptimal_tieBreak_iff A s (priority s) (hnone s)).mpr
      (fun hne ↦ h s ⟨hu, hne⟩)
  · intro h s hs
    exact (P.outsideOptionOptimal_tieBreak_iff A s (priority s) (hnone s)).mp
      (h s hs.1) hs.2

/-- Refined option choice selects exactly the greatest-priority weak maximizer, if one exists.
The statement is pointwise and does not assume attainment. -/
theorem mem_tieBreak_optionChoice_iff [LinearOrder U] (A : Set X) (s : S)
    (priority : Option (P.Own s) ↪ U) (hnone : ∀ x, priority (some x) ≤ priority none)
    (x : P.Own s) :
    x ∈ ofOptionLinearOrder ((P.pref s).tieBreak priority) (P.unofferedOwnMenu A s) ↔
      x ∈ maximizers (P.contractPreference s) (P.remaining A s) ∧
        ∀ y ∈ maximizers (P.contractPreference s) (P.remaining A s),
          priority (some y) ≤ priority (some x) := by
  rw [mem_ofOptionLinearOrder]
  constructor
  · rintro ⟨hx, hnx, hmax⟩
    have hnle : ¬ (P.pref s).le (some x) none := by
      intro h
      exact Option.some_ne_none _ (((P.pref s).tieBreak priority).le_antisymm _ _
        ((P.tieBreak_some_le_none_iff priority hnone x).mpr h) hnx)
    have hbest : x ∈ maximizers (P.contractPreference s) (P.remaining A s) :=
      ⟨⟨hx, (P.pref s).not_le.mp hnle⟩,
        fun {_} hy ↦ (P.pref s).le_of_tieBreak_le priority (hmax _ hy.1)⟩
    refine ⟨hbest, fun y hy ↦ ?_⟩
    exact (((P.pref s).tieBreak_le_iff priority (some y) (some x)).mp
      (hmax y hy.1.1)).2 ⟨hbest.2 hy.1, hy.2 hbest.1⟩
  · rintro ⟨hx, hpriority⟩
    have hacc := hx.1.2
    refine ⟨hx.1.1, ((P.pref s).tieBreak_le_iff priority _ _).mpr
      ⟨hacc.1, fun h ↦ (hacc.2 h.2).elim⟩, ?_⟩
    intro y hy
    apply ((P.pref s).tieBreak_le_iff priority _ _).mpr
    by_cases hyacc : (P.pref s).lt none (some y)
    · have hyr : y ∈ P.remaining A s := ⟨hy, hyacc⟩
      refine ⟨hx.2 hyr, fun htie ↦ hpriority y ⟨hyr, ?_⟩⟩
      intro _ hz
      exact (P.pref s).le_trans (hx.2 hz) htie.2
    · have hy0 : (P.pref s).le (some y) none := by
        by_contra hnle
        exact hyacc ((P.pref s).not_le.mp hnle)
      have hyx := (P.pref s).toPreference.lt_of_le_of_lt hy0 hacc
      exact ⟨hyx.1, fun htie ↦ (hyx.2 htie.2).elim⟩

/-- At an eligible seller's menu, empty refined choice means failure of attainment.
This distinguishes nonattainment from optimal nonparticipation without finiteness. -/
theorem Eligible.not_hasBundleOptimum_of_optionChoice_eq_empty [LinearOrder U]
    {A : Set X} {s : S} (h : P.Eligible A s)
    (priority : Option (P.Own s) ↪ U) (hnone : ∀ x, priority (some x) ≤ priority none)
    (hempty : ofOptionLinearOrder ((P.pref s).tieBreak priority)
      (P.unofferedOwnMenu A s) = ∅) :
    ¬ HasBundleOptimum ((P.pref s).tieBreak priority) optionBundle
      (P.unofferedOwnMenu A s) := by
  intro hatt
  have hout := (ofOptionLinearOrder_eq_empty_iff_of_hasBundleOptimum _ hatt).mp hempty
  exact (P.outsideOptionOptimal_tieBreak_iff A s priority hnone).mp hout h.2

/-- An eligible seller with an attained refined optimum can take a singleton step.
No finiteness of the seller set or contract type is required. -/
theorem Eligible.exists_validSingleton_of_hasBundleOptimum [LinearOrder U]
    {A : Set X} {s : S} (h : P.Eligible A s)
    (priority : Option (P.Own s) ↪ U) (hnone : ∀ x, priority (some x) ≤ priority none)
    (hatt : HasBundleOptimum ((P.pref s).tieBreak priority) optionBundle
      (P.unofferedOwnMenu A s)) :
    ∃ x, P.seller x = s ∧ P.ValidBatch A {x} := by
  have hne : (ofOptionLinearOrder ((P.pref s).tieBreak priority)
      (P.unofferedOwnMenu A s)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    have hout := (ofOptionLinearOrder_eq_empty_iff_of_hasBundleOptimum _ hatt).mp hempty
    exact (P.outsideOptionOptimal_tieBreak_iff A s priority hnone).mp hout h.2
  obtain ⟨x, hx⟩ := hne
  have hbest := ((P.mem_tieBreak_optionChoice_iff A s priority hnone x).mp hx).1
  exact ⟨x.val, x.property, (P.validBatch_singleton_iff A x.val).mpr
    ⟨s, x, rfl, h.1, hbest⟩⟩

end MathEconLib.Matching.CumulativeOffer.CumulativeOfferProcess
