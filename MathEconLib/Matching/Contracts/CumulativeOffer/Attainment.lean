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
-/

@[expose] public section

namespace MathEconLib.Matching.CumulativeOffer.CumulativeOfferProcess

open MathEconLib.Choice.ChoiceFunction MathEconLib.Preferences

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

end MathEconLib.Matching.CumulativeOffer.CumulativeOfferProcess
