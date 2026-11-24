/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import MathEconLib.Mechanism.Core.DeterministicIC
public import MathEconLib.Mechanism.Core.UtilityCompatibility

/-!
# Quasilinear recovery of deterministic comparison incentives

Supplying the existing quasilinear consequence utility and truthful identity strategies recovers
`DirectMechanism.IsDSIC` exactly, with no private-values restriction. Ex-post comparison IC
recovers truthful Nash at every true profile in the retained utility-game view. These bridges
leave the legacy declarations unchanged and keep true types fixed under report deviations.

## Main statements

* `Mechanism.isDSICWith_iff_quasilinear`: exact legacy dominant-strategy IC recovery.
* `Mechanism.isExPostICWith_iff_quasilinear`: exact recovery of truthful utility-game Nash.

## Tags

mechanism design, incentive compatibility, quasilinear utility, compatibility
-/

@[expose] public section

namespace MathEconLib.Mechanism

universe uI uT uO

variable {I : Type uI} {T : I → Type uT} {O : Type uO} [DecidableEq I]

/-- Quasilinear comparisons and identity reporting recover the retained direct DSIC predicate.
The environment may have interdependent values. -/
theorem isDSICWith_iff_quasilinear (M : DirectMechanism I T O)
    (E : QuasilinearEnvironment I T O) :
    M.IsDSICWith (fun i θ c d ↦ E.consequenceUtility i θ c ≤ E.consequenceUtility i θ d)
      (fun _ ↦ id) ↔ DirectMechanism.IsDSIC E M :=
  (M.isDSICWith_iff_isDominant_of_representation _ E.consequenceUtility
    (fun _ _ _ _ ↦ Iff.rfl) (fun _ ↦ id)).trans (by
      simpa only [toStrategicGame_quasilinear, id_eq] using
        (DirectMechanism.isDSIC_iff_isDominant E M).symm)

/-- Quasilinear comparison ex-post IC is truthful Nash in every retained utility game.
This does not identify ex-post IC with dominance for interdependent values. -/
theorem isExPostICWith_iff_quasilinear (M : DirectMechanism I T O)
    (E : QuasilinearEnvironment I T O) :
    M.IsExPostICWith
      (fun i θ c d ↦ E.consequenceUtility i θ c ≤ E.consequenceUtility i θ d)
      (fun _ ↦ id) ↔ ∀ θ, (E.utilityGame M θ).IsNash θ := by
  simpa only [toStrategicGame_quasilinear, id_eq] using
    M.isExPostICWith_iff_isNash_of_representation _ E.consequenceUtility
      (fun _ _ _ _ ↦ Iff.rfl) (fun _ ↦ id)

end MathEconLib.Mechanism

end
