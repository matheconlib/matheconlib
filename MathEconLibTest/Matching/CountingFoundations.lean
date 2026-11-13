/-
Copyright (c) 2026 Georges Khater and MathEconLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georges Khater, MathEconLib contributors
-/
import MathEconLib.Matching.Classical.Marriage

/-!
# Public counting-foundations interface

These clients import only the marriage umbrella. They pin the threshold generators,
the reservation-cutoff transfer lemmas, the rank-list bridges and the counting
bounds. Checked applications to concrete markets are in
`MathEconLibTest.Matching.CountingFoundationsApplications`.
-/

namespace MathEconLibTest.Matching.CountingFoundations

open MathEconLib.Matching MarriageMarket

/-! ### Finiteness and counting bounds -/

section Bounds

variable {M W : Type*} (mkt : MarriageMarket M W)

example : Function.Injective (fun μ : mkt.StableMatching => fun m : M => μ.matching m) :=
  StableMatching.matching_apply_injective mkt

-- Finiteness needs only `Finite`, not `Fintype`.
example [Finite M] [Finite W] : Finite mkt.StableMatching := inferInstance

variable [Fintype M] [Fintype W]

example : Nat.card mkt.StableMatching ≤ (Fintype.card W + 1) ^ Fintype.card M :=
  StableMatching.card_le_partner_assignments mkt

example : Nat.card mkt.StableMatching ≤ 2 ^ (Fintype.card M * Fintype.card W) :=
  StableMatching.card_le_two_pow_pairs mkt

example : Nat.card {μ : mkt.StableMatching // SupIrred μ} ≤
    Fintype.card M * (Fintype.card W + 1) :=
  StableMatching.card_supIrred_le mkt

end Bounds

/-! ### Threshold generators -/

section Generators

variable {M W : Type*} (mkt : MarriageMarket M W) [Fintype M] [Fintype W]

example (m : M) (o : Option W) (μ : mkt.StableMatching) :
    StableMatching.MeetsThreshold mkt m o μ ↔ mkt.leM m o (μ.matching m) := Iff.rfl

example (m : M) (o : Option W) :
    StableMatching.thresholdGenerator mkt m o =
      sInf {μ | StableMatching.MeetsThreshold mkt m o μ} := rfl

example {m : M} {o : Option W} {μ : mkt.StableMatching}
    (hμ : StableMatching.MeetsThreshold mkt m o μ) :
    StableMatching.thresholdGenerator mkt m o ≤ μ :=
  StableMatching.thresholdGenerator_le mkt hμ

example (m : M) (o : Option W) :
    InfClosed {μ : mkt.StableMatching | StableMatching.MeetsThreshold mkt m o μ} :=
  StableMatching.infClosed_meetsThreshold mkt m o

example {m : M} {o : Option W}
    (hex : ∃ μ : mkt.StableMatching, StableMatching.MeetsThreshold mkt m o μ) :
    StableMatching.MeetsThreshold mkt m o (StableMatching.thresholdGenerator mkt m o) :=
  StableMatching.thresholdGenerator_meets mkt hex

example {m : M} {o : Option W} :
    StableMatching.MeetsThreshold mkt m o (StableMatching.thresholdGenerator mkt m o) ↔
      ∃ μ : mkt.StableMatching, StableMatching.MeetsThreshold mkt m o μ :=
  StableMatching.meetsThreshold_thresholdGenerator_iff mkt

example {m : M} {o : Option W}
    (hex : ¬ ∃ μ : mkt.StableMatching, StableMatching.MeetsThreshold mkt m o μ) :
    StableMatching.thresholdGenerator mkt m o = ⊤ :=
  StableMatching.thresholdGenerator_eq_top_of_not_exists mkt hex

example (μ : mkt.StableMatching) (m : M) :
    (StableMatching.thresholdGenerator mkt m (μ.matching m)).matching m = μ.matching m :=
  StableMatching.thresholdGenerator_matching mkt μ m

example (j : {μ : mkt.StableMatching // SupIrred μ}) :
    ∃ m : M, StableMatching.thresholdGenerator mkt m (j.1.matching m) = j.1 :=
  StableMatching.exists_thresholdGenerator_eq mkt j

example : Function.Injective (StableMatching.thresholdIndex mkt) :=
  StableMatching.thresholdIndex_injective mkt

end Generators

/-! ### Reservation-cutoff transfer -/

section Transfer

variable {M W : Type*} [DecidableEq M] (mkt : MarriageMarket M W)

example (pref : LinearOrder (Option W)) (threshold w : W) :
    @LE.le (Option W) (truncateOptionOrder pref threshold).toLE none (some w) ↔
      @LE.le (Option W) pref.toLE (some threshold) (some w) :=
  truncateOptionOrder_none_le_some pref threshold w

example (m m' : M) (threshold x y : W) :
    (mkt.truncateMan m threshold).leM m' (some x) (some y) ↔
      mkt.leM m' (some x) (some y) :=
  truncateMan_leM_some_some mkt m m' threshold x y

example (m m' : M) (threshold : W) (hne : m' ≠ m) (x y : Option W) :
    (mkt.truncateMan m threshold).leM m' x y ↔ mkt.leM m' x y :=
  truncateMan_leM_of_ne mkt m m' threshold hne x y

example (m : M) (threshold w : W) :
    (mkt.truncateMan m threshold).leM m none (some w) ↔
      mkt.leM m (some threshold) (some w) :=
  truncateMan_none_le_some mkt m threshold w

example (m : M) (threshold w : W) :
    (mkt.truncateMan m threshold).ltM m none (some w) ↔
      mkt.leM m (some threshold) (some w) :=
  truncateMan_none_lt_some mkt m threshold w

example {m : M} {threshold w : W} (hacceptable : mkt.leM m none (some threshold))
    (hw : (mkt.truncateMan m threshold).leM m none (some w)) :
    mkt.leM m none (some w) :=
  truncateMan_acceptable_of_acceptable mkt hacceptable hw

example (m : M) (threshold : W) :
    (∀ w, (mkt.truncateMan m threshold).leM m none (some w) →
      mkt.leM m none (some w)) ↔ mkt.leM m none (some threshold) :=
  truncateMan_acceptable_subset_iff mkt m threshold

example {m : M} {threshold w : W} (hunacceptable : mkt.leM m (some threshold) none)
    (hw : mkt.leM m none (some w)) :
    (mkt.truncateMan m threshold).leM m none (some w) :=
  truncateMan_acceptable_of_unacceptable mkt hunacceptable hw

example {μ : M ≃. W} {m : M} {threshold current : W}
    (hμ : mkt.IsStableMatching μ) (hcurrent : μ m = some current)
    (hthreshold : mkt.leM m (some threshold) (some current)) :
    (mkt.truncateMan m threshold).IsStableMatching μ :=
  stable_truncateMan_of_stable mkt hμ hcurrent hthreshold

example {μ : M ≃. W} {m : M} {threshold current : W}
    (hacceptable : mkt.leM m none (some threshold))
    (hμ : (mkt.truncateMan m threshold).IsStableMatching μ)
    (hcurrent : μ m = some current) : mkt.IsStableMatching μ :=
  stable_of_stable_truncateMan mkt hacceptable hμ hcurrent

end Transfer

/-! ### Rank-list bridges -/

section Ranks

example {n : Nat} : Function.Injective (@optionIndex n) := optionIndex_injective

example {n : Nat} (o : Option (Fin n)) : optionIndex o = finSuccEquivLast.symm o :=
  optionIndex_eq_finSuccEquivLast_symm o

variable (p : RankInput)

example (m : Fin p.men.length) (a b : Option (Fin p.men.length)) :
    p.market.leM m a b ↔
      rankAt p.men m.val (optionIndex a).val ≤ rankAt p.men m.val (optionIndex b).val :=
  p.leM_iff m a b

example (m : Fin p.men.length) (a b : Option (Fin p.men.length)) :
    p.market.ltM m a b ↔
      rankAt p.men m.val (optionIndex a).val < rankAt p.men m.val (optionIndex b).val :=
  p.ltM_iff m a b

example (w : Fin p.men.length) (a b : Option (Fin p.men.length)) :
    p.market.leW w a b ↔
      rankAt p.women w.val (optionIndex a).val ≤ rankAt p.women w.val (optionIndex b).val :=
  p.leW_iff w a b

example (w : Fin p.men.length) (a b : Option (Fin p.men.length)) :
    p.market.ltW w a b ↔
      rankAt p.women w.val (optionIndex a).val < rankAt p.women w.val (optionIndex b).val :=
  p.ltW_iff w a b

end Ranks

end MathEconLibTest.Matching.CountingFoundations
