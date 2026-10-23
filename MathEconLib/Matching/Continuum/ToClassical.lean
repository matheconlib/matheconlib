/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLib.Matching.Classical.Marriage.Basic
import MathEconLib.Matching.Continuum.Stability

/-!
# Agreement with classical marriage stability

A measured matching map is a complete classical matching after forgetting its measure structure.
When classical preferences and utilities give the same comparisons, including the outside option,
their pointwise stability predicates agree. The representation hypothesis is explicit: utility
profiles with ties need not represent a classical market's linear preferences. No finiteness or
existence theorem is used. Pointwise stability implies distributional stability under the
measurability hypotheses of `PointwiseStable.toMatchingMeasure`.
-/

namespace MathEconLib.Matching.Continuum.MatchingMap

open MeasureTheory

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
variable {μ : ProbabilityMeasure A} {ν : ProbabilityMeasure B}

/-- Forgetting measure structure preserves blocking under the same partner comparisons. -/
theorem isBlockingPair_iff_classical (f : MatchingMap μ ν) (u : Utilities A B)
    (mkt : MarriageMarket A B) (hpref : mkt.toPartnerComparisons = u.toPartnerComparisons)
    (a : A) (b : B) :
    f.IsBlockingPair u a b ↔
      mkt.IsBlockingPair f.toMeasurableEquiv.toEquiv.toPEquiv a b := by
  simp only [MarriageMarket.IsBlockingPair, hpref, ← Equiv.toPEquiv_symm]
  rfl

/-- Classical stability and pointwise stability agree for a utility representation of the market. -/
theorem pointwiseStable_iff_classical (f : MatchingMap μ ν) (u : Utilities A B)
    (mkt : MarriageMarket A B) (hpref : mkt.toPartnerComparisons = u.toPartnerComparisons) :
    f.PointwiseStable u ↔ mkt.IsStableMatching f.toMeasurableEquiv.toEquiv.toPEquiv := by
  have hIL (a : A) (b : B) : mkt.leM a none (some b) ↔ u.outsideLeft a ≤ u.left a b := by
    have h := not_congr (Iff.of_eq (congrArg (fun p ↦ p.left a (some b) none) hpref))
    change (¬mkt.ltM a (some b) none) ↔ (¬u.left a b < u.outsideLeft a) at h
    simpa only [MarriageMarket.ltM, MarriageMarket.leM, not_lt] using h
  have hIR (b : B) (a : A) : mkt.leW b none (some a) ↔ u.outsideRight b ≤ u.right b a := by
    have h := not_congr (Iff.of_eq (congrArg (fun p ↦ p.right b (some a) none) hpref))
    change (¬mkt.ltW b (some a) none) ↔ (¬u.right b a < u.outsideRight b) at h
    simpa only [MarriageMarket.ltW, MarriageMarket.leW, not_lt] using h
  have hi : mkt.IndividuallyRational f.toMeasurableEquiv.toEquiv.toPEquiv ↔
      f.IndividuallyRational u := by
    constructor
    · intro h a
      constructor
      · exact (hIL a (f a)).mp (by simpa using h.1 a)
      · exact (hIR (f a) a).mp (by
          simpa [MarriageMarket.IndividuallyRationalForW, ← Equiv.toPEquiv_symm] using h.2 (f a))
    · intro h
      constructor
      · intro a
        simpa using (hIL a (f a)).mpr (h a).1
      · intro b
        simpa [← Equiv.toPEquiv_symm, symm] using
          (hIR b (f.symm b)).mpr (by simpa [graph] using (h (f.symm b)).2)
  change (_ ∧ _) ↔ (_ ∧ _)
  rw [hi, mkt.unblocked_iff_no_blockingPair]
  simp only [← f.isBlockingPair_iff_classical u mkt hpref, Unblocked]

end MathEconLib.Matching.Continuum.MatchingMap
