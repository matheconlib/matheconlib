/-
Copyright (c) 2026 Ayan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ayan
-/
module

public import MathEconLib.Matching.Classical.Marriage.Preferences

/-!
# Unambiguous improvements and selection from a fixed menu

A receiver's preference `new` is an unambiguous improvement over `old` for a proposer `m` when
`m` keeps every advantage he had, the other proposers keep their relative order, and no other
proposer who was acceptable becomes unacceptable. Other proposers may become newly acceptable.

## Main definitions and statements

* `IsUnambiguousImprovement new old m`: Kominers (2024), Definition 1, represented by three
  fields on `LinearOrder (Option M)`; `none` is the outside option and larger options are preferred.
* `MarriageMarket.mem_inducedChoiceW_of_forall_lt_some`: a receiver who selected `m` from a
  fixed menu still selects him if every option he beat before remains below him.
* `MarriageMarket.bestW_eq_some_of_forall_lt_some`: the same statement for the finite selector.

The fixed-menu results use only the first clause of the relation, supplied through
`IsUnambiguousImprovement.lt_some_of_lt_some`. The structural choice result needs no finiteness;
the `bestW` wrapper requires only finitely many proposers. The worked examples include a rival
becoming newly acceptable and show why the first clause must include both rivals and `none`.
These are local choice results, not a comparison of deferred-acceptance outcomes across markets.

## References

Scott Duke Kominers (2024), *Respect for Improvements and Comparative Statics in Matching
Markets*, *Journal of Mechanism and Institution Design* **9**(1), 83–104, Definition 1 and
footnote 8, p. 90. [DOI: 10.22574/jmid.2024.12.005](https://doi.org/10.22574/jmid.2024.12.005).
The relation follows that definition, including its one-way preservation of rivals'
acceptability. It does not impose the stronger requirement that their outside-option comparisons
remain unchanged. This module derives the fixed-menu consequences for classical one-to-one choice.
-/

@[expose] public section

namespace MathEconLib.Matching

universe u v

/-- `IsUnambiguousImprovement new old m` says that the preference `new` is an unambiguous
improvement over `old` for `m` (Kominers 2024, Definition 1). Here `none` is the outside option
and larger options are preferred. -/
structure IsUnambiguousImprovement {M : Type u} (new old : LinearOrder (Option M)) (m : M) :
    Prop where
  /-- Every option, a proposer or the outside option, that `m` beats under `old` he still beats
  under `new`. -/
  lt_some_of_lt_some : ∀ ⦃o : Option M⦄, old.lt o (some m) → new.lt o (some m)
  /-- Two proposers other than `m` keep their relative ranking. -/
  some_lt_some_iff : ∀ ⦃m' m'' : M⦄, m' ≠ m → m'' ≠ m →
    (old.lt (some m'') (some m') ↔ new.lt (some m'') (some m'))
  /-- A proposer other than `m` who is acceptable under `old` remains acceptable under `new`.
  The implication runs one way, so other proposers may become newly acceptable. -/
  none_lt_some_of_none_lt_some : ∀ ⦃m' : M⦄, m' ≠ m → old.lt none (some m') → new.lt none (some m')

namespace MarriageMarket

variable {M : Type u} {W : Type v}

/-- If everything `m` beats under `old` he still beats under `new`, then `w` still selects `m`
from a fixed menu. This is the first clause of an unambiguous improvement, on its own. -/
theorem mem_inducedChoiceW_of_forall_lt_some (old new : MarriageMarket M W) {w : W} {m : M}
    {Y : Set (M × W)}
    (h : ∀ ⦃o : Option M⦄, (old.prefW w).lt o (some m) → (new.prefW w).lt o (some m))
    (hm : (m, w) ∈ old.inducedChoiceW w Y) : (m, w) ∈ new.inducedChoiceW w Y := by
  obtain ⟨hY, hnone, hbest⟩ := old.mem_inducedChoiceW_iff.mp hm
  have key : ∀ o : Option M, old.leW w o (some m) → new.leW w o (some m) := by
    intro o ho
    by_cases he : o = some m
    · subst he
      exact (new.prefW w).le_refl _
    · have hlt : (old.prefW w).lt o (some m) :=
        @lt_of_le_of_ne _ (old.prefW w).toPartialOrder _ _ ho he
      exact @le_of_lt _ (new.prefW w).toPreorder _ _ (h hlt)
  exact new.mem_inducedChoiceW_iff.mpr ⟨hY, key _ hnone, fun m' hm' => key _ (hbest m' hm')⟩

/-- The finite selector `bestW` keeps returning `m` when everything `m` beats under `old` he
still beats under `new`. -/
theorem bestW_eq_some_of_forall_lt_some [Fintype M] (old new : MarriageMarket M W) {w : W}
    {m : M} {Y : Set (M × W)}
    (h : ∀ ⦃o : Option M⦄, (old.prefW w).lt o (some m) → (new.prefW w).lt o (some m))
    (hm : old.bestW w Y = some m) : new.bestW w Y = some m := by
  have hold : (m, w) ∈ old.inducedChoiceW w Y := old.mem_inducedChoiceW.mpr ⟨rfl, hm.symm⟩
  exact (new.mem_inducedChoiceW.mp (old.mem_inducedChoiceW_of_forall_lt_some new h hold)).2.symm

end MarriageMarket

end MathEconLib.Matching
