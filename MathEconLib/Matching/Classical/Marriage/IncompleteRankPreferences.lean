/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLib.Matching.Classical.Marriage.RankPreferences

/-!
# Finite strict ranks with incomplete acceptable lists

`OptionalRanking n` orders all `n` partners together with `none`. Its outside option may occupy
any position: partners above it are acceptable, and partners below it are unacceptable. This
is a strict order, without ties. Ordering the unacceptable partners supplies a strict total
order to the existing marriage API; it does not make these partners acceptable.

`IncompleteRankProfile` composes two families of these rankings and adapts them to the existing
`MarriageMarket`. No alternative matching, stability, or deferred-acceptance definition is used.
The complete profiles from `RankPreferences` embed explicitly by putting `none` last.

Ranks count positions starting at one, including the outside option in its actual position.
Thus an unmatched agent has one plus their number of acceptable partners, rather than a
population-wide penalty. An individually rational match has rank at most that outside rank.
The average includes all agents and is zero for an empty side. These are ordinal positions,
not cardinal welfare or a matched-agent average. Receiver statistics use `p.symm` and `μ.symm`.
-/

namespace MathEconLib.Matching.MarriageMarket

open scoped BigOperators

/-- A strict ranking of all partners and the outside option, from best to worst. -/
abbrev OptionalRanking (n : ℕ) := Option (Fin n) ≃ Fin (n + 1)

namespace OptionalRanking

variable {n : ℕ}

/-- One-based ordinal position, including the outside option in its actual position. -/
def rank (r : OptionalRanking n) (o : Option (Fin n)) : ℕ := (r o).val + 1

theorem rank_pos (r : OptionalRanking n) (o : Option (Fin n)) : 0 < r.rank o :=
  Nat.zero_lt_succ _

theorem rank_le (r : OptionalRanking n) (o : Option (Fin n)) : r.rank o ≤ n + 1 :=
  (r o).isLt

theorem rank_injective (r : OptionalRanking n) : Function.Injective r.rank :=
  Nat.succ_injective.comp (Fin.val_injective.comp r.injective)

/-- The marriage API prefers larger values, so smaller ordinal ranks induce its dual order. -/
@[instance_reducible] def rankOrder (r : OptionalRanking n) : LinearOrder (Option (Fin n)) :=
  LinearOrder.lift' (fun o ↦ OrderDual.toDual (r.rank o)) r.rank_injective

/-- Embed a complete strict ranking by placing the outside option after every partner. -/
def ofComplete (r : Equiv.Perm (Fin n)) : OptionalRanking n :=
  (Equiv.optionCongr r).trans finSuccEquivLast.symm

/-- Distinct complete rankings remain distinct after inserting the outside option last. -/
theorem ofComplete_injective : Function.Injective (ofComplete (n := n)) :=
  fun _ _ h ↦ Equiv.optionCongr_injective
    (Equiv.ext fun o ↦ finSuccEquivLast.symm.injective (congrArg (fun r ↦ r o) h))

@[simp] theorem rank_ofComplete (r : Equiv.Perm (Fin n)) (o : Option (Fin n)) :
    (ofComplete r).rank o = RankProfile.rank r o := by
  cases o <;> simp [rank, ofComplete, RankProfile.rank]

theorem rankOrder_ofComplete (r : Equiv.Perm (Fin n)) :
    (ofComplete r).rankOrder = RankProfile.rankOrder r := by
  apply LinearOrder.ext
  change ∀ x y, (ofComplete r).rank y ≤ (ofComplete r).rank x ↔
    RankProfile.rank r y ≤ RankProfile.rank r x
  simp

end OptionalRanking

/-- Strict ranking families allowing each agent a different acceptable set. -/
structure IncompleteRankProfile (m n : ℕ) where
  /-- Each man's strict ranking includes his outside option. -/
  manRank : Fin m → OptionalRanking n
  /-- Each woman's strict ranking includes her outside option. -/
  womanRank : Fin n → OptionalRanking m
  deriving DecidableEq

namespace IncompleteRankProfile

variable {m n : ℕ}

/-- Exchange the two populations and their ranking families. -/
def symm (p : IncompleteRankProfile m n) : IncompleteRankProfile n m :=
  ⟨p.womanRank, p.manRank⟩

@[simp] theorem symm_symm (p : IncompleteRankProfile m n) : p.symm.symm = p := rfl

/-- The profile space is the product of the two unrestricted ranking families. -/
def equivRanks (m n : ℕ) : IncompleteRankProfile m n ≃
    ((Fin m → OptionalRanking n) × (Fin n → OptionalRanking m)) where
  toFun p := (p.manRank, p.womanRank)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (IncompleteRankProfile m n) :=
  Fintype.ofEquiv _ (equivRanks m n).symm

instance : Inhabited (IncompleteRankProfile m n) :=
  ⟨⟨fun _ ↦ finSuccEquivLast.symm, fun _ ↦ finSuccEquivLast.symm⟩⟩

/-- An individual optional ranking, indexed by the disjoint union of both populations. -/
def Ranking (m n : ℕ) : Fin m ⊕ Fin n → Type :=
  Sum.elim (fun _ ↦ OptionalRanking n) (fun _ ↦ OptionalRanking m)

instance (a : Fin m ⊕ Fin n) : Fintype (Ranking m n a) := by
  cases a <;> dsimp [Ranking] <;> infer_instance

/-- The same profile as one unrestricted family indexed by every agent. -/
def equivAgentRanks (m n : ℕ) : IncompleteRankProfile m n ≃ (∀ a, Ranking m n a) :=
  (equivRanks m n).trans (Equiv.sumPiEquivProdPi (Ranking m n)).symm

@[simp] theorem equivAgentRanks_inl (p : IncompleteRankProfile m n) (i : Fin m) :
    equivAgentRanks m n p (Sum.inl i) = p.manRank i := rfl

@[simp] theorem equivAgentRanks_inr (p : IncompleteRankProfile m n) (j : Fin n) :
    equivAgentRanks m n p (Sum.inr j) = p.womanRank j := rfl

/-- Interpret the optional ranks as existing strict marriage preferences. -/
def toMarriageMarket (p : IncompleteRankProfile m n) : MarriageMarket (Fin m) (Fin n) where
  prefM i := (p.manRank i).rankOrder
  prefW j := (p.womanRank j).rankOrder

@[simp] theorem symm_toMarriageMarket (p : IncompleteRankProfile m n) :
    p.symm.toMarriageMarket = p.toMarriageMarket.symm := rfl

@[simp] theorem toMarriageMarket_leM (p : IncompleteRankProfile m n) (i : Fin m)
    (x y : Option (Fin n)) :
    p.toMarriageMarket.leM i x y ↔ (p.manRank i).rank y ≤ (p.manRank i).rank x := Iff.rfl

@[simp] theorem toMarriageMarket_leW (p : IncompleteRankProfile m n) (j : Fin n)
    (x y : Option (Fin m)) :
    p.toMarriageMarket.leW j x y ↔ (p.womanRank j).rank y ≤ (p.womanRank j).rank x := Iff.rfl

@[simp] theorem toMarriageMarket_ltM (p : IncompleteRankProfile m n) (i : Fin m)
    (x y : Option (Fin n)) :
    p.toMarriageMarket.ltM i x y ↔ (p.manRank i).rank y < (p.manRank i).rank x := Iff.rfl

@[simp] theorem toMarriageMarket_ltW (p : IncompleteRankProfile m n) (j : Fin n)
    (x y : Option (Fin m)) :
    p.toMarriageMarket.ltW j x y ↔ (p.womanRank j).rank y < (p.womanRank j).rank x := Iff.rfl

/-- Acceptability depends on the position of this proposer's outside option. -/
@[simp] theorem toMarriageMarket_acceptableM (p : IncompleteRankProfile m n)
    (i : Fin m) (j : Fin n) :
    p.toMarriageMarket.AcceptableM i j ↔
      (p.manRank i).rank (some j) < (p.manRank i).rank none := Iff.rfl

/-- Acceptability depends on the position of this receiver's outside option. -/
@[simp] theorem toMarriageMarket_acceptableW (p : IncompleteRankProfile m n)
    (j : Fin n) (i : Fin m) :
    p.toMarriageMarket.AcceptableW j i ↔
      (p.womanRank j).rank (some i) < (p.womanRank j).rank none := Iff.rfl

/-- Sum of one-based ordinal positions, with an unmatched agent at their own outside rank. -/
def totalProposerRank (p : IncompleteRankProfile m n) (μ : Fin m ≃. Fin n) : ℕ :=
  ∑ i, (p.manRank i).rank (μ i)

/-- Average ordinal position over all proposers, including unmatched agents; zero if empty. -/
noncomputable def averageProposerRank (p : IncompleteRankProfile m n)
    (μ : Fin m ≃. Fin n) : ℝ :=
  𝔼 i, ((p.manRank i).rank (μ i) : ℝ)

/-- The average divides the total by the proposer population, including unequal populations. -/
theorem averageProposerRank_eq_total_div (p : IncompleteRankProfile m n)
    (μ : Fin m ≃. Fin n) :
    p.averageProposerRank μ = (p.totalProposerRank μ : ℝ) / m := by
  simp [averageProposerRank, Fintype.expect_eq_sum_div_card, totalProposerRank, Nat.cast_sum]

/-- Pointwise weak preference implies weakly lower total ordinal position. -/
theorem totalProposerRank_le (p : IncompleteRankProfile m n) {μ ν : Fin m ≃. Fin n}
    (h : ∀ i, p.toMarriageMarket.leM i (ν i) (μ i)) :
    p.totalProposerRank μ ≤ p.totalProposerRank ν :=
  Finset.sum_le_sum fun i _ ↦ (p.toMarriageMarket_leM i (ν i) (μ i)).mp (h i)

/-- Pointwise weak preference implies weakly lower average ordinal position. -/
theorem averageProposerRank_le (p : IncompleteRankProfile m n) {μ ν : Fin m ≃. Fin n}
    (h : ∀ i, p.toMarriageMarket.leM i (ν i) (μ i)) :
    p.averageProposerRank μ ≤ p.averageProposerRank ν := by
  rw [averageProposerRank_eq_total_div, averageProposerRank_eq_total_div]
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (p.totalProposerRank_le h))
    (Nat.cast_nonneg _)

end IncompleteRankProfile

namespace RankProfile

variable {m n : ℕ}

/-- Complete profiles specialize incomplete profiles by putting every outside option last. -/
def toIncomplete (p : RankProfile m n) : IncompleteRankProfile m n :=
  ⟨fun i ↦ OptionalRanking.ofComplete (p.manRank i),
    fun j ↦ OptionalRanking.ofComplete (p.womanRank j)⟩

/-- The complete specialization is an embedding, preserving distinct preference profiles. -/
theorem toIncomplete_injective : Function.Injective (toIncomplete (m := m) (n := n)) :=
  fun _ _ h ↦ (equivRanks m n).injective (Prod.ext
    (funext fun i ↦ OptionalRanking.ofComplete_injective
      (congrArg (fun p ↦ p.manRank i) h))
    (funext fun j ↦ OptionalRanking.ofComplete_injective
      (congrArg (fun p ↦ p.womanRank j) h)))

@[simp] theorem symm_toIncomplete (p : RankProfile m n) :
    p.symm.toIncomplete = p.toIncomplete.symm := rfl

/-- The explicit embedding preserves the existing marriage-market interpretation. -/
@[simp] theorem toIncomplete_toMarriageMarket (p : RankProfile m n) :
    p.toIncomplete.toMarriageMarket = p.toMarriageMarket := by
  simp only [toIncomplete, IncompleteRankProfile.toMarriageMarket, toMarriageMarket,
    OptionalRanking.rankOrder_ofComplete]

/-- The complete specialization has no unacceptable partners on either side. -/
theorem toIncomplete_noUnacceptablePartners (p : RankProfile m n) :
    p.toIncomplete.toMarriageMarket.NoUnacceptablePartners := by
  simpa only [toIncomplete_toMarriageMarket] using p.toMarriageMarket_noUnacceptablePartners

/-- The explicit embedding preserves the rank of every (possibly unmatched) assignment. -/
@[simp] theorem toIncomplete_totalProposerRank (p : RankProfile m n) (μ : Fin m ≃. Fin n) :
    p.toIncomplete.totalProposerRank μ = p.totalProposerRank μ := by
  simp [IncompleteRankProfile.totalProposerRank, totalProposerRank, toIncomplete]

/-- Complete-profile average ranks agree exactly, including empty or unequal populations. -/
@[simp] theorem toIncomplete_averageProposerRank (p : RankProfile m n) (μ : Fin m ≃. Fin n) :
    p.toIncomplete.averageProposerRank μ = p.averageProposerRank μ := by
  simp [IncompleteRankProfile.averageProposerRank, averageProposerRank, toIncomplete]

end RankProfile
end MathEconLib.Matching.MarriageMarket
