module

public import Auctionlib.Auction.Typeclasses

/-!
# Strict Monotonicity of Equilibrium Strategy (Lemma 6.2)

In a symmetric IPV auction with positive density, regular equilibrium,
and universal IC over nonneg bids, the equilibrium strategy is strictly
monotone on the type interval.

## Typeclasses used

- `HasIdenticalTypes` — common CDF
- `HasBoundedTypes` — types in intervals
- `HasPosDensity` — CDF has positive continuous density
- `HasOrderStatWinProb` — winProb = F(v₀)^(n-1) via threshold
- `ReducedForm.IsRegular` — monotone strategy/winProb, nonneg bids, continuous cost
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} [NeZero n] [n.AtLeastTwo]

namespace Auction

/-! ### Density typeclass -/

/-- The common CDF has a continuous density that is strictly positive
on the interior of the type interval. -/
class HasPosDensity (A : Auction Ω n) [HasIdenticalTypes A] where
  /-- density function -/
  f : ℝ → ℝ
  /-- CDF equals integral of density -/
  F_eq_integral : ∀ v ∈ Icc A.lowestType A.highestType,
    A.commonCDF v = ∫ t in A.lowestType..v, f t
  /-- density is continuous on the type interval -/
  f_continuous : ContinuousOn f (Icc A.lowestType A.highestType)
  /-- density is strictly positive on the interior -/
  f_pos : ∀ v ∈ Ioo A.lowestType A.highestType, 0 < f v

/-- The winning probability is characterized via order statistics:
`winProb(b) = F(v₀)^(n-1)` where `v₀` is the threshold type.
Bundles the type-interval agreement between `R` and `A`. -/
class HasOrderStatWinProb (A : Auction Ω n) [HasIdenticalTypes A]
    (R : ReducedForm) : Prop where
  typeInterval_eq : R.typeInterval = Icc A.lowestType A.highestType
  orderStat : ∀ b, ∃ v₀ ∈ Icc A.lowestType A.highestType,
    (∀ v ∈ Icc A.lowestType A.highestType, v < v₀ → R.strategy v < b) ∧
    (∀ v ∈ Icc A.lowestType A.highestType, R.strategy v < b → v ≤ v₀) ∧
    R.winProb b = A.commonCDF v₀ ^ (n - 1)

/-! ### Strict monotonicity proof -/

variable (A : Auction Ω n) [HasIdenticalTypes A] [HasBoundedTypes A]
  [HasAtomlessTypes A] [HasPosDensity A]

omit [n.AtLeastTwo] [HasBoundedTypes A] [HasAtomlessTypes A] [HasPosDensity A] in
/-- The reduced form's type interval equals the auction's common type interval. -/
lemma toReducedForm_typeInterval_eq
    (hx : A.rules.HasValidAllocation) (i : Fin n) :
    (A.toReducedForm hx i).typeInterval = Icc A.lowestType A.highestType := by
  show Icc (A.θmin i) (A.θmax i) = Icc (A.θmin 0) (A.θmax 0)
  rw [HasIdenticalTypes.θmin_eq (i := i), HasIdenticalTypes.θmax_eq (i := i)]

-- Shorthand
local notation "I" => Icc A.lowestType A.highestType
local notation "I°" => Ioo A.lowestType A.highestType
local notation "F" => A.commonCDF
local notation "lo" => A.lowestType
local notation "hi" => A.highestType

omit [n.AtLeastTwo] [HasBoundedTypes A] [HasAtomlessTypes A] in
private lemma F_strictMono_interior
    (v₁ v₂ : ℝ) (hv₁ : v₁ ∈ I°) (hv₂ : v₂ ∈ I°) (hlt : v₁ < v₂) :
    F v₁ < F v₂ := by
  have hv₁' := Ioo_subset_Icc_self hv₁
  have hv₂' := Ioo_subset_Icc_self hv₂
  rw [HasPosDensity.F_eq_integral v₁ hv₁', HasPosDensity.F_eq_integral v₂ hv₂']
  have hcont : ContinuousOn (HasPosDensity.f A) (Icc v₁ v₂) :=
    HasPosDensity.f_continuous.mono
      (Icc_subset_Icc (le_of_lt hv₁.1) (le_of_lt hv₂.2))
  have hint_pos : 0 < ∫ t in v₁..v₂, HasPosDensity.f A t :=
    intervalIntegral.integral_pos hlt hcont
      (fun x hx => le_of_lt (HasPosDensity.f_pos x
        ⟨lt_of_lt_of_le hv₁.1 (le_of_lt hx.1),
         lt_of_le_of_lt hx.2 hv₂.2⟩))
      ⟨(v₁ + v₂) / 2, ⟨by linarith, by linarith⟩,
        HasPosDensity.f_pos _
          ⟨by linarith [hv₁.1], by linarith [hv₂.2]⟩⟩
  have hv₂_nn : lo ≤ v₂ := le_of_lt hv₂.1
  have hcont_full : ContinuousOn (HasPosDensity.f A)
      (Set.uIcc lo v₂) := by
    rw [Set.uIcc_of_le hv₂_nn]
    exact HasPosDensity.f_continuous.mono
      (Icc_subset_Icc le_rfl (le_of_lt hv₂.2))
  have hint1 : IntervalIntegrable (HasPosDensity.f A) volume lo v₁ := by
    apply (hcont_full.mono _).intervalIntegrable
    apply Set.uIcc_subset_uIcc_left
    rw [Set.uIcc_of_le hv₂_nn]
    exact ⟨le_of_lt hv₁.1, le_of_lt hlt⟩
  have hint2 : IntervalIntegrable (HasPosDensity.f A) volume v₁ v₂ :=
    (show ContinuousOn (HasPosDensity.f A) (Set.uIcc v₁ v₂) by
      rw [Set.uIcc_of_le (le_of_lt hlt)]; exact hcont).intervalIntegrable
  linarith [intervalIntegral.integral_add_adjacent_intervals hint1 hint2]

omit [HasBoundedTypes A] [HasAtomlessTypes A] in
private lemma F_pow_strict_mono
    (v₁ v₂ : ℝ) (hv₁ : v₁ ∈ I°) (hv₂ : v₂ ∈ I°) (hlt : v₁ < v₂) :
    F v₁ ^ (n - 1) < F v₂ ^ (n - 1) :=
  pow_lt_pow_left₀ (A.F_strictMono_interior v₁ v₂ hv₁ hv₂ hlt)
    (A.commonCDF_nonneg v₁)
    (by have := Nat.AtLeastTwo.prop (n := n); omega)

set_option linter.unusedSectionVars false in
private lemma winProb_gap
    (R : ReducedForm) [A.HasOrderStatWinProb R]
    (v₁ v₂ : ℝ) (hv₁ : v₁ ∈ I°) (hv₂ : v₂ ∈ I°)
    (_hlt : v₁ < v₂) (b₀ : ℝ)
    (hβ₁ : R.strategy v₁ = b₀) (hβ₂ : R.strategy v₂ = b₀)
    (ε : ℝ) (hε : 0 < ε) :
    F v₂ ^ (n - 1) - F v₁ ^ (n - 1) ≤ R.winProb (b₀ + ε) - R.winProb b₀ := by
  have hGβ : A.HasOrderStatWinProb R := inferInstance
  obtain ⟨v₀, hv₀_mem, hv₀_below, _, hG_b₀⟩ := hGβ.orderStat b₀
  obtain ⟨v₀_ε, hv₀_ε_mem, _, hv₀_ε_above, hG_bε⟩ :=
    hGβ.orderStat (b₀ + ε)
  have hv₁' := Ioo_subset_Icc_self hv₁
  have hv₂' := Ioo_subset_Icc_self hv₂
  have hv₀_le_v₁ : v₀ ≤ v₁ :=
    le_of_not_gt fun h => by
      linarith [hv₀_below v₁ hv₁' h, hβ₁.symm.le]
  have hv₂_le_v₀_ε : v₂ ≤ v₀_ε :=
    hv₀_ε_above v₂ hv₂' (by rw [hβ₂]; linarith)
  rw [hG_bε, hG_b₀]
  linarith [pow_le_pow_left₀ (A.commonCDF_nonneg v₀)
              (A.commonCDF_mono hv₀_le_v₁) (n - 1),
            pow_le_pow_left₀ (A.commonCDF_nonneg v₂)
              (A.commonCDF_mono hv₂_le_v₀_ε) (n - 1)]

set_option linter.unusedSectionVars false in
private lemma ic_contradiction
    (R : ReducedForm) [ReducedForm.IsRegular R]
    (v₂ b₀ Δ : ℝ) (hv₂_mem : v₂ ∈ I) (hv₂_pos : lo < v₂)
    (hβ₂ : R.strategy v₂ = b₀) (hΔ : 0 < Δ)
    (hgap : ∀ ε > 0, Δ ≤ R.winProb (b₀ + ε) - R.winProb b₀)
    (hb₀_nonneg : 0 ≤ b₀) (hlo_nonneg : 0 ≤ lo)
    (ic : ∀ v ∈ I, ∀ b, 0 ≤ b → R.payoff v b ≤ R.U v) :
    False := by
  have hv₂_pos' : 0 < v₂ := lt_of_le_of_lt hlo_nonneg hv₂_pos
  obtain ⟨η, hη_pos, hη⟩ :=
    (Metric.tendsto_nhds_nhds.mp
      (ReducedForm.IsRegular.cost_continuous (R := R).tendsto b₀))
      (v₂ * Δ) (mul_pos hv₂_pos' hΔ)
  have hε : 0 < η / 2 := by linarith
  have hic := ic v₂ hv₂_mem (b₀ + η / 2) (by linarith)
  simp only [ReducedForm.payoff_eq, ReducedForm.U_eq] at hic
  rw [hβ₂] at hic
  have h_small := hη (show dist (b₀ + η / 2) b₀ < η by
    rw [Real.dist_eq, show b₀ + η / 2 - b₀ = η / 2 by ring,
      abs_of_pos hε]; linarith)
  rw [Real.dist_eq] at h_small
  linarith [abs_lt.mp h_small, hgap (η / 2) hε,
    mul_le_mul_of_nonneg_left (hgap (η / 2) hε) (le_of_lt hv₂_pos')]

/-! ### Main theorem -/

/-- **Lemma 6.2 — Strict monotonicity.** In a symmetric IPV auction with
positive density, the equilibrium strategy is strictly monotone on the
type interval. -/
theorem strictMonotonicity
    (R : ReducedForm) [ReducedForm.IsRegular R]
    [A.HasOrderStatWinProb R]
    (hlo_nonneg : 0 ≤ lo)
    (ic : ∀ v ∈ I, ∀ b, 0 ≤ b → R.payoff v b ≤ R.U v) :
    StrictMonoOn R.strategy I := by
  have hGβ : A.HasOrderStatWinProb R := inferInstance
  have β_mono : MonotoneOn R.strategy I := by
    intro a ha b hb hab
    exact ReducedForm.IsRegular.strategy_mono
      (show a ∈ R.typeInterval by rw [hGβ.typeInterval_eq]; exact ha)
      (show b ∈ R.typeInterval by rw [hGβ.typeInterval_eq]; exact hb) hab
  by_contra h
  -- If not strictly monotone, find interior flat pair
  simp only [StrictMonoOn] at h; push_neg at h
  obtain ⟨a, ha, b, hb, hab, hnlt⟩ := h
  have heq : R.strategy a = R.strategy b := le_antisymm (β_mono ha hb hab.le) hnlt
  -- Find interior points with equal strategy
  have hv₁ : (2 * a + b) / 3 ∈ I° :=
    ⟨by linarith [ha.1], by linarith [hb.2]⟩
  have hv₂ : (a + 2 * b) / 3 ∈ I° :=
    ⟨by linarith [ha.1], by linarith [hb.2]⟩
  have hlt : (2 * a + b) / 3 < (a + 2 * b) / 3 := by linarith
  -- Strategy is flat on [a, b], so equal at the interior points
  have hflat (w) (hw : w ∈ Icc a b) : R.strategy w = R.strategy a := by
    have hw_mem : w ∈ I := ⟨le_trans ha.1 hw.1, le_trans hw.2 hb.2⟩
    linarith [β_mono ha hw_mem hw.1, β_mono hw_mem hb hw.2]
  have heq' : R.strategy ((2 * a + b) / 3) = R.strategy ((a + 2 * b) / 3) :=
    (hflat _ ⟨by linarith, by linarith⟩).trans
      (hflat _ ⟨by linarith, by linarith⟩).symm
  set v₁ := (2 * a + b) / 3
  set v₂ := (a + 2 * b) / 3
  set b₀ := R.strategy v₁
  exact A.ic_contradiction R v₂ b₀
    (F v₂ ^ (n - 1) - F v₁ ^ (n - 1))
    (Ioo_subset_Icc_self hv₂) hv₂.1 heq'.symm
    (by linarith [A.F_pow_strict_mono v₁ v₂ hv₁ hv₂ hlt])
    (fun ε hε => A.winProb_gap R v₁ v₂ hv₁ hv₂ hlt b₀ rfl heq'.symm ε hε)
    (ReducedForm.IsRegular.strategy_nonneg v₁
      (show v₁ ∈ R.typeInterval by rw [hGβ.typeInterval_eq]; exact Ioo_subset_Icc_self hv₁))
    hlo_nonneg ic

/-- Distinct types in the interior have distinct bids. -/
theorem no_ties
    (R : ReducedForm) [ReducedForm.IsRegular R]
    [A.HasOrderStatWinProb R]
    (hlo_nonneg : 0 ≤ lo)
    (ic : ∀ v ∈ I, ∀ b, 0 ≤ b → R.payoff v b ≤ R.U v) :
    ∀ v₁ ∈ I°, ∀ v₂ ∈ I°, v₁ ≠ v₂ → R.strategy v₁ ≠ R.strategy v₂ := by
  intro v₁ hv₁ v₂ hv₂ hne
  exact ((A.strictMonotonicity R hlo_nonneg ic).injOn
    (Ioo_subset_Icc_self hv₁) (Ioo_subset_Icc_self hv₂)).mt hne

end Auction

end
