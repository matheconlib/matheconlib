module

public import Auctionlib.Auction.SymmetricIPV

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

/-- The winning probability `G` is characterized via order statistics:
`G(b) = F(v₀)^(n-1)` where `v₀` is the threshold type and `β` is the strategy. -/
def HasOrderStatWinProb (A : Auction Ω n) [HasIdenticalTypes A]
    (G : ℝ → ℝ) (β : ℝ → ℝ) : Prop :=
  ∀ b, ∃ v₀ ∈ Icc A.lowestType A.highestType,
    (∀ v ∈ Icc A.lowestType A.highestType, v < v₀ → β v < b) ∧
    (∀ v ∈ Icc A.lowestType A.highestType, β v < b → v ≤ v₀) ∧
    G b = A.commonCDF v₀ ^ (n - 1)

/-! ### Strict monotonicity proof -/

variable (A : Auction Ω n) [HasIdenticalTypes A] [HasBoundedTypes A]
  [HasAtomlessTypes A] [HasPosDensity A]

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

set_option linter.unusedSectionVars false in
private lemma strategy_constant_on_flat
    (hx : A.rules.HasValidAllocation) (i : Fin n)
    [ReducedForm.IsRegular (A.toReducedForm hx i)]
    (v₁ v₂ : ℝ) (hv₁ : v₁ ∈ I) (hv₂ : v₂ ∈ I)
    (_hlt : v₁ < v₂) (heq : (A.toReducedForm hx i).strategy v₁ =
      (A.toReducedForm hx i).strategy v₂)
    (w : ℝ) (hw : w ∈ Icc v₁ v₂) :
    (A.toReducedForm hx i).strategy w =
      (A.toReducedForm hx i).strategy v₁ := by
  have hw_mem : w ∈ I := ⟨le_trans hv₁.1 hw.1, le_trans hw.2 hv₂.2⟩
  have hconv := A.toReducedForm_typeInterval_eq hx i
  linarith [ReducedForm.IsRegular.strategy_mono (hconv ▸ hv₁) (hconv ▸ hw_mem) hw.1,
            ReducedForm.IsRegular.strategy_mono (hconv ▸ hw_mem) (hconv ▸ hv₂) hw.2]

set_option linter.unusedSectionVars false in
private lemma exists_interior_flat_pair
    (hx : A.rules.HasValidAllocation) (i : Fin n)
    [ReducedForm.IsRegular (A.toReducedForm hx i)]
    (h : ¬StrictMonoOn (A.toReducedForm hx i).strategy I) :
    ∃ v₁ ∈ I°, ∃ v₂ ∈ I°,
      v₁ < v₂ ∧ (A.toReducedForm hx i).strategy v₁ =
        (A.toReducedForm hx i).strategy v₂ := by
  simp only [StrictMonoOn] at h; push_neg at h
  obtain ⟨a, ha, b, hb, hab, hnlt⟩ := h
  have hconv := A.toReducedForm_typeInterval_eq hx i
  have heq := le_antisymm
    (ReducedForm.IsRegular.strategy_mono (hconv ▸ ha) (hconv ▸ hb) hab.le) hnlt
  refine ⟨(2 * a + b) / 3, ?_, (a + 2 * b) / 3, ?_, ?_, ?_⟩
  · exact ⟨by linarith [ha.1], by linarith [hb.2]⟩
  · exact ⟨by linarith [ha.1], by linarith [hb.2]⟩
  · linarith
  · have h1 := A.strategy_constant_on_flat hx i a b ha hb hab heq
        ((2 * a + b) / 3) (show _ ∈ Icc a b by constructor <;> linarith)
    have h2 := A.strategy_constant_on_flat hx i a b ha hb hab heq
        ((a + 2 * b) / 3) (show _ ∈ Icc a b by constructor <;> linarith)
    rw [h1, h2]

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

private lemma F_pow_strict_mono
    (v₁ v₂ : ℝ) (hv₁ : v₁ ∈ I°) (hv₂ : v₂ ∈ I°) (hlt : v₁ < v₂) :
    F v₁ ^ (n - 1) < F v₂ ^ (n - 1) :=
  pow_lt_pow_left₀ (A.F_strictMono_interior v₁ v₂ hv₁ hv₂ hlt)
    (A.commonCDF_nonneg v₁)
    (by have := Nat.AtLeastTwo.prop (n := n); omega)

set_option linter.unusedSectionVars false in
private lemma winProb_gap
    {G : ℝ → ℝ} {β : ℝ → ℝ}
    (hGβ : A.HasOrderStatWinProb G β)
    (v₁ v₂ : ℝ) (hv₁ : v₁ ∈ I°) (hv₂ : v₂ ∈ I°)
    (_hlt : v₁ < v₂) (b₀ : ℝ)
    (hβ₁ : β v₁ = b₀) (hβ₂ : β v₂ = b₀)
    (ε : ℝ) (hε : 0 < ε) :
    F v₂ ^ (n - 1) - F v₁ ^ (n - 1) ≤ G (b₀ + ε) - G b₀ := by
  obtain ⟨v₀, hv₀_mem, hv₀_below, _, hG_b₀⟩ := hGβ b₀
  obtain ⟨v₀_ε, hv₀_ε_mem, _, hv₀_ε_above, hG_bε⟩ := hGβ (b₀ + ε)
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
    {G : ℝ → ℝ} {β : ℝ → ℝ} {C : ℝ → ℝ}
    (hC_cont : Continuous C)
    (v₂ b₀ Δ : ℝ) (hv₂_mem : v₂ ∈ I) (hv₂_pos : lo < v₂)
    (hβ₂ : β v₂ = b₀) (hΔ : 0 < Δ)
    (hgap : ∀ ε > 0, Δ ≤ G (b₀ + ε) - G b₀)
    (hb₀_nonneg : 0 ≤ b₀) (hlo_nonneg : 0 ≤ lo)
    (ic : ∀ v ∈ I, ∀ b, 0 ≤ b →
      v * G b - C b ≤ v * G (β v) - C (β v)) :
    False := by
  have hv₂_pos' : 0 < v₂ := lt_of_le_of_lt hlo_nonneg hv₂_pos
  obtain ⟨η, hη_pos, hη⟩ :=
    (Metric.tendsto_nhds_nhds.mp (hC_cont.tendsto b₀))
      (v₂ * Δ) (mul_pos hv₂_pos' hΔ)
  have hε : 0 < η / 2 := by linarith
  have hic := ic v₂ hv₂_mem (b₀ + η / 2) (by linarith)
  rw [hβ₂] at hic
  have h_small := hη (show dist (b₀ + η / 2) b₀ < η by
    rw [Real.dist_eq, show b₀ + η / 2 - b₀ = η / 2 by ring,
      abs_of_pos hε]; linarith)
  rw [Real.dist_eq] at h_small
  linarith [abs_lt.mp h_small, hgap (η / 2) hε,
    mul_le_mul_of_nonneg_left (hgap (η / 2) hε) (le_of_lt hv₂_pos')]

/-! ### Main theorem -/

/-- **Lemma 6.2 — Strict monotonicity.** In a symmetric IPV auction with
positive density, the equilibrium strategy `β` is strictly monotone. -/
theorem strictMonotonicity
    {G : ℝ → ℝ} {β : ℝ → ℝ} {C : ℝ → ℝ}
    (hGβ : A.HasOrderStatWinProb G β)
    (β_mono : MonotoneOn β I)
    (β_nonneg : ∀ v ∈ I, 0 ≤ β v)
    (hC_cont : Continuous C)
    (hlo_nonneg : 0 ≤ lo)
    (ic : ∀ v ∈ I, ∀ b, 0 ≤ b →
      v * G b - C b ≤ v * G (β v) - C (β v)) :
    StrictMonoOn β I := by
  by_contra h
  -- If not strictly monotone, find interior flat pair
  simp only [StrictMonoOn] at h; push_neg at h
  obtain ⟨a, ha, b, hb, hab, hnlt⟩ := h
  have heq : β a = β b := le_antisymm (β_mono ha hb hab.le) hnlt
  -- Find interior points with equal β
  have hv₁ : (2 * a + b) / 3 ∈ I° :=
    ⟨by linarith [ha.1], by linarith [hb.2]⟩
  have hv₂ : (a + 2 * b) / 3 ∈ I° :=
    ⟨by linarith [ha.1], by linarith [hb.2]⟩
  have hlt : (2 * a + b) / 3 < (a + 2 * b) / 3 := by linarith
  -- β is flat on [a, b], so equal at the interior points
  have hflat (w) (hw : w ∈ Icc a b) : β w = β a := by
    have hw_mem : w ∈ I := ⟨le_trans ha.1 hw.1, le_trans hw.2 hb.2⟩
    linarith [β_mono ha hw_mem hw.1, β_mono hw_mem hb hw.2]
  have heq' : β ((2 * a + b) / 3) = β ((a + 2 * b) / 3) :=
    (hflat _ ⟨by linarith, by linarith⟩).trans
      (hflat _ ⟨by linarith, by linarith⟩).symm
  set v₁ := (2 * a + b) / 3
  set v₂ := (a + 2 * b) / 3
  set b₀ := β v₁
  exact A.ic_contradiction hC_cont v₂ b₀
    (F v₂ ^ (n - 1) - F v₁ ^ (n - 1))
    (Ioo_subset_Icc_self hv₂) hv₂.1 heq'.symm
    (by linarith [A.F_pow_strict_mono v₁ v₂ hv₁ hv₂ hlt])
    (fun ε hε => A.winProb_gap hGβ v₁ v₂ hv₁ hv₂ hlt b₀ rfl heq'.symm ε hε)
    (β_nonneg v₁ (Ioo_subset_Icc_self hv₁))
    hlo_nonneg ic

/-- Distinct types in the interior have distinct bids. -/
theorem no_ties
    {G : ℝ → ℝ} {β : ℝ → ℝ} {C : ℝ → ℝ}
    (hGβ : A.HasOrderStatWinProb G β)
    (β_mono : MonotoneOn β I)
    (β_nonneg : ∀ v ∈ I, 0 ≤ β v)
    (hC_cont : Continuous C)
    (hlo_nonneg : 0 ≤ lo)
    (ic : ∀ v ∈ I, ∀ b, 0 ≤ b →
      v * G b - C b ≤ v * G (β v) - C (β v)) :
    ∀ v₁ ∈ I°, ∀ v₂ ∈ I°, v₁ ≠ v₂ → β v₁ ≠ β v₂ := by
  intro v₁ hv₁ v₂ hv₂ hne
  exact ((A.strictMonotonicity hGβ β_mono β_nonneg hC_cont hlo_nonneg ic).injOn
    (Ioo_subset_Icc_self hv₁) (Ioo_subset_Icc_self hv₂)).mt hne

end Auction

end
