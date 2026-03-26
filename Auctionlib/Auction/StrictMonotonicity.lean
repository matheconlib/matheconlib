module

public import Auctionlib.Auction.Basic

/-!
# Strict Monotonicity of Equilibrium Strategy (Lemma 6.2)

In a symmetric IPV auction with positive density and universal IC,
the equilibrium strategy is strictly monotone on the type interval.

## Main results

- `Auction.strictMonotonicity`: `strategy` is strictly increasing.
- `Auction.no_ties`: distinct interior types have distinct bids.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory

namespace Auction

variable (A : Auction) [A.n.AtLeastTwo] [HasPosDensity A] [HasOrderStatWinProb A]
  [Mechanism.IsRegular A.mechanism]

-- Shorthand for the type interval
local notation "I" => Icc A.mechanism.lowestType A.mechanism.highestType
local notation "I°" => Ioo A.mechanism.lowestType A.mechanism.highestType

instance : IsProbabilityMeasure A.typeDist := A.typeDist_prob

set_option linter.unusedSectionVars false in
private lemma strategy_constant_on_flat
    (v₁ v₂ : ℝ) (hv₁ : v₁ ∈ I) (hv₂ : v₂ ∈ I)
    (_hlt : v₁ < v₂) (heq : A.mechanism.strategy v₁ = A.mechanism.strategy v₂)
    (w : ℝ) (hw : w ∈ Icc v₁ v₂) : A.mechanism.strategy w = A.mechanism.strategy v₁ := by
  have hw_mem : w ∈ I := ⟨le_trans hv₁.1 hw.1, le_trans hw.2 hv₂.2⟩
  linarith [Mechanism.IsRegular.strategy_mono (M := A.mechanism) hv₁ hw_mem hw.1, Mechanism.IsRegular.strategy_mono (M := A.mechanism) hw_mem hv₂ hw.2]

set_option linter.unusedSectionVars false in
private lemma exists_interior_flat_pair
    (h : ¬StrictMonoOn A.mechanism.strategy I) :
    ∃ v₁ ∈ I°, ∃ v₂ ∈ I°, v₁ < v₂ ∧ A.mechanism.strategy v₁ = A.mechanism.strategy v₂ := by
  simp only [StrictMonoOn] at h
  push_neg at h
  obtain ⟨a, ha, b, hb, hab, hnlt⟩ := h
  have heq : A.mechanism.strategy a = A.mechanism.strategy b :=
    le_antisymm (Mechanism.IsRegular.strategy_mono (M := A.mechanism) ha hb hab.le) hnlt
  refine ⟨(2 * a + b) / 3, ?_, (a + 2 * b) / 3, ?_, ?_, ?_⟩
  · exact ⟨by linarith [ha.1], by linarith [hb.2]⟩
  · exact ⟨by linarith [ha.1], by linarith [hb.2]⟩
  · linarith
  · have hv₁_in : (2 * a + b) / 3 ∈ Icc a b := by constructor <;> linarith
    have hv₂_in : (a + 2 * b) / 3 ∈ Icc a b := by constructor <;> linarith
    rw [A.strategy_constant_on_flat a b ha hb hab heq _ hv₁_in,
        A.strategy_constant_on_flat a b ha hb hab heq _ hv₂_in]

set_option linter.unusedSectionVars false in
private lemma F_strictMono_interior
    (v₁ v₂ : ℝ) (hv₁ : v₁ ∈ I°) (hv₂ : v₂ ∈ I°)
    (hlt : v₁ < v₂) : A.F v₁ < A.F v₂ := by
  have hv₁' := Ioo_subset_Icc_self hv₁
  have hv₂' := Ioo_subset_Icc_self hv₂
  rw [HasPosDensity.F_eq_integral v₁ hv₁', HasPosDensity.F_eq_integral v₂ hv₂']
  have hcont : ContinuousOn (HasPosDensity.f A) (Icc v₁ v₂) :=
    HasPosDensity.f_continuous.mono (Icc_subset_Icc (le_of_lt hv₁.1) (le_of_lt hv₂.2))
  have hint_pos : 0 < ∫ t in v₁..v₂, HasPosDensity.f A t :=
    intervalIntegral.integral_pos hlt hcont
      (fun x hx => le_of_lt (HasPosDensity.f_pos x
        ⟨lt_of_lt_of_le hv₁.1 (le_of_lt hx.1), lt_of_le_of_lt hx.2 hv₂.2⟩))
      ⟨(v₁ + v₂) / 2, ⟨by linarith, by linarith⟩,
        HasPosDensity.f_pos _ ⟨by linarith [hv₁.1], by linarith [hv₂.2]⟩⟩
  have hv₂_nn : A.mechanism.lowestType ≤ v₂ := le_of_lt hv₂.1
  have hcont_full : ContinuousOn (HasPosDensity.f A)
      (Set.uIcc A.mechanism.lowestType v₂) := by
    rw [Set.uIcc_of_le hv₂_nn]
    exact HasPosDensity.f_continuous.mono (Icc_subset_Icc le_rfl (le_of_lt hv₂.2))
  have hint1 : IntervalIntegrable (HasPosDensity.f A) volume
      A.mechanism.lowestType v₁ := by
    apply (hcont_full.mono _).intervalIntegrable
    apply Set.uIcc_subset_uIcc_left
    rw [Set.uIcc_of_le hv₂_nn]
    exact ⟨le_of_lt hv₁.1, le_of_lt hlt⟩
  have hint2 : IntervalIntegrable (HasPosDensity.f A) volume v₁ v₂ :=
    (show ContinuousOn (HasPosDensity.f A) (Set.uIcc v₁ v₂) by
      rw [Set.uIcc_of_le (le_of_lt hlt)]
      exact hcont).intervalIntegrable
  linarith [intervalIntegral.integral_add_adjacent_intervals hint1 hint2]

private lemma F_pow_strict_mono
    (v₁ v₂ : ℝ) (hv₁ : v₁ ∈ I°) (hv₂ : v₂ ∈ I°)
    (hlt : v₁ < v₂) : A.F v₁ ^ (A.n - 1) < A.F v₂ ^ (A.n - 1) :=
  pow_lt_pow_left₀ (A.F_strictMono_interior v₁ v₂ hv₁ hv₂ hlt)
    (cdf_nonneg A.typeDist v₁)
    (by have := Nat.AtLeastTwo.prop (n := A.n); omega)

set_option linter.unusedSectionVars false in
private lemma winProb_gap
    (v₁ v₂ : ℝ) (hv₁ : v₁ ∈ I°) (hv₂ : v₂ ∈ I°)
    (_hlt : v₁ < v₂) (b₀ : ℝ)
    (hβ₁ : A.mechanism.strategy v₁ = b₀) (hβ₂ : A.mechanism.strategy v₂ = b₀)
    (ε : ℝ) (hε : 0 < ε) :
    A.F v₂ ^ (A.n - 1) - A.F v₁ ^ (A.n - 1) ≤
      A.mechanism.winProb (b₀ + ε) - A.mechanism.winProb b₀ := by
  have hwp := HasOrderStatWinProb.winProb_eq (A := A)
  obtain ⟨v₀, hv₀_mem, hv₀_below, _, hG_b₀⟩ := hwp b₀
  obtain ⟨v₀_ε, hv₀_ε_mem, _, hv₀_ε_above, hG_bε⟩ := hwp (b₀ + ε)
  have hv₁' := Ioo_subset_Icc_self hv₁
  have hv₂' := Ioo_subset_Icc_self hv₂
  have hv₀_le_v₁ : v₀ ≤ v₁ :=
    le_of_not_gt fun h => by linarith [hv₀_below v₁ hv₁' h, hβ₁.symm.le]
  have hv₂_le_v₀_ε : v₂ ≤ v₀_ε :=
    hv₀_ε_above v₂ hv₂' (by rw [hβ₂]; linarith)
  rw [hG_bε, hG_b₀]
  linarith [pow_le_pow_left₀ (cdf_nonneg A.typeDist v₀)
              (monotone_cdf A.typeDist hv₀_le_v₁) (A.n - 1),
            pow_le_pow_left₀ (cdf_nonneg A.typeDist v₂)
              (monotone_cdf A.typeDist hv₂_le_v₀_ε) (A.n - 1)]

set_option linter.unusedSectionVars false in
private lemma ic_contradiction
    (v₂ b₀ Δ : ℝ)
    (hv₂_mem : v₂ ∈ I)
    (hv₂_pos : A.mechanism.lowestType < v₂)
    (hβ₂ : A.mechanism.strategy v₂ = b₀)
    (hΔ : 0 < Δ)
    (hgap : ∀ ε > 0, Δ ≤ A.mechanism.winProb (b₀ + ε) - A.mechanism.winProb b₀)
    (hb₀_nonneg : 0 ≤ b₀)
    (hlo_nonneg : 0 ≤ A.mechanism.lowestType)
    (ic : ∀ v ∈ I, ∀ b, 0 ≤ b →
      A.mechanism.payoff v b ≤ A.mechanism.payoff v (A.mechanism.strategy v)) :
    False := by
  have hv₂_pos' : 0 < v₂ := lt_of_le_of_lt hlo_nonneg hv₂_pos
  have hcost_cont := Mechanism.IsRegular.cost_continuous (M := A.mechanism)
  obtain ⟨η, hη_pos, hη⟩ :=
    (Metric.tendsto_nhds_nhds.mp (hcost_cont.tendsto b₀))
      (v₂ * Δ) (mul_pos hv₂_pos' hΔ)
  have hε : 0 < η / 2 := by linarith
  have hic := ic v₂ hv₂_mem (b₀ + η / 2) (by linarith)
  simp only [Mechanism.payoff] at hic
  rw [hβ₂] at hic
  have h_small := hη (show dist (b₀ + η / 2) b₀ < η by
    rw [Real.dist_eq, show b₀ + η / 2 - b₀ = η / 2 by ring, abs_of_pos hε]
    linarith)
  rw [Real.dist_eq] at h_small
  linarith [abs_lt.mp h_small, hgap (η / 2) hε,
            mul_le_mul_of_nonneg_left (hgap (η / 2) hε) (le_of_lt hv₂_pos')]

/-! ### Main theorems -/

/-- **Lemma 6.2 — Strict monotonicity.** In a symmetric IPV auction with positive
density and universal IC over nonneg bids, the equilibrium strategy is strictly
monotone on the type interval. -/
theorem strictMonotonicity
    (hlo_nonneg : 0 ≤ A.mechanism.lowestType)
    (ic : ∀ v ∈ I, ∀ b, 0 ≤ b →
      A.mechanism.payoff v b ≤ A.mechanism.payoff v (A.mechanism.strategy v)) :
    StrictMonoOn A.mechanism.strategy I := by
  by_contra h
  obtain ⟨v₁, hv₁, v₂, hv₂, hlt, heq⟩ := A.exists_interior_flat_pair h
  set b₀ := A.mechanism.strategy v₁
  exact A.ic_contradiction v₂ b₀ (A.F v₂ ^ (A.n - 1) - A.F v₁ ^ (A.n - 1))
    (Ioo_subset_Icc_self hv₂) hv₂.1 heq.symm
    (by linarith [A.F_pow_strict_mono v₁ v₂ hv₁ hv₂ hlt])
    (fun ε hε => A.winProb_gap v₁ v₂ hv₁ hv₂ hlt b₀ rfl heq.symm ε hε)
    (Mechanism.IsRegular.strategy_nonneg (M := A.mechanism) v₁ (Ioo_subset_Icc_self hv₁))
    hlo_nonneg ic

/-- Distinct types in the interior have distinct bids. -/
theorem no_ties
    (hlo_nonneg : 0 ≤ A.mechanism.lowestType)
    (ic : ∀ v ∈ I, ∀ b, 0 ≤ b →
      A.mechanism.payoff v b ≤ A.mechanism.payoff v (A.mechanism.strategy v)) :
    ∀ v₁ ∈ I°, ∀ v₂ ∈ I°, v₁ ≠ v₂ →
      A.mechanism.strategy v₁ ≠ A.mechanism.strategy v₂ := by
  intro v₁ hv₁ v₂ hv₂ hne
  exact ((A.strictMonotonicity hlo_nonneg ic).injOn
    (Ioo_subset_Icc_self hv₁) (Ioo_subset_Icc_self hv₂)).mt hne

end Auction

end
