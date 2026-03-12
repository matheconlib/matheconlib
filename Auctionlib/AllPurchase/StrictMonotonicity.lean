import Mathlib

open MeasureTheory Set

structure StrictMonoSetup where
  v_bar : ℝ
  hv_bar_pos : 0 < v_bar
  n : ℕ
  hn : 2 ≤ n
  F : ℝ → ℝ
  F_mono : Monotone F
  F_zero : F 0 = 0
  F_v_bar : F v_bar = 1
  F_range : ∀ v ∈ Icc 0 v_bar, F v ∈ Icc 0 1
  f : ℝ → ℝ
  F_eq_integral : ∀ v ∈ Icc 0 v_bar, F v = ∫ t in (0 : ℝ)..v, f t
  f_pos : ∀ v ∈ Ioo 0 v_bar, 0 < f v
  f_continuous : ContinuousOn f (Icc 0 v_bar)
  β : ℝ → ℝ
  β_mono : MonotoneOn β (Icc 0 v_bar)
  β_nonneg : ∀ v ∈ Icc 0 v_bar, 0 ≤ β v
  G : ℝ → ℝ
  G_mono : Monotone G
  G_range : ∀ b, G b ∈ Icc 0 1
  G_eq : ∀ b, ∃ v₀ ∈ Icc 0 v_bar,
    (∀ v ∈ Icc 0 v_bar, v < v₀ → β v < b) ∧
    (∀ v ∈ Icc 0 v_bar, β v < b → v ≤ v₀) ∧
    G b = F v₀ ^ (n - 1)
  C : ℝ → ℝ
  C_continuous : Continuous C
  ic : ∀ v ∈ Icc 0 v_bar, ∀ b, 0 ≤ b →
    v * G b - C b ≤ v * G (β v) - C (β v)

namespace StrictMonoSetup

variable (S : StrictMonoSetup)

/-- If β is constant on endpoints of [v₁, v₂], it is constant throughout. -/
lemma beta_constant_on_flat
    (v₁ v₂ : ℝ) (hv₁ : v₁ ∈ Icc 0 S.v_bar) (hv₂ : v₂ ∈ Icc 0 S.v_bar)
    (_hlt : v₁ < v₂) (heq : S.β v₁ = S.β v₂)
    (w : ℝ) (hw : w ∈ Icc v₁ v₂) : S.β w = S.β v₁ := by
  have hw_mem : w ∈ Icc 0 S.v_bar := ⟨le_trans hv₁.1 hw.1, le_trans hw.2 hv₂.2⟩
  linarith [S.β_mono hv₁ hw_mem hw.1, S.β_mono hw_mem hv₂ hw.2]

/-- If β is monotone but not strictly monotone, there exist interior points with equal β. -/
lemma exists_interior_flat_pair (h : ¬StrictMonoOn S.β (Icc 0 S.v_bar)) :
    ∃ v₁ ∈ Ioo 0 S.v_bar, ∃ v₂ ∈ Ioo 0 S.v_bar,
      v₁ < v₂ ∧ S.β v₁ = S.β v₂ := by
  simp only [StrictMonoOn] at h
  push_neg at h
  obtain ⟨a, ha, b, hb, hab, hnlt⟩ := h
  have heq : S.β a = S.β b := le_antisymm (S.β_mono ha hb hab.le) hnlt
  refine ⟨(2 * a + b) / 3, ?_, (a + 2 * b) / 3, ?_, ?_, ?_⟩
  · exact ⟨by linarith [ha.1], by linarith [hb.2]⟩
  · exact ⟨by linarith [ha.1], by linarith [hb.2]⟩
  · linarith
  · have hv₁_in : (2 * a + b) / 3 ∈ Icc a b := by constructor <;> linarith
    have hv₂_in : (a + 2 * b) / 3 ∈ Icc a b := by constructor <;> linarith
    rw [S.beta_constant_on_flat a b ha hb hab heq _ hv₁_in,
        S.beta_constant_on_flat a b ha hb hab heq _ hv₂_in]

/-- F is strictly monotone on (0, v̄) via positivity of ∫ f on [v₁, v₂]. -/
lemma F_strictMono_interior
    (v₁ v₂ : ℝ) (hv₁ : v₁ ∈ Ioo 0 S.v_bar) (hv₂ : v₂ ∈ Ioo 0 S.v_bar)
    (hlt : v₁ < v₂) : S.F v₁ < S.F v₂ := by
  have hv₁' : v₁ ∈ Icc 0 S.v_bar := Ioo_subset_Icc_self hv₁
  have hv₂' : v₂ ∈ Icc 0 S.v_bar := Ioo_subset_Icc_self hv₂
  rw [S.F_eq_integral v₁ hv₁', S.F_eq_integral v₂ hv₂']
  have hcont : ContinuousOn S.f (Icc v₁ v₂) :=
    S.f_continuous.mono (Icc_subset_Icc (le_of_lt hv₁.1) (le_of_lt hv₂.2))
  have hint_pos : 0 < ∫ t in v₁..v₂, S.f t :=
    intervalIntegral.integral_pos hlt hcont
      (fun x hx => le_of_lt (S.f_pos x
        ⟨lt_of_lt_of_le hv₁.1 (le_of_lt hx.1), lt_of_le_of_lt hx.2 hv₂.2⟩))
      ⟨(v₁ + v₂) / 2, ⟨by linarith, by linarith⟩,
        S.f_pos _ ⟨by linarith [hv₁.1], by linarith [hv₂.2]⟩⟩
  have hv₂_nn : (0 : ℝ) ≤ v₂ := le_of_lt hv₂.1
  have hcont_full : ContinuousOn S.f (Set.uIcc 0 v₂) := by
    rw [Set.uIcc_of_le hv₂_nn]
    exact S.f_continuous.mono (Icc_subset_Icc le_rfl (le_of_lt hv₂.2))
  have hint1 : IntervalIntegrable S.f volume 0 v₁ := by
    apply (hcont_full.mono _).intervalIntegrable
    apply Set.uIcc_subset_uIcc_left
    rw [Set.uIcc_of_le hv₂_nn]
    exact ⟨by linarith [hv₁.1], by linarith⟩
  have hint2 : IntervalIntegrable S.f volume v₁ v₂ :=
    (show ContinuousOn S.f (Set.uIcc v₁ v₂) by
      rw [Set.uIcc_of_le (le_of_lt hlt)]
      exact hcont).intervalIntegrable
  linarith [intervalIntegral.integral_add_adjacent_intervals hint1 hint2]

/-- F(v₁)^(n-1) < F(v₂)^(n-1) for v₁ < v₂ in (0, v̄). -/
lemma F_pow_strict_mono
    (v₁ v₂ : ℝ) (hv₁ : v₁ ∈ Ioo 0 S.v_bar) (hv₂ : v₂ ∈ Ioo 0 S.v_bar)
    (hlt : v₁ < v₂) : S.F v₁ ^ (S.n - 1) < S.F v₂ ^ (S.n - 1) :=
  pow_lt_pow_left₀ (S.F_strictMono_interior v₁ v₂ hv₁ hv₂ hlt)
    (S.F_range v₁ (Ioo_subset_Icc_self hv₁)).1
    (by have := S.hn; omega)

/-- The G gap: for β(v₁) = β(v₂) = b₀ and ε > 0,
    G(b₀ + ε) - G(b₀) ≥ F(v₂)^(n-1) - F(v₁)^(n-1). -/
lemma G_gap
    (v₁ v₂ : ℝ) (hv₁ : v₁ ∈ Ioo 0 S.v_bar) (hv₂ : v₂ ∈ Ioo 0 S.v_bar)
    (_hlt : v₁ < v₂) (b₀ : ℝ) (hβ₁ : S.β v₁ = b₀) (hβ₂ : S.β v₂ = b₀)
    (ε : ℝ) (hε : 0 < ε) :
    S.F v₂ ^ (S.n - 1) - S.F v₁ ^ (S.n - 1) ≤ S.G (b₀ + ε) - S.G b₀ := by
  obtain ⟨v₀, hv₀_mem, hv₀_below, _, hG_b₀⟩ := S.G_eq b₀
  obtain ⟨v₀_ε, hv₀_ε_mem, _, hv₀_ε_above, hG_bε⟩ := S.G_eq (b₀ + ε)
  have hv₀_le_v₁ : v₀ ≤ v₁ :=
    le_of_not_gt fun h => by linarith [hv₀_below v₁ (Ioo_subset_Icc_self hv₁) h, hβ₁.symm.le]
  have hv₂_le_v₀_ε : v₂ ≤ v₀_ε :=
    hv₀_ε_above v₂ (Ioo_subset_Icc_self hv₂) (by rw [hβ₂]; linarith)
  rw [hG_bε, hG_b₀]
  linarith [pow_le_pow_left₀ (S.F_range v₀ hv₀_mem).1 (S.F_mono hv₀_le_v₁) (S.n - 1),
            pow_le_pow_left₀ (S.F_range v₂ (Ioo_subset_Icc_self hv₂)).1
              (S.F_mono hv₂_le_v₀_ε) (S.n - 1)]

/-- IC contradiction: a positive G-gap and continuity of C are incompatible. -/
lemma ic_contradiction
    (v₂ b₀ Δ : ℝ)
    (hv₂_mem : v₂ ∈ Icc 0 S.v_bar)
    (hv₂_pos : 0 < v₂)
    (hβ₂ : S.β v₂ = b₀)
    (hΔ : 0 < Δ)
    (hgap : ∀ ε > 0, Δ ≤ S.G (b₀ + ε) - S.G b₀)
    (hb₀_nonneg : 0 ≤ b₀) : False := by
  obtain ⟨η, hη_pos, hη⟩ :=
    (Metric.tendsto_nhds_nhds.mp (S.C_continuous.tendsto b₀)) (v₂ * Δ) (mul_pos hv₂_pos hΔ)
  have hε : 0 < η / 2 := by linarith
  have hic := S.ic v₂ hv₂_mem (b₀ + η / 2) (by linarith)
  rw [hβ₂] at hic
  have h_small := hη (show dist (b₀ + η / 2) b₀ < η by
    rw [Real.dist_eq, show b₀ + η / 2 - b₀ = η / 2 by ring, abs_of_pos hε]
    linarith)
  rw [Real.dist_eq] at h_small
  linarith [abs_lt.mp h_small, hgap (η / 2) hε,
            mul_le_mul_of_nonneg_left (hgap (η / 2) hε) (le_of_lt hv₂_pos)]

theorem strictMonotonicity : StrictMonoOn S.β (Icc 0 S.v_bar) := by
  by_contra h
  obtain ⟨v₁, hv₁, v₂, hv₂, hlt, heq⟩ := S.exists_interior_flat_pair h
  set b₀ := S.β v₁
  exact S.ic_contradiction v₂ b₀ (S.F v₂ ^ (S.n - 1) - S.F v₁ ^ (S.n - 1))
    (Ioo_subset_Icc_self hv₂) hv₂.1 heq.symm
    (by linarith [S.F_pow_strict_mono v₁ v₂ hv₁ hv₂ hlt])
    (fun ε hε => S.G_gap v₁ v₂ hv₁ hv₂ hlt b₀ rfl heq.symm ε hε)
    (S.β_nonneg v₁ (Ioo_subset_Icc_self hv₁))

theorem no_ties : ∀ v₁ ∈ Ioo 0 S.v_bar, ∀ v₂ ∈ Ioo 0 S.v_bar,
    v₁ ≠ v₂ → S.β v₁ ≠ S.β v₂ := by
  intro v₁ hv₁ v₂ hv₂ hne
  exact (S.strictMonotonicity.injOn (Ioo_subset_Icc_self hv₁)
    (Ioo_subset_Icc_self hv₂)).mt hne

end StrictMonoSetup
