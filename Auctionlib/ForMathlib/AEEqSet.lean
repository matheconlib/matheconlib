import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.Order.CompleteBooleanAlgebra

/-! # Measurable sets up to almost everywhere equality
In this file we defined the type of measurable sets up to almost-everywhere equality
of a measure space, also known as its measure algebra.
-/

open Set

namespace MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- The equivalence relation given by almost-everywhere equality on measurable sets. -/
def Measure.aeEqSetoidSet : Setoid {s : Set Ω // MeasurableSet s} :=
  ⟨fun s t ↦ s.1 =ᵐ[μ] t.1, fun _ ↦ ae_eq_refl _, ae_eq_symm, fun h h' ↦ ae_eq_trans h h'⟩

/-- The type of measurable sets up to almost-everywhere equality. -/
def AEEqSet := Quotient μ.aeEqSetoidSet

namespace AEEqSet

/-- The equivalence class of a measurable set under almost-everywhere equality. -/
def mk (s : Set Ω) (hs : MeasurableSet s) : AEEqSet μ := Quotient.mk'' ⟨s, hs⟩

variable {μ}

instance : LE (AEEqSet μ) where
  le s t := Quotient.liftOn₂' s t (fun s t ↦ s.1 ≤ᵐ[μ] t.1) (fun _ _ _ _ hs ht ↦
    (Filter.eventuallyLE_congr hs ht).eq)

instance : PartialOrder (AEEqSet μ) where
  le_refl s := s.inductionOn fun _ ↦ Filter.EventuallyLE.refl _ _
  le_trans s s' s'' := s.inductionOn <| s'.inductionOn <| s''.inductionOn fun s s' s'' h h' ↦
    Filter.EventuallyLE.trans h h'
  le_antisymm s t := s.inductionOn <| t.inductionOn fun _ _ h h' ↦
    Quotient.sound' (Filter.EventuallyLE.antisymm h h')

/-- The Boolean algebra structure on measurable sets up to almost-everywhere equality, with all
operations lifted from the corresponding set operations. In particular `⊔`, `⊓`, `ᶜ`, `\`, `⊥`
and `⊤` are (definitionally) the classes of `∪`, `∩`, `ᶜ`, `\`, `∅` and `univ`. -/
instance : BooleanAlgebra (AEEqSet μ) where
  __ := inferInstanceAs (PartialOrder (AEEqSet μ))
  sup := Quotient.map₂' (fun s t ↦ ⟨s.1 ∪ t.1, s.2.union t.2⟩) fun _ _ hs _ _ ht ↦ hs.union ht
  inf := Quotient.map₂' (fun s t ↦ ⟨s.1 ∩ t.1, s.2.inter t.2⟩) fun _ _ hs _ _ ht ↦ hs.inter ht
  compl := Quotient.map' (fun s ↦ ⟨s.1ᶜ, s.2.compl⟩) fun _ _ hs ↦ hs.compl
  sdiff := Quotient.map₂' (fun s t ↦ ⟨s.1 \ t.1, s.2.diff t.2⟩) fun _ _ hs _ _ ht ↦ hs.diff ht
  bot := mk μ ∅ MeasurableSet.empty
  top := mk μ univ MeasurableSet.univ
  himp_eq _ _ := rfl
  le_sup_left s t := s.inductionOn <| t.inductionOn fun _ _ ↦ subset_union_left.eventuallyLE
  le_sup_right s t := s.inductionOn <| t.inductionOn fun _ _ ↦ subset_union_right.eventuallyLE
  sup_le s t u := s.inductionOn fun s ↦ t.inductionOn fun t ↦ u.inductionOn fun u h h' ↦ by
    show (s.1 ∪ t.1 : Set Ω) ≤ᵐ[μ] u.1
    filter_upwards [show s.1 ≤ᵐ[μ] u.1 from h, show t.1 ≤ᵐ[μ] u.1 from h'] with x hx hx'
    exact fun hmem ↦ hmem.elim hx hx'
  inf_le_left s t := s.inductionOn <| t.inductionOn fun _ _ ↦ inter_subset_left.eventuallyLE
  inf_le_right s t := s.inductionOn <| t.inductionOn fun _ _ ↦ inter_subset_right.eventuallyLE
  le_inf s t u := s.inductionOn fun s ↦ t.inductionOn fun t ↦ u.inductionOn fun u h h' ↦ by
    show s.1 ≤ᵐ[μ] (t.1 ∩ u.1 : Set Ω)
    filter_upwards [show s.1 ≤ᵐ[μ] t.1 from h, show s.1 ≤ᵐ[μ] u.1 from h'] with x hx hx'
    exact fun hs ↦ ⟨hx hs, hx' hs⟩
  le_sup_inf s t u := s.inductionOn fun s ↦ t.inductionOn fun t ↦ u.inductionOn fun u ↦ by
    show ((s.1 ∪ t.1) ∩ (s.1 ∪ u.1) : Set Ω) ≤ᵐ[μ] (s.1 ∪ t.1 ∩ u.1 : Set Ω)
    refine Filter.Eventually.of_forall fun x hx ↦ ?_
    obtain ⟨hst, hsu⟩ := hx
    rcases hst with hs | ht
    · exact Or.inl hs
    · rcases hsu with hs | hu
      · exact Or.inl hs
      · exact Or.inr ⟨ht, hu⟩
  inf_compl_le_bot s := s.inductionOn fun s ↦ by
    show (s.1 ∩ s.1ᶜ : Set Ω) ≤ᵐ[μ] (∅ : Set Ω)
    exact Filter.Eventually.of_forall fun _ hx ↦ absurd hx.1 hx.2
  top_le_sup_compl s := s.inductionOn fun s ↦ by
    show (univ : Set Ω) ≤ᵐ[μ] (s.1 ∪ s.1ᶜ : Set Ω)
    exact Filter.Eventually.of_forall fun x _ ↦ Classical.em (x ∈ s.1)
  le_top s := s.inductionOn fun s ↦ (subset_univ s.1).eventuallyLE
  bot_le s := s.inductionOn fun s ↦ (empty_subset s.1).eventuallyLE
  sdiff_eq s t := s.inductionOn <| t.inductionOn fun _ _ ↦ rfl

variable {s t : Set Ω}

@[simp]
lemma mk_le_mk (hs : MeasurableSet s) (ht : MeasurableSet t) :
    mk μ s hs ≤ mk μ t ht ↔ s ≤ᵐ[μ] t := Iff.rfl

@[simp]
lemma mk_sup_mk (hs : MeasurableSet s) (ht : MeasurableSet t) :
    mk μ s hs ⊔ mk μ t ht = mk μ (s ∪ t) (hs.union ht) := rfl

@[simp]
lemma mk_inf_mk (hs : MeasurableSet s) (ht : MeasurableSet t) :
    mk μ s hs ⊓ mk μ t ht = mk μ (s ∩ t) (hs.inter ht) := rfl

@[simp]
lemma compl_mk (hs : MeasurableSet s) : (mk μ s hs)ᶜ = mk μ sᶜ hs.compl := rfl

@[simp]
lemma mk_sdiff_mk (hs : MeasurableSet s) (ht : MeasurableSet t) :
    mk μ s hs \ mk μ t ht = mk μ (s \ t) (hs.diff ht) := rfl

@[simp]
lemma bot_eq : (⊥ : AEEqSet μ) = mk μ ∅ MeasurableSet.empty := rfl

@[simp]
lemma top_eq : (⊤ : AEEqSet μ) = mk μ univ MeasurableSet.univ := rfl

open Filter Topology ENNReal in
/-- The measure algebra of any finite measure is complete. -/
noncomputable instance [IsFiniteMeasure μ] : CompleteBooleanAlgebra (AEEqSet μ) where
  __ := inferInstanceAs (BooleanAlgebra (AEEqSet μ))
  __ : CompleteLattice _ := by
    refine completeLatticeOfSup (H2 := ⟨_⟩) (AEEqSet μ) fun S ↦ (?_ : ∃ u, IsLUB S u).choose_spec
    classical
    -- A measurable representative of each class.
    set rep : AEEqSet μ → Set Ω := fun α ↦ (Quotient.out α).1 with hrepdef
    have hrep_meas : ∀ α, MeasurableSet (rep α) := fun α ↦ (Quotient.out α).2
    have hrep : ∀ α, mk μ (rep α) (hrep_meas α) = α := fun α ↦ Quotient.out_eq' α
    -- `x ≤ y` in terms of representatives.
    have hle_null : ∀ {x y : AEEqSet μ}, x ≤ y → μ (rep x \ rep y) = 0 := by
      intro x y hxy
      rw [← hrep x, ← hrep y, mk_le_mk, ae_le_set] at hxy
      exact hxy
    -- Finite-union measure of a finite subfamily of `S`.
    set J : Type _ := {T : Finset (AEEqSet μ) // (↑T : Set _) ⊆ S} with hJdef
    set val : J → ℝ≥0∞ := fun T ↦ μ (⋃ x ∈ (T.1 : Finset _), rep x) with hvaldef
    set c : ℝ≥0∞ := ⨆ T : J, val T with hcdef
    have hval_le : ∀ T : J, val T ≤ μ univ := fun T ↦ measure_mono (subset_univ _)
    have hc_ne_top : c ≠ ⊤ := ne_top_of_le_ne_top (measure_ne_top μ univ) (iSup_le hval_le)
    have hJne : Nonempty J := ⟨⟨∅, by simp⟩⟩
    -- Finite subfamilies whose value approaches `c`.
    have hachieve : ∀ n : ℕ, ∃ T : J, c ≤ val T + (1 : ℝ≥0∞) / (n + 1) := by
      intro n
      by_cases hc0 : c = 0
      · exact ⟨Classical.choice hJne, by simp [hc0]⟩
      · have hpos : (0 : ℝ≥0∞) < 1 / (n + 1) :=
          ENNReal.div_pos_iff.mpr ⟨by norm_num, by simp⟩
        have hlt : c - 1 / (n + 1) < c := ENNReal.sub_lt_self hc_ne_top hc0 hpos.ne'
        rw [hcdef, lt_iSup_iff] at hlt
        obtain ⟨T, hT⟩ := hlt
        exact ⟨T, by rw [← tsub_le_iff_right]; exact hT.le⟩
    choose T0 hT0 using hachieve
    -- Increasing partial unions.
    set Bset : ℕ → Finset (AEEqSet μ) :=
      fun n ↦ (Finset.range (n + 1)).biUnion fun k ↦ (T0 k).1 with hBsetdef
    have hBset_sub : ∀ n, (↑(Bset n) : Set _) ⊆ S := by
      intro n x hx
      simp only [hBsetdef, Finset.coe_biUnion, mem_iUnion] at hx
      obtain ⟨k, _, hk⟩ := hx
      exact (T0 k).2 hk
    set B : ℕ → Set Ω := fun n ↦ ⋃ x ∈ Bset n, rep x with hBdef
    have hB_meas : ∀ n, MeasurableSet (B n) :=
      fun n ↦ Finset.measurableSet_biUnion _ fun x _ ↦ hrep_meas x
    have hBset_mono : Monotone Bset := by
      intro a b hab x hx
      simp only [hBsetdef, Finset.mem_biUnion, Finset.mem_range] at hx ⊢
      obtain ⟨k, hk, hkx⟩ := hx
      exact ⟨k, lt_of_lt_of_le hk (by omega), hkx⟩
    have hB_mono : Monotone B :=
      fun a b hab ↦ Set.biUnion_subset_biUnion_left (by exact_mod_cast hBset_mono hab)
    have hB_val_le : ∀ n, μ (B n) ≤ c := by
      intro n
      have : μ (B n) = val ⟨Bset n, hBset_sub n⟩ := rfl
      rw [this]; exact le_iSup val ⟨Bset n, hBset_sub n⟩
    have hT0_sub_B : ∀ n, (T0 n).1 ⊆ Bset n := by
      intro n x hx
      simp only [hBsetdef, Finset.mem_biUnion, Finset.mem_range]
      exact ⟨n, by omega, hx⟩
    have hB_ge : ∀ n, val (T0 n) ≤ μ (B n) := by
      intro n
      apply measure_mono
      apply Set.biUnion_subset_biUnion_left
      exact_mod_cast hT0_sub_B n
    have hB_close : ∀ n, c ≤ μ (B n) + 1 / (n + 1) := fun n ↦
      (hT0 n).trans (by gcongr; exact hB_ge n)
    -- The essential union.
    set U : Set Ω := ⋃ n, B n with hUdef
    have hU_meas : MeasurableSet U := MeasurableSet.iUnion hB_meas
    have htend : Tendsto (fun n ↦ μ (B n)) atTop (𝓝 (μ U)) := by
      simpa [hUdef] using tendsto_measure_iUnion_atTop (μ := μ) hB_mono
    have hμU_le : μ U ≤ c := le_of_tendsto htend (Eventually.of_forall hB_val_le)
    have hμU_ge : c ≤ μ U := by
      have h0 : Tendsto (fun n : ℕ ↦ (1 : ℝ≥0∞) / (n + 1)) atTop (𝓝 0) := by
        have h := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
        simp only [Function.comp_def, Nat.cast_add, Nat.cast_one] at h
        simpa [one_div] using h
      have htend2 : Tendsto (fun n ↦ μ (B n) + 1 / (n + 1)) atTop (𝓝 (μ U)) := by
        have := htend.add h0; rwa [add_zero] at this
      exact ge_of_tendsto htend2 (Eventually.of_forall hB_close)
    have hμU : μ U = c := le_antisymm hμU_le hμU_ge
    refine ⟨mk μ U hU_meas, ?_, ?_⟩
    · -- `mk U` is an upper bound of `S`.
      intro α hα
      rw [← hrep α, mk_le_mk, ae_le_set]
      by_contra hne
      have hpos : 0 < μ (rep α \ U) := pos_iff_ne_zero.mpr hne
      -- Adjoining `α` to each `Bset n` gives finite subfamilies of `S`.
      set Cset : ℕ → Finset (AEEqSet μ) := fun n ↦ insert α (Bset n) with hCsetdef
      have hCset_sub : ∀ n, (↑(Cset n) : Set _) ⊆ S := by
        intro n y hy
        simp only [hCsetdef, Finset.coe_insert, mem_insert_iff] at hy
        rcases hy with rfl | hy
        · exact hα
        · exact hBset_sub n hy
      set C : ℕ → Set Ω := fun n ↦ B n ∪ rep α with hCdef
      have hC_eq : ∀ n, (⋃ y ∈ Cset n, rep y) = C n := by
        intro n
        simp only [hCsetdef, hCdef, Finset.set_biUnion_insert, hBdef]
        rw [Set.union_comm]
      have hC_val_le : ∀ n, μ (C n) ≤ c := by
        intro n
        have : μ (C n) = val ⟨Cset n, hCset_sub n⟩ := by simp only [hvaldef]; rw [← hC_eq n]
        rw [this]; exact le_iSup val ⟨Cset n, hCset_sub n⟩
      have hC_mono : Monotone C := fun a b hab ↦ Set.union_subset_union_left _ (hB_mono hab)
      have hCtend : Tendsto (fun n ↦ μ (C n)) atTop (𝓝 (μ (⋃ n, C n))) := by
        simpa using tendsto_measure_iUnion_atTop (μ := μ) hC_mono
      have hCU : (⋃ n, C n) = U ∪ rep α := by simp only [hCdef, hUdef]; rw [Set.iUnion_union]
      have hμCU : μ (⋃ n, C n) ≤ c := le_of_tendsto hCtend (Eventually.of_forall hC_val_le)
      rw [hCU] at hμCU
      have hunion : μ U + μ (rep α \ U) = μ (U ∪ rep α) :=
        measure_add_diff hU_meas.nullMeasurableSet _
      rw [← hunion, hμU] at hμCU
      have hcontra : μ (rep α \ U) ≤ 0 :=
        ENNReal.le_of_add_le_add_left hc_ne_top (by rw [add_zero]; exact hμCU)
      exact hne (le_antisymm hcontra (zero_le _))
    · -- `mk U` is below every upper bound of `S`.
      intro v hv
      rw [← hrep v, mk_le_mk, ae_le_set]
      have hB_null : ∀ n, μ (B n \ rep v) = 0 := by
        intro n
        have hEq : B n \ rep v = ⋃ x ∈ Bset n, (rep x \ rep v) := by
          simp only [hBdef, Set.iUnion_diff]
        rw [hEq]
        refine (measure_biUnion_null_iff (Bset n).countable_toSet).mpr fun x hx ↦ ?_
        exact hle_null (hv (hBset_sub n hx))
      have hUV : U \ rep v = ⋃ n, (B n \ rep v) := by simp only [hUdef, Set.iUnion_diff]
      rw [hUV]
      exact measure_iUnion_null hB_null

end AEEqSet

end MeasureTheory
