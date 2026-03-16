import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Semicontinuity.Hemicontinuity

set_option linter.unusedVariables false

open Uniformity Pointwise Topology Set

/-! ### Definitions -/

def IsApproxSelection {X Y : Type} [UniformSpace X] [TopologicalSpace Y] [AddCommMonoid Y]
    (F : X → Set Y) (U : Set (X × X)) (W : Set Y) (f : X → Y) : Prop :=
  Continuous f ∧ ∀ x : X, ∃ x' : X, (x, x') ∈ U ∧ f x ∈ F x' + W

/-! ### Correctness lemmas -/

theorem upperHemicontinuous_iff_isOpen_of_isOpen {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {F : X → Set Y} :
    UpperHemicontinuous F ↔ ∀ V : Set Y, IsOpen V → IsOpen {x | F x ⊆ V} := by
  rw [upperHemicontinuous_iff_forall_isOpen]
  exact ⟨fun h v hv ↦ isOpen_iff_mem_nhds.2 fun x hx ↦ h x v hv hx,
    fun h x v hv hx ↦ isOpen_iff_mem_nhds.1 (h v hv) x hx⟩

theorem UpperHemicontinuous.isOpen_of_isOpen {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {F : X → Set Y} (hF : UpperHemicontinuous F) :
    ∀ V : Set Y, IsOpen V → IsOpen {x | F x ⊆ V} :=
  upperHemicontinuous_iff_isOpen_of_isOpen.1 hF

theorem isApproxSelection_metric_iff {X Y : Type} [PseudoMetricSpace X]
    [SeminormedAddCommGroup Y] (F : X → Set Y) (ε : ℝ) (f : X → Y) :
    IsApproxSelection F {p : X × X | dist p.1 p.2 < ε} (Metric.ball (0 : Y) ε) f ↔
      Continuous f ∧
        ∀ x : X, ∃ x' : X, dist x x' < ε ∧ f x ∈ F x' + Metric.ball (0 : Y) ε :=
  Iff.rfl

/-! ### Helper lemmas -/

/-- There exists an open symmetric entourage V with V ○ V ⊆ U. -/
private lemma exists_open_symm_entourage_comp {X : Type} [UniformSpace X]
    (U : Set (X × X)) (hU : U ∈ 𝓤 X) :
    ∃ V ∈ 𝓤 X, IsOpen V ∧
      (∀ x y : X, (x, y) ∈ V → (y, x) ∈ V) ∧
      (∀ x y z : X, (x, y) ∈ V → (y, z) ∈ V → (x, z) ∈ U) := by
  obtain ⟨V, hV, hOpen, hSymm, hComp⟩ := comp_open_symm_mem_uniformity_sets hU
  exact ⟨V, hV, hOpen, fun x y hxy => (SetRel.comm V).mp hxy,
    fun x y z hxy hyz => hComp (SetRel.prodMk_mem_comp hxy hyz)⟩

/-- The cover set is open. -/
private lemma coverSet_isOpen
    {X : Type} [UniformSpace X]
    {Y : Type} [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
    (F : X → Set Y) (hF_uhc : UpperHemicontinuous F) (W : Set Y) (hW : IsOpen W)
    (V : Set (X × X)) (hV : IsOpen V) (x₀ : X) :
    IsOpen ({z : X | F z ⊆ F x₀ + W} ∩ {z : X | (x₀, z) ∈ V}) :=
  (hF_uhc.isOpen_of_isOpen _ (IsOpen.add_left hW)).inter (UniformSpace.isOpen_ball x₀ hV)

/-- Each x₀ is in its own cover set. -/
private lemma mem_own_coverSet
    {X : Type} [UniformSpace X] {Y : Type} [AddCommGroup Y]
    (F : X → Set Y) (W : Set Y) (hW : (0 : Y) ∈ W)
    (V : Set (X × X)) (hV : V ∈ 𝓤 X) (x₀ : X) :
    x₀ ∈ {z : X | F z ⊆ F x₀ + W} ∩ {z : X | (x₀, z) ∈ V} := by
  refine ⟨fun y hy => ?_, refl_mem_uniformity hV⟩
  rw [show y = y + 0 from (add_zero y).symm]
  exact Set.add_mem_add hy hW

/-- Cover sets cover all of X. -/
private lemma coverSets_cover
    {X : Type} [UniformSpace X] {Y : Type} [AddCommGroup Y]
    (F : X → Set Y) (W : Set Y) (hW : (0 : Y) ∈ W)
    (V : Set (X × X)) (hV : V ∈ 𝓤 X) :
    (⋃ x₀ : X, {z : X | F z ⊆ F x₀ + W} ∩ {z : X | (x₀, z) ∈ V}) = univ :=
  eq_univ_of_forall fun x => mem_iUnion.mpr ⟨x, mem_own_coverSet F W hW V hV x⟩

/-- If φ is subordinate and φ(k)(x) ≠ 0, then x ∈ S(k). -/
private lemma active_mem_of_subordinate
    {X κ : Type} [TopologicalSpace X]
    (S : κ → Set X) (φ : PartitionOfUnity κ X univ)
    (hφ : φ.IsSubordinate S)
    (k : κ) (x : X) (hk : (φ k) x ≠ 0) : x ∈ S k :=
  hφ k (subset_tsupport _ (Function.mem_support.mpr hk))

/-- If ∑ᶠ i, f i ≠ 0, there exists i with f i ≠ 0. -/
private lemma exists_ne_zero_of_finsum
    {κ : Type} {f : κ → ℝ} (h : ∑ᶠ k, f k ≠ 0) : ∃ k, f k ≠ 0 := by
  by_contra! h'
  exact h (by simp [funext h'])

/-! ### Metric specialization helpers -/

/-- If y ∈ s + Metric.ball 0 ε and s is nonempty, then Metric.infDist y s < ε. -/
private lemma infDist_lt_of_mem_add_ball
    {Y : Type} [SeminormedAddCommGroup Y]
    (s : Set Y) (hs : s.Nonempty) (y : Y) (ε : ℝ)
    (hy : y ∈ s + Metric.ball (0 : Y) ε) :
    Metric.infDist y s < ε := by
  rw [Metric.infDist_lt_iff hs]
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hy
  exact ⟨a, ha, by
    rw [dist_eq_norm, add_sub_cancel_left]
    exact mem_ball_zero_iff.mp hb⟩

/-- Properties of Metric.ball 0 ε for ε > 0: open, contains 0, convex, symmetric. -/
private lemma metric_ball_props
    {Y : Type} [SeminormedAddCommGroup Y] [NormedSpace ℝ Y] {ε : ℝ} (hε : 0 < ε) :
    IsOpen (Metric.ball (0 : Y) ε) ∧ (0 : Y) ∈ Metric.ball (0 : Y) ε ∧
    Convex ℝ (Metric.ball (0 : Y) ε) ∧ -Metric.ball (0 : Y) ε = Metric.ball (0 : Y) ε :=
  ⟨Metric.isOpen_ball, Metric.mem_ball_self hε, convex_ball 0 ε, by simp⟩

/-! ### Star refinement -/

lemma star_refinement_shrinking
    {X : Type} [TopologicalSpace X] [ParacompactSpace X] [NormalSpace X]
    {ι : Type} (C : ι → Set X) (hC_open : ∀ i, IsOpen (C i)) (hC_cover : ⋃ i, C i = univ) :
    ∃ (R W : ι → Set X),
      (∀ i, IsOpen (R i)) ∧ (⋃ i, R i = univ) ∧ LocallyFinite R ∧ (∀ i, R i ⊆ C i) ∧
      (∀ i, IsOpen (W i)) ∧ (⋃ i, W i = univ) ∧ (∀ i, closure (W i) ⊆ R i) := by
  obtain ⟨R, hR_open, hR_cover, hR_lf, hR_sub⟩ := precise_refinement C hC_open hC_cover
  obtain ⟨W, hW_cover, hW_open, hW_closure⟩ :=
    exists_iUnion_eq_closure_subset hR_open hR_lf.point_finite hR_cover
  exact ⟨R, W, hR_open, hR_cover, hR_lf, hR_sub, hW_open, hW_cover, hW_closure⟩

lemma locallyFinite_isClosed_biUnion
    {X : Type} [TopologicalSpace X]
    {ι : Type} (f : ι → Set X) (p : ι → Prop)
    (hf_lf : LocallyFinite f) (hf_closed : ∀ i, IsClosed (f i)) :
    IsClosed (⋃ i ∈ {i | p i}, f i) := by
  classical
  rw [show ⋃ i ∈ {i : ι | p i}, f i = ⋃ i : ι, if p i then f i else ∅ from by
    ext x
    simp_all]
  exact (hf_lf.subset fun i => by split_ifs <;> simp).isClosed_iUnion fun i => by
    split_ifs with h
    · exact hf_closed i
    · exact isClosed_empty

/-- Assembly of star refinement from shrinking and star neighborhoods. -/
lemma star_refinement_assembly
    {X : Type} [TopologicalSpace X] [ParacompactSpace X] [NormalSpace X]
    {ι : Type} (C R W : ι → Set X)
    (hR_open : ∀ i, IsOpen (R i)) (hR_cover : ⋃ i, R i = univ)
    (hR_lf : LocallyFinite R) (hRC : ∀ i, R i ⊆ C i)
    (hW_open : ∀ i, IsOpen (W i)) (hW_cover : ⋃ i, W i = univ)
    (hW_lf : LocallyFinite W) (hWR : ∀ i, closure (W i) ⊆ R i) :
    ∃ (κ : Type) (S : κ → Set X) (π : κ → ι),
      (∀ k, IsOpen (S k)) ∧ (⋃ k, S k = univ) ∧ LocallyFinite S ∧
      (∀ k, S k ⊆ C (π k)) ∧
      (∀ k₁ k₂, (S k₁ ∩ S k₂).Nonempty → S k₁ ⊆ C (π k₂)) := by
  let D : X → Set X := fun x => (⋂ i ∈ {i | x ∈ R i}, R i) \ (⋃ i ∈ {i | x ∉ R i}, closure (W i))
  let E : X × ι → Set X := fun p => D p.1 ∩ W p.2
  have hE_open : ∀ p : X × ι, IsOpen (E p) := fun p =>
    (((hR_lf.point_finite p.1).isOpen_biInter fun i _ => hR_open i).sdiff
      (locallyFinite_isClosed_biUnion _ _ hW_lf.closure fun _ => isClosed_closure)).inter
      (hW_open p.2)
  have hE_cover : ⋃ p : X × ι, E p = univ :=
    eq_univ_of_forall fun z => by
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hW_cover ▸ mem_univ z : z ∈ ⋃ i, W i)
      exact mem_iUnion.mpr ⟨⟨z, i⟩,
        ⟨Set.mem_iInter₂.mpr fun _ hi => hi, fun h =>
          let ⟨j, hj, hx⟩ := Set.mem_iUnion₂.mp h; hj (hWR j hx)⟩, hi⟩
  obtain ⟨κ, S, hS_open, hS_cover, hS_lf, hS_ref⟩ :=
    ParacompactSpace.locallyFinite_refinement (X × ι) E hE_open hE_cover
  choose witness hw using hS_ref
  let τ : κ → X := fun k => (witness k).1
  let π : κ → ι := fun k => (witness k).2
  refine ⟨κ, S, π, hS_open, hS_cover, hS_lf, ?_, ?_⟩
  · intro k
    calc S k ⊆ D (τ k) ∩ W (π k) := hw k
      _ ⊆ W (π k) := inter_subset_right
      _ ⊆ closure (W (π k)) := subset_closure
      _ ⊆ R (π k) := hWR (π k)
      _ ⊆ C (π k) := hRC (π k)
  · intro k₁ k₂ ⟨z, hz₁, hz₂⟩
    have hτR : τ k₁ ∈ R (π k₂) :=
      by_contra fun hx => (hw k₁ hz₁).1.2
        (Set.mem_iUnion₂.mpr ⟨π k₂, hx, subset_closure (hw k₂ hz₂).2⟩)
    calc S k₁ ⊆ D (τ k₁) ∩ W (π k₁) := hw k₁
      _ ⊆ D (τ k₁) := inter_subset_left
      _ ⊆ R (π k₂) := Set.diff_subset.trans (Set.biInter_subset_of_mem hτR)
      _ ⊆ C (π k₂) := hRC (π k₂)

/-- Star-refinement of an open cover of a paracompact Hausdorff space. -/
lemma exists_star_refinement
    {X : Type} [TopologicalSpace X] [ParacompactSpace X] [T2Space X]
    {ι : Type} (C : ι → Set X) (hC_open : ∀ i, IsOpen (C i)) (hC_cover : ⋃ i, C i = univ) :
    ∃ (κ : Type) (S : κ → Set X) (π : κ → ι),
      (∀ k, IsOpen (S k)) ∧ (⋃ k, S k = univ) ∧ LocallyFinite S ∧
      (∀ k, S k ⊆ C (π k)) ∧
      (∀ k₁ k₂, (S k₁ ∩ S k₂).Nonempty → S k₁ ⊆ C (π k₂)) := by
  haveI : NormalSpace X := T4Space.of_paracompactSpace_t2Space.toNormalSpace
  obtain ⟨R, W, hR_open, hR_cover, hR_lf, hRC, hW_open, hW_cover, hWR⟩ :=
    star_refinement_shrinking C hC_open hC_cover
  have hW_lf : LocallyFinite W :=
    (hR_lf.subset fun i => hWR i).subset fun i => subset_closure
  exact star_refinement_assembly C R W hR_open hR_cover hR_lf hRC
    hW_open hW_cover hW_lf hWR

/-! ### Main theorems -/

theorem approxSelection_of_uhc
    {X : Type} [UniformSpace X] [ParacompactSpace X] [T2Space X]
    {Y : Type} [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
    [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
    (F : X → Set Y)
    (hF_uhc : UpperHemicontinuous F)
    (hF_nonempty : ∀ x, (F x).Nonempty)
    (hF_convex : ∀ x, Convex ℝ (F x))
    (U : Set (X × X)) (hU : U ∈ 𝓤 X)
    (W : Set Y) (hW_open : IsOpen W) (hW_mem : (0 : Y) ∈ W)
    (hW_convex : Convex ℝ W) (hW_symm : -W = W) :
    ∃ f : X → Y, IsApproxSelection F U W f := by
  obtain ⟨V, hV_mem, hV_open, hV_symm, hV_comp⟩ := exists_open_symm_entourage_comp U hU
  let C : X → Set X := fun x₀ => {z | F z ⊆ F x₀ + W} ∩ {z | (x₀, z) ∈ V}
  have hC_open : ∀ x₀, IsOpen (C x₀) :=
    fun x₀ => coverSet_isOpen F hF_uhc W hW_open V hV_open x₀
  have hC_cover : ⋃ x₀, C x₀ = univ := coverSets_cover F W hW_mem V hV_mem
  haveI : NormalSpace X := T4Space.of_paracompactSpace_t2Space.toNormalSpace
  obtain ⟨κ, S, π, hS_open, hS_cover, hS_lf, hS_sub, hS_star⟩ :=
    exists_star_refinement C hC_open hC_cover
  obtain ⟨φ, hφ⟩ := PartitionOfUnity.exists_isSubordinate (ι := κ) isClosed_univ S hS_open
    (hS_cover ▸ subset_refl _)
  have hS_choice : ∀ k : κ, ∃ p : X, (S k).Nonempty → p ∈ S k := by
    intro k
    by_cases h : (S k).Nonempty
    · exact ⟨h.some, fun _ => h.some_mem⟩
    · exact ⟨π k, fun h' => absurd h' h⟩
  choose p hp using hS_choice
  choose y hy using fun k => hF_nonempty (p k)
  refine ⟨fun x => ∑ᶠ k, (φ k x) • y k, ?_, ?_⟩
  · exact hφ.continuous_finsum_smul hS_open (fun _ => continuousOn_const)
  · intro x
    have hone : (∑ᶠ k, (φ k) x) = 1 := φ.sum_eq_one (mem_univ x)
    obtain ⟨k₀, hk₀⟩ := exists_ne_zero_of_finsum (hone ▸ one_ne_zero)
    refine ⟨π k₀, ?_, ?_⟩
    · have hxCπk₀ := hS_sub k₀ (active_mem_of_subordinate S φ hφ k₀ x hk₀)
      exact hV_comp x x (π k₀) (refl_mem_uniformity hV_mem) (hV_symm _ x hxCπk₀.2)
    · apply φ.finsum_smul_mem_convex (mem_univ x) _ ((hF_convex (π k₀)).add hW_convex)
      intro k hk
      have hxSk := active_mem_of_subordinate S φ hφ k x hk
      have hxSk₀ := active_mem_of_subordinate S φ hφ k₀ x hk₀
      exact (hS_star k k₀ ⟨x, hxSk, hxSk₀⟩ (hp k ⟨x, hxSk⟩)).1 (hy k)

theorem approxSelection_of_uhc_metric
    {X : Type} [MetricSpace X]
    {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Set Y)
    (hF_uhc : UpperHemicontinuous F)
    (hF_nonempty : ∀ x, (F x).Nonempty)
    (hF_convex : ∀ x, Convex ℝ (F x))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : X → Y, Continuous f ∧
      ∀ x : X, ∃ x' : X, dist x x' < ε ∧ Metric.infDist (f x) (F x') < ε := by
  obtain ⟨hBo, hBm, hBc, hBs⟩ := metric_ball_props (Y := Y) hε
  obtain ⟨f, hf_cont, hf_approx⟩ :=
    approxSelection_of_uhc F hF_uhc hF_nonempty hF_convex
      {p : X × X | dist p.1 p.2 < ε} (Metric.dist_mem_uniformity hε)
      (Metric.ball (0 : Y) ε) hBo hBm hBc hBs
  exact ⟨f, hf_cont, fun x => by
    obtain ⟨x', hx'_dist, hx'_mem⟩ := hf_approx x
    exact ⟨x', hx'_dist, infDist_lt_of_mem_add_ball (F x') (hF_nonempty x') (f x) ε hx'_mem⟩⟩
