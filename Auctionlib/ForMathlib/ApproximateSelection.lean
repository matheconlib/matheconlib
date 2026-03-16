module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.Semicontinuity.Hemicontinuity

import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.EMetricSpace.Paracompact

/-!
# Approximate selections of upper hemi-continuous functions
This file contains an auto-formalisation of existence theorems for continuous approximate selections
of set-valued functions.

Most declarations are kept private; the only public declarations in this file are the following:
* `IsApproxSelection`: definition of approximate selections
* `isApproxSelection_metric_iff`, `IsApproxSelection.mono`: API lemmas for `IsApproxSelection`
* `upperHemicontinuous_iff_isOpen_of_isOpen` and `UpperHemicontinuous.isOpen_of_isOpen`: two missing
  API lemmas on hemicontinuous functions
* `exists_star_refinement`: proof that every open cover of a paracompact Hausdorff space admits a
  locally finite star-refinement consisting only of nonempty sets
* `UpperHemicontinuous.exists_isApproxSelection`, `UpperHemicontinuous.exists_isApproxSelection'`,
  `UpperHemicontinuous.exists_isApproxSelection_metric`: existence of continuous approximate
  selections for upper hemicontinuous functions from paracompact Hausdorff uniform spaces to
  topological vector spaces that are valued in nonempty convex sets, and some convenient
  special cases.
-/

universe u v

open Uniformity Pointwise Topology Set

/-! ### Definitions -/

@[expose]
public def IsApproxSelection {X Y : Type*} [UniformSpace X] [TopologicalSpace Y] [AddCommMonoid Y]
    (F : X → Set Y) (U : Set (X × X)) (W : Set Y) (f : X → Y) : Prop :=
  Continuous f ∧ ∀ x : X, ∃ x' : X, (x, x') ∈ U ∧ f x ∈ F x' + W

/-! ### API lemmas -/

public theorem isApproxSelection_metric_iff {X Y : Type*} [PseudoMetricSpace X]
    [SeminormedAddCommGroup Y] (F : X → Set Y) (ε : ℝ) (f : X → Y) :
    IsApproxSelection F {p : X × X | dist p.1 p.2 < ε} (Metric.ball 0 ε) f ↔
      Continuous f ∧ ∀ x : X, ∃ x', dist x x' < ε ∧ f x ∈ F x' + Metric.ball 0 ε :=
  Iff.rfl

public theorem IsApproxSelection.mono {X Y : Type*} [UniformSpace X] [TopologicalSpace Y]
    [AddCommMonoid Y] {F F' : X → Set Y} {U U' : Set (X × X)} {W W' : Set Y} {f : X → Y}
    (hf : IsApproxSelection F U W f) (hF' : ∀ x, F x ⊆ F' x) (hU' : U ⊆ U') (hW' : W ⊆ W') :
    IsApproxSelection F' U' W' f := by
  refine ⟨hf.1, fun x ↦ (hf.2 x).imp fun x' h ↦ ?_⟩
  grind [add_subset_add (hF' x') hW']


/-! ### Helper lemmas -/

public theorem upperHemicontinuous_iff_isOpen_of_isOpen {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {F : X → Set Y} :
    UpperHemicontinuous F ↔ ∀ V : Set Y, IsOpen V → IsOpen {x | F x ⊆ V} := by
  rw [upperHemicontinuous_iff_forall_isOpen]
  exact ⟨fun h v hv ↦ isOpen_iff_mem_nhds.2 fun x hx ↦ h x v hv hx,
    fun h x v hv hx ↦ isOpen_iff_mem_nhds.1 (h v hv) x hx⟩

public theorem UpperHemicontinuous.isOpen_of_isOpen {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {F : X → Set Y} (hF : UpperHemicontinuous F) :
    ∀ V : Set Y, IsOpen V → IsOpen {x | F x ⊆ V} :=
  upperHemicontinuous_iff_isOpen_of_isOpen.1 hF

/-- There exists an open symmetric entourage V with V ○ V ⊆ U. -/
lemma exists_open_symm_entourage_comp {X : Type*} [UniformSpace X]
    (U : Set (X × X)) (hU : U ∈ 𝓤 X) :
    ∃ V ∈ 𝓤 X, IsOpen V ∧
      (∀ x y : X, (x, y) ∈ V → (y, x) ∈ V) ∧
      (∀ x y z : X, (x, y) ∈ V → (y, z) ∈ V → (x, z) ∈ U) := by
  obtain ⟨V, hV, hOpen, hSymm, hComp⟩ := comp_open_symm_mem_uniformity_sets hU
  exact ⟨V, hV, hOpen, fun x y hxy ↦ (SetRel.comm V).mp hxy,
    fun x y z hxy hyz ↦ hComp (SetRel.prodMk_mem_comp hxy hyz)⟩

/-- The cover set is open. -/
lemma coverSet_isOpen
    {X : Type*} [UniformSpace X]
    {Y : Type*} [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
    (F : X → Set Y) (hF_uhc : UpperHemicontinuous F) (W : Set Y) (hW : IsOpen W)
    (V : Set (X × X)) (hV : IsOpen V) (x₀ : X) :
    IsOpen ({z : X | F z ⊆ F x₀ + W} ∩ {z : X | (x₀, z) ∈ V}) :=
  (hF_uhc.isOpen_of_isOpen _ (IsOpen.add_left hW)).inter (UniformSpace.isOpen_ball x₀ hV)

/-- Each x₀ is in its own cover set. -/
lemma mem_own_coverSet
    {X : Type*} [UniformSpace X] {Y : Type*} [AddCommGroup Y]
    (F : X → Set Y) (W : Set Y) (hW : (0 : Y) ∈ W)
    (V : Set (X × X)) (hV : V ∈ 𝓤 X) (x₀ : X) :
    x₀ ∈ {z : X | F z ⊆ F x₀ + W} ∩ {z : X | (x₀, z) ∈ V} := by
  refine ⟨fun y hy ↦ ?_, refl_mem_uniformity hV⟩
  rw [show y = y + 0 from (add_zero y).symm]
  exact Set.add_mem_add hy hW

/-- Cover sets cover all of X. -/
lemma coverSets_cover
    {X : Type*} [UniformSpace X] {Y : Type*} [AddCommGroup Y]
    (F : X → Set Y) (W : Set Y) (hW : (0 : Y) ∈ W)
    (V : Set (X × X)) (hV : V ∈ 𝓤 X) :
    (⋃ x₀ : X, {z : X | F z ⊆ F x₀ + W} ∩ {z : X | (x₀, z) ∈ V}) = univ :=
  eq_univ_of_forall fun x ↦ mem_iUnion.mpr ⟨x, mem_own_coverSet F W hW V hV x⟩

/-- If φ is subordinate and φ(k)(x) ≠ 0, then x ∈ S(k). -/
lemma active_mem_of_subordinate
    {X κ : Type*} [TopologicalSpace X]
    (S : κ → Set X) (φ : PartitionOfUnity κ X univ)
    (hφ : φ.IsSubordinate S)
    (k : κ) (x : X) (hk : (φ k) x ≠ 0) : x ∈ S k :=
  hφ k (subset_tsupport _ (Function.mem_support.mpr hk))

/-- If ∑ᶠ i, f i ≠ 0, there exists i with f i ≠ 0. -/
lemma exists_ne_zero_of_finsum
    {κ : Type*} {f : κ → ℝ} (h : ∑ᶠ k, f k ≠ 0) : ∃ k, f k ≠ 0 := by
  by_contra! h'
  exact h (by simp [funext h'])

/-! ### Metric specialization helpers -/

/-- If y ∈ s + Metric.ball 0 ε and s is nonempty, then Metric.infDist y s < ε. -/
lemma infDist_lt_of_mem_add_ball
    {Y : Type*} [SeminormedAddCommGroup Y]
    (s : Set Y) (hs : s.Nonempty) (y : Y) (ε : ℝ)
    (hy : y ∈ s + Metric.ball (0 : Y) ε) :
    Metric.infDist y s < ε := by
  rw [Metric.infDist_lt_iff hs]
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hy
  exact ⟨a, ha, by
    rw [dist_eq_norm, add_sub_cancel_left]
    exact mem_ball_zero_iff.mp hb⟩

/-! ### Star refinement -/

lemma star_refinement_shrinking
    {X : Type*} [TopologicalSpace X] [ParacompactSpace X] [NormalSpace X]
    {ι : Type*} (C : ι → Set X) (hC_open : ∀ i, IsOpen (C i)) (hC_cover : ⋃ i, C i = univ) :
    ∃ (R W : ι → Set X),
      (∀ i, IsOpen (R i)) ∧ (⋃ i, R i = univ) ∧ LocallyFinite R ∧ (∀ i, R i ⊆ C i) ∧
      (∀ i, IsOpen (W i)) ∧ (⋃ i, W i = univ) ∧ (∀ i, closure (W i) ⊆ R i) := by
  obtain ⟨R, hR_open, hR_cover, hR_lf, hR_sub⟩ := precise_refinement C hC_open hC_cover
  obtain ⟨W, hW_cover, hW_open, hW_closure⟩ :=
    exists_iUnion_eq_closure_subset hR_open hR_lf.point_finite hR_cover
  exact ⟨R, W, hR_open, hR_cover, hR_lf, hR_sub, hW_open, hW_cover, hW_closure⟩

lemma locallyFinite_isClosed_biUnion
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} (f : ι → Set X) (p : ι → Prop)
    (hf_lf : LocallyFinite f) (hf_closed : ∀ i, IsClosed (f i)) :
    IsClosed (⋃ i ∈ {i | p i}, f i) := by
  classical
  rw [show ⋃ i ∈ {i : ι | p i}, f i = ⋃ i : ι, if p i then f i else ∅ from by
    ext x
    simp_all]
  exact (hf_lf.subset fun i ↦ by split_ifs <;> simp).isClosed_iUnion fun i ↦ by
    split_ifs with h
    · exact hf_closed i
    · exact isClosed_empty

/-- Assembly of star refinement from shrinking and star neighborhoods. -/
lemma star_refinement_assembly
    {X : Type u} [TopologicalSpace X] [ParacompactSpace X] [NormalSpace X]
    {ι : Type v} (C R W : ι → Set X)
    (hR_open : ∀ i, IsOpen (R i))
    (hR_lf : LocallyFinite R) (hRC : ∀ i, R i ⊆ C i)
    (hW_open : ∀ i, IsOpen (W i)) (hW_cover : ⋃ i, W i = univ)
    (hW_lf : LocallyFinite W) (hWR : ∀ i, closure (W i) ⊆ R i) :
    ∃ (κ : Type max u v) (S : κ → Set X) (π : κ → ι),
      (∀ k, IsOpen (S k)) ∧ (⋃ k, S k = univ) ∧ LocallyFinite S ∧
      (∀ k, S k ⊆ C (π k)) ∧
      (∀ k₁ k₂, (S k₁ ∩ S k₂).Nonempty → S k₁ ⊆ C (π k₂)) := by
  let D : X → Set X := fun x ↦ (⋂ i ∈ {i | x ∈ R i}, R i) \ (⋃ i ∈ {i | x ∉ R i}, closure (W i))
  let E : X × ι → Set X := fun p ↦ D p.1 ∩ W p.2
  have hE_open : ∀ p : X × ι, IsOpen (E p) := fun p ↦
    (((hR_lf.point_finite p.1).isOpen_biInter fun i _ ↦ hR_open i).sdiff
      (locallyFinite_isClosed_biUnion _ _ hW_lf.closure fun _ ↦ isClosed_closure)).inter
      (hW_open p.2)
  have hE_cover : ⋃ p : X × ι, E p = univ :=
    eq_univ_of_forall fun z ↦ by
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hW_cover ▸ mem_univ z : z ∈ ⋃ i, W i)
      exact mem_iUnion.mpr ⟨⟨z, i⟩,
        ⟨Set.mem_iInter₂.mpr fun _ hi ↦ hi, fun h ↦
          let ⟨j, hj, hx⟩ := Set.mem_iUnion₂.mp h; hj (hWR j hx)⟩, hi⟩
  obtain ⟨S, hS_open, hS_cover, hS_lf, hS_ref⟩ := precise_refinement _ hE_open hE_cover
  let π : X × ι → ι := fun k ↦ k.2
  refine ⟨X × ι, S, π, hS_open, hS_cover, hS_lf, ?_, ?_⟩
  · intro k
    calc S k ⊆ D k.1 ∩ W (π k) := hS_ref k
      _ ⊆ W (π k) := inter_subset_right
      _ ⊆ closure (W (π k)) := subset_closure
      _ ⊆ R (π k) := hWR (π k)
      _ ⊆ C (π k) := hRC (π k)
  · intro k₁ k₂ ⟨z, hz₁, hz₂⟩
    have hτR : k₁.1 ∈ R (π k₂) :=
      by_contra fun hx ↦ (hS_ref k₁ hz₁).1.2
        (Set.mem_iUnion₂.mpr ⟨π k₂, hx, subset_closure (hS_ref k₂ hz₂).2⟩)
    calc S k₁ ⊆ D k₁.1 ∩ W (π k₁) := hS_ref k₁
      _ ⊆ D k₁.1 := inter_subset_left
      _ ⊆ R (π k₂) := Set.diff_subset.trans (Set.biInter_subset_of_mem hτR)
      _ ⊆ C (π k₂) := hRC (π k₂)

/-- Every open cover of a paracompact Hausdorff space admits a locally finite star-refinement
consisting only of nonempty sets. -/
public lemma exists_star_refinement
    {X : Type u} [TopologicalSpace X] [ParacompactSpace X] [T2Space X]
    {ι : Type v} (C : ι → Set X) (hC_open : ∀ i, IsOpen (C i)) (hC_cover : ⋃ i, C i = univ) :
    ∃ (κ : Type max u v) (S : κ → Set X) (π : κ → ι),
      (∀ k, IsOpen (S k)) ∧ (⋃ k, S k = univ) ∧ LocallyFinite S ∧
      (∀ k, S k ⊆ C (π k)) ∧
      (∀ k₁ k₂, (S k₁ ∩ S k₂).Nonempty → S k₁ ⊆ C (π k₂)) := by
  haveI : NormalSpace X := T4Space.of_paracompactSpace_t2Space.toNormalSpace
  obtain ⟨R, W, hR_open, hR_cover, hR_lf, hRC, hW_open, hW_cover, hWR⟩ :=
    star_refinement_shrinking C hC_open hC_cover
  have hW_lf : LocallyFinite W :=
    (hR_lf.subset fun i ↦ hWR i).subset fun i ↦ subset_closure
  exact star_refinement_assembly C R W hR_open hR_lf hRC
    hW_open hW_cover hW_lf hWR

/-! ### Main theorems -/

/-- Every upper hemicontinuous function `F` from a paracompact Hausdorff uniform space `X` to a
topological vector space `E` that is valued in nonempty convex sets admits arbitrarily good
continuous approximate selections: for every entourage `U : Set (X × X)` and every open
convex neighbourhood `W` of `0` in `E` there exists a function `f : X → E` such that for every
`x : X`, there exists an `x' : X` with `(x,x') ∈ U` and `f x ∈ F x' + W`.

Note that in locally convex vector spaces this holds for arbitrary neighbourhoods `W` of `0`,
not just open and convex ones: see `UpperHemicontinuous.exists_isApproxSelection'`. -/
public theorem UpperHemicontinuous.exists_isApproxSelection
    {X : Type*} [UniformSpace X] [ParacompactSpace X] [T2Space X]
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {F : X → Set E}
    (hF : UpperHemicontinuous F) (hF' : ∀ x, (F x).Nonempty) (hF'' : ∀ x, Convex ℝ (F x))
    {U : Set (X × X)} (hU : U ∈ 𝓤 X) {W : Set E} (hW : IsOpen W) (hW' : 0 ∈ W) (hW'' : Convex ℝ W) :
    ∃ f : X → E, IsApproxSelection F U W f := by
  obtain ⟨V, hV_mem, hV_open, hV_symm, hV_comp⟩ := exists_open_symm_entourage_comp U hU
  let C : X → Set X := fun x₀ ↦ {z | F z ⊆ F x₀ + W} ∩ {z | (x₀, z) ∈ V}
  have hC_open : ∀ x₀, IsOpen (C x₀) :=
    fun x₀ ↦ coverSet_isOpen F hF W hW V hV_open x₀
  have hC_cover : ⋃ x₀, C x₀ = univ := coverSets_cover F W hW' V hV_mem
  haveI : NormalSpace X := T4Space.of_paracompactSpace_t2Space.toNormalSpace
  obtain ⟨κ, S, π, hS_open, hS_cover, hS_lf, hS_sub, hS_star⟩ :=
    exists_star_refinement C hC_open hC_cover
  obtain ⟨φ, hφ⟩ := PartitionOfUnity.exists_isSubordinate (ι := κ) isClosed_univ S hS_open
    (hS_cover ▸ subset_refl _)
  have hS_choice : ∀ k : κ, ∃ p : X, (S k).Nonempty → p ∈ S k := by
    intro k
    by_cases h : (S k).Nonempty
    · exact ⟨h.some, fun _ ↦ h.some_mem⟩
    · exact ⟨π k, fun h' ↦ absurd h' h⟩
  choose p hp using hS_choice
  choose y hy using fun k ↦ hF' (p k)
  refine ⟨fun x ↦ ∑ᶠ k, (φ k x) • y k, ?_, ?_⟩
  · exact hφ.continuous_finsum_smul hS_open (fun _ ↦ continuousOn_const)
  · intro x
    have hone : (∑ᶠ k, (φ k) x) = 1 := φ.sum_eq_one (mem_univ x)
    obtain ⟨k₀, hk₀⟩ := exists_ne_zero_of_finsum (hone ▸ one_ne_zero)
    refine ⟨π k₀, ?_, ?_⟩
    · have hxCπk₀ := hS_sub k₀ (active_mem_of_subordinate S φ hφ k₀ x hk₀)
      exact hV_comp x x (π k₀) (refl_mem_uniformity hV_mem) (hV_symm _ x hxCπk₀.2)
    · apply φ.finsum_smul_mem_convex (mem_univ x) _ ((hF'' (π k₀)).add hW'')
      intro k hk
      have hxSk := active_mem_of_subordinate S φ hφ k x hk
      have hxSk₀ := active_mem_of_subordinate S φ hφ k₀ x hk₀
      exact (hS_star k k₀ ⟨x, hxSk, hxSk₀⟩ (hp k ⟨x, hxSk⟩)).1 (hy k)


/-- Every upper hemicontinuous function `F` from a paracompact Hausdorff uniform space `X` to a
topological vector space `E` that is valued in nonempty convex sets admits arbitrarily good
continuous approximate selections: for every entourage `U : Set (X × X)` and every
neighbourhood `W` of `0` in `E` there exists a function `f : X → E` such that for every
`x : X`, there exists an `x' : X` with `(x,x') ∈ U` and `f x ∈ F x' + W`.

This is a convenient special case of `UpperHemicontinuous.exists_isApproxSelection` for locally
convex vector spaces. -/
public theorem UpperHemicontinuous.exists_isApproxSelection'
    {X : Type*} [UniformSpace X] [ParacompactSpace X] [T2Space X]
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] {F : X → Set E}
    (hF : UpperHemicontinuous F) (hF' : ∀ x, (F x).Nonempty) (hF'' : ∀ x, Convex ℝ (F x))
    {U : Set (X × X)} (hU : U ∈ 𝓤 X) {W : Set E} (hW : W ∈ 𝓝 0) :
    ∃ f : X → E, IsApproxSelection F U W f := by
  obtain ⟨V, hV⟩ := (LocallyConvexSpace.convex_open_basis_zero ℝ E).mem_iff.1 hW
  obtain ⟨f, hf⟩ := hF.exists_isApproxSelection hF' hF'' hU hV.1.2.1 hV.1.1 hV.1.2.2
  exact ⟨f, hf.mono (by simp) (by simp) hV.2⟩

/-- Every upper hemicontinuous function `F` from a metric space `X` to a normed space `E` that is
valued in nonempty convex sets admits arbitrarily good continuous approximate selections:
for every `ε > 0` there exists a function `f : X → E` such that for every `x : X`, there exists an
`x' : X` with `dist x x' < ε` and `Metric.infDist (f x) (F x') < ε`.

This is a special case of `UpperHemicontinuous.exists_isApproxSelection` restated in terms of
distances instead of neighbourhoods. -/
public theorem UpperHemicontinuous.exists_isApproxSelection_metric
    {X : Type*} [MetricSpace X] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : X → Set E} (hF : UpperHemicontinuous F) (hF' : ∀ x, (F x).Nonempty)
    (hF'' : ∀ x, Convex ℝ (F x)) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : X → E, Continuous f ∧
      ∀ x : X, ∃ x' : X, dist x x' < ε ∧ Metric.infDist (f x) (F x') < ε := by
  obtain ⟨f, hf_cont, hf_approx⟩ := hF.exists_isApproxSelection hF' hF''
    (Metric.dist_mem_uniformity hε) Metric.isOpen_ball (Metric.mem_ball_self hε) (convex_ball _ _)
  exact ⟨f, hf_cont, fun x ↦ by
    obtain ⟨x', hx'_dist, hx'_mem⟩ := hf_approx x
    exact ⟨x', hx'_dist, infDist_lt_of_mem_add_ball (F x') (hF' x') (f x) ε hx'_mem⟩⟩
