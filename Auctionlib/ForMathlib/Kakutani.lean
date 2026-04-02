module

public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.Semicontinuity.Defs

import Auctionlib.ForMathlib.ApproximateSelection
import Auctionlib.ForMathlib.Schauder

/-!
# The Kakutani-Glicksberg-Fan fixed point theorem
This file contains a mostly auto-generated proof of the Kakutani-Glicksberg-Fan fixed point theorem,
stating that for every nonempty compact convex subset `k` of a Hausdorff topological vector space
`E`, any upper hemicontinuous function `F : k → Set E` valued in nonempty compact convex subsets
of `k` has a fixed point, i.e. a point `x` for which `↑x ∈ F x`.

Most declarations are kept private; the only public declarations in this file are the following:
* `UpperHemicontinuous.isClosed_graph`: API lemma stating that every upper hemicontinuous function
  whose codomain is Hausdorff and whose values are compact has a closed graph.
* `kakutaniGlicksbergFan`: the Kakutani-Glicksberg-Fan fixed point theorem.
-/

universe u

open Uniformity Pointwise Topology Set Filter

/-! ## Closed graph of an upper hemicontinuous map -/

/-- The graph of any upper hemicontinuous function whose codomain is Hausdorff and whose values are
compact is closed. -/
public lemma UpperHemicontinuous.isClosed_graph {X : Type*} [TopologicalSpace X]
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] {F : X → Set Y}
    (hF : UpperHemicontinuous F) (hF' : ∀ x, IsCompact (F x)) :
    IsClosed {p : X × Y | p.2 ∈ F p.1} := by
  rw [← isOpen_compl_iff, isOpen_prod_iff]
  intro x₀ y₀ hy₀
  simp only [mem_compl_iff, mem_setOf_eq] at hy₀
  have hsep := SeparatedNhds.of_isCompact_isCompact isCompact_singleton (hF' x₀)
    (Set.disjoint_singleton_left.mpr hy₀)
  rw [SeparatedNhds.eq_1] at hsep
  obtain ⟨Vy, VF, hVy_open, hVF_open, hy_sub, hF_sub, hd⟩ := hsep
  exact ⟨{x | F x ⊆ VF}, Vy, hF.isOpen_of_isOpen VF hVF_open, hVy_open, hF_sub,
    hy_sub (Set.mem_singleton y₀), by grind⟩

/-! ## Approximate fixed points from Schauder + approximate selections -/

/-- For every entourage `U` and neighborhood `W ∈ 𝓝 0`, Schauder + approximate selection
yield `x x' : k` and `y ∈ F x'` with `(x, x') ∈ U` and `↑x - y ∈ W`. -/
lemma approx_fixed_point_data {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [LocallyConvexSpace ℝ E]
    {k : Set E} (hk : IsCompact k) (hk' : Convex ℝ k) (hk'' : k.Nonempty)
    {F : k → Set E} (hF : UpperHemicontinuous F) (hFk : ∀ x, F x ⊆ k)
    (hFconv : ∀ x, Convex ℝ (F x)) (hFne : ∀ x, (F x).Nonempty)
    {U : Set (k × k)} (hU : U ∈ @uniformity k (instUniformSpaceSubtype (p := (· ∈ k))
      (t := IsTopologicalAddGroup.rightUniformSpace E)))
    {W : Set E} (hW : W ∈ 𝓝 (0 : E)) :
    ∃ (x x' : k) (y : E), y ∈ F x' ∧ (x, x') ∈ U ∧ (↑x : E) - y ∈ W := by
  letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  haveI : CompactSpace k := isCompact_iff_compactSpace.mp hk
  haveI : ParacompactSpace k := paracompact_of_compact
  obtain ⟨f, hf_cont, hf_range, hf_approx⟩ := hF.exists_isApproxSelection' hFne hFconv hU hW hk' hFk
  have hf_mem : ∀ a : k, f a ∈ k := Set.range_subset_iff.mp hf_range
  obtain ⟨x, hx⟩ := (hf_cont.codRestrict hf_mem).exists_fixedPt_of_isConvex_isCompact hk hk' hk''
  have hfx : f x = ↑x := congr_arg Subtype.val hx
  obtain ⟨x', hxx', hfx_mem⟩ := hf_approx x
  rw [hfx, Set.mem_add] at hfx_mem
  obtain ⟨y, hy, w, hw, hyw⟩ := hfx_mem
  exact ⟨x, x', y, hy, hxx', show (↑x : E) - y ∈ W by rwa [show (↑x : E) - y = w by grind]⟩

/-! ## Constructing convergent nets from approximate data -/

/-- A `V ∈ 𝓝 0` lifts to an entourage in the subtype uniformity. -/
lemma nhd_zero_mem_entourage_subtype {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [LocallyConvexSpace ℝ E]
    {k : Set E} {V : Set E} (hV : V ∈ 𝓝 (0 : E)) :
    {p : ↑k × ↑k | (↑p.2 : E) - ↑p.1 ∈ V} ∈
      @uniformity k (instUniformSpaceSubtype (p := (· ∈ k))
        (t := IsTopologicalAddGroup.rightUniformSpace E)) := by
  rw [@uniformity_setCoe _ k (IsTopologicalAddGroup.rightUniformSpace E),
      show @uniformity E (IsTopologicalAddGroup.rightUniformSpace E) =
        Filter.comap (fun (p : E × E) => p.2 - p.1) (𝓝 0) from rfl, Filter.comap_comap]
  exact Filter.preimage_mem_comap hV

lemma raw_approx_index_codirected {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [LocallyConvexSpace ℝ E]
    {k : Set E} :
    let unif := @uniformity k (instUniformSpaceSubtype (p := (· ∈ k))
        (t := IsTopologicalAddGroup.rightUniformSpace E))
    let ι := { p : Set (↑k × ↑k) × Set E // p.1 ∈ unif ∧ p.2 ∈ 𝓝 (0 : E) }
    Nonempty ι ∧ IsCodirectedOrder ι := by
  intro unif ι
  exact ⟨⟨⟨(Set.univ, Set.univ), Filter.univ_mem, Filter.univ_mem⟩⟩, by
    rw [IsCodirectedOrder.eq_1]
    exact ⟨fun ⟨⟨U₁, W₁⟩, hU₁, hW₁⟩ ⟨⟨U₂, W₂⟩, hU₂, hW₂⟩ =>
      ⟨⟨⟨U₁ ∩ U₂, W₁ ∩ W₂⟩, inter_mem hU₁ hU₂, inter_mem hW₁ hW₂⟩,
       ⟨inter_subset_left, inter_subset_left⟩,
       ⟨inter_subset_right, inter_subset_right⟩⟩⟩⟩

lemma tendsto_diff_of_entourage_atBot {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [LocallyConvexSpace ℝ E]
    {k : Set E}
    {xι x'ι : { p : Set (↑k × ↑k) × Set E //
      p.1 ∈ @uniformity k (instUniformSpaceSubtype (p := (· ∈ k))
        (t := IsTopologicalAddGroup.rightUniformSpace E)) ∧ p.2 ∈ 𝓝 (0 : E) } → ↑k}
    (hmem : ∀ i, (xι i, x'ι i) ∈ i.val.1) :
    Tendsto (fun i => (↑(x'ι i) : E) - ↑(xι i)) atBot (𝓝 0) := by
  obtain ⟨hne, hcodir⟩ := raw_approx_index_codirected (k := k)
  rw [Filter.tendsto_atBot']
  intro V hV
  refine ⟨⟨({p : ↑k × ↑k | (↑p.2 : E) - ↑p.1 ∈ V}, univ),
    nhd_zero_mem_entourage_subtype hV, univ_mem⟩, fun i hi => ?_⟩
  exact hi.1 (hmem i)

lemma tendsto_sub_of_nhd_atBot {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [LocallyConvexSpace ℝ E]
    {k : Set E}
    {xι : { p : Set (↑k × ↑k) × Set E //
      p.1 ∈ @uniformity k (instUniformSpaceSubtype (p := (· ∈ k))
        (t := IsTopologicalAddGroup.rightUniformSpace E)) ∧ p.2 ∈ 𝓝 (0 : E) } → ↑k}
    {yι : { p : Set (↑k × ↑k) × Set E //
      p.1 ∈ @uniformity k (instUniformSpaceSubtype (p := (· ∈ k))
        (t := IsTopologicalAddGroup.rightUniformSpace E)) ∧ p.2 ∈ 𝓝 (0 : E) } → E}
    (hmem : ∀ i, (↑(xι i) : E) - yι i ∈ i.val.2) :
    Tendsto (fun i => (↑(xι i) : E) - yι i) atBot (𝓝 0) := by
  rw [tendsto_def]
  intro V hV
  exact Filter.mem_of_superset
    (Filter.mem_atBot ⟨(Set.univ, V), Filter.univ_mem, hV⟩)
    fun i (hi : i ≤ _) => hi.2 (hmem i)

lemma raw_approx_data {E : Type u} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [LocallyConvexSpace ℝ E]
    {k : Set E} {F : k → Set E}
    (hApprox : ∀ (U : Set (k × k)),
      U ∈ @uniformity k (instUniformSpaceSubtype (p := (· ∈ k))
        (t := IsTopologicalAddGroup.rightUniformSpace E)) →
      ∀ (W : Set E), W ∈ 𝓝 (0 : E) →
      ∃ (x x' : k) (y : E), y ∈ F x' ∧ (x, x') ∈ U ∧ (↑x : E) - y ∈ W) :
    ∃ (ι : Type u) (l₀ : Filter ι) (_ : l₀.NeBot) (xι x'ι : ι → k) (yι : ι → E),
      (∀ i, yι i ∈ F (x'ι i)) ∧
      Tendsto (fun i => (↑(x'ι i) : E) - ↑(xι i)) l₀ (𝓝 0) ∧
      Tendsto (fun i => (↑(xι i) : E) - yι i) l₀ (𝓝 0) := by
  let unif := @uniformity k (instUniformSpaceSubtype (p := (· ∈ k))
      (t := IsTopologicalAddGroup.rightUniformSpace E))
  let ι := { p : Set (↑k × ↑k) × Set E // p.1 ∈ unif ∧ p.2 ∈ 𝓝 (0 : E) }
  choose xι x'ι yι hy hpair hsub using
    fun (i : ι) => hApprox i.val.1 i.2.1 i.val.2 i.2.2
  obtain ⟨hne, hcodir⟩ := raw_approx_index_codirected (k := k)
  haveI : Nonempty ι := hne
  haveI : IsCodirectedOrder ι := hcodir
  exact ⟨ι, atBot, atBot_neBot, xι, x'ι, yι, hy,
    tendsto_diff_of_entourage_atBot (hmem := hpair),
    tendsto_sub_of_nhd_atBot (hmem := hsub)⟩

/-! ## Cluster point extraction -/

lemma compact_cluster_refine {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} {l₀ : Filter ι} [l₀.NeBot] (xι : ι → X) :
    ∃ x₀ : X, (l₀ ⊓ comap xι (𝓝 x₀)).NeBot ∧
      Tendsto xι (l₀ ⊓ comap xι (𝓝 x₀)) (𝓝 x₀) := by
  have hle : map xι l₀ ≤ principal univ := le_principal_iff.mpr (univ_mem)
  obtain ⟨x₀, _, hcp⟩ := isCompact_univ.exists_mapClusterPt hle
  refine ⟨x₀, ?_, ?_⟩
  · rw [MapClusterPt.eq_1] at hcp
    have hnebot := hcp.neBot
    rw [inf_comm, ← Filter.push_pull] at hnebot
    exact (Filter.map_neBot_iff xι).mp hnebot
  · exact Filter.tendsto_inf_right Filter.tendsto_comap

/-! ## Assembling the cluster-point argument -/

lemma approx_data_cluster_point {E : Type u} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [LocallyConvexSpace ℝ E]
    {k : Set E} (hk : IsCompact k)
    {F : k → Set E}
    (hApprox : ∀ (U : Set (k × k)),
      U ∈ @uniformity k (instUniformSpaceSubtype (p := (· ∈ k))
        (t := IsTopologicalAddGroup.rightUniformSpace E)) →
      ∀ (W : Set E), W ∈ 𝓝 (0 : E) →
      ∃ (x x' : k) (y : E), y ∈ F x' ∧ (x, x') ∈ U ∧ (↑x : E) - y ∈ W) :
    ∃ (ι : Type u) (l : Filter ι) (_ : l.NeBot) (xι x'ι : ι → k) (yι : ι → E),
      (∀ᶠ i in l, yι i ∈ F (x'ι i)) ∧
      (∃ x₀ : k, Tendsto (fun i => (↑(xι i) : E)) l (𝓝 ↑x₀) ∧
        Tendsto (fun i => (↑(x'ι i) : E)) l (𝓝 ↑x₀) ∧
        Tendsto yι l (𝓝 ↑x₀)) := by
  obtain ⟨ι, l₀, hl₀, xι, x'ι, yι, hmem, hpair, hdiff⟩ := raw_approx_data hApprox
  haveI : CompactSpace k := isCompact_iff_compactSpace.mp hk
  obtain ⟨x₀, hNeBot, hxTendsto⟩ := compact_cluster_refine (l₀ := l₀) xι
  set l := l₀ ⊓ comap xι (𝓝 x₀)
  have hl_le : l ≤ l₀ := inf_le_left
  have hx_conv := tendsto_subtype_rng.mp hxTendsto
  exact ⟨ι, l, hNeBot, xι, x'ι, yι,
    Eventually.filter_mono hl_le (Eventually.of_forall hmem), x₀, hx_conv,
    show _ by simpa [add_zero, add_sub_cancel] using hx_conv.add (hpair.mono_left hl_le),
    show _ by simpa [sub_sub_cancel, sub_zero] using hx_conv.sub (hdiff.mono_left hl_le)⟩

/-! ## Main theorem -/

public theorem kakutaniGlicksbergFan {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [LocallyConvexSpace ℝ E]
    {k : Set E} (hk : IsCompact k) (hk' : Convex ℝ k) (hk'' : k.Nonempty)
    {F : k → Set E} {hF : UpperHemicontinuous F} (hF' : ∀ x, F x ⊆ k)
    (hF'' : ∀ x, IsCompact (F x)) (hF''' : ∀ x, Convex ℝ (F x)) (hF'''' : ∀ x, (F x).Nonempty) :
    ∃ x, ↑x ∈ F x := by
  have hGraph := hF.isClosed_graph hF''
  have hData U hU W hW := approx_fixed_point_data hk hk' hk'' hF hF' hF''' hF''''
    (U := U) hU (W := W) hW
  obtain ⟨ι, l, hl, xι, x'ι, yι, hmem, x₀, hx, hx', hy⟩ :=
    approx_data_cluster_point hk hData
  exact ⟨x₀, hGraph.mem_of_tendsto ((tendsto_subtype_rng.mpr hx').prodMk_nhds hy) hmem⟩
