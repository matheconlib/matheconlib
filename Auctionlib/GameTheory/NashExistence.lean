module

public import Auctionlib.GameTheory.Basic
public import Mathlib.Analysis.Convex.Quasiconvex

import Auctionlib.ForMathlib.ApproximateSelection
import Auctionlib.ForMathlib.Kakutani
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Existence of Nash equilibria
This file contains classical, mostly auto-formalised results on the existence of Nash equilibria.

Currently, the only public declaration in this file are:
* `Game.Continuous`: typeclass stating that the outcome function of a game whose action spaces and
  outcome space are topological spaces is continuous.
* `PayoffStructure.Continuous`: typeclass stating that the payoff functions of a payoff structure on
  a topological space are continuous.
* `Game.exists_isNashEquilibrium_of_quasiconcaveOn`: existence of pure Nash equilibria for games
  whose action spaces are homeomorphic to nonempty compact convex subsets of locally convex vector
  spaces in such a way that their payoff functions are quasiconcave.
* `Game.exists_isNashEquilibrium_of_isCompact`: existence of mixed Nash equlibria for games with
  nonempty compact metrisable action spaces and continuous payoff functions.
* `Game.exists_isNashEquilibrium_of_finite`: existence of mixed Nash equilibria for finite games.
All other declarations used in the proofs are kept private.

## TODOs:
* get rid of unnecessary assumption `P.toExpected.Continuous` in
  `Game.exists_isNashEquilibrium_of_isCompact`.
* get rid of unnecessary assumptions `∀ i, DiscreteMeasurableSpace (A i)`,
  `DiscreteMeasurableSpace O` and `Fintype O` in`Game.exists_isNashEquilibrium_of_finite`.
-/

namespace GameTheory

variable {ι : Type*} {A : ι → Type*} {O : Type*}

section Helpers

/-! ## Encoding/decoding between strategy profiles and product spaces -/

lemma isCompact_ki {ι : Type*} {A : ι → Type*} {E : ι → Type*}
    [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)]
    [∀ i, TopologicalSpace (E i)]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i) (i : ι) :
    IsCompact (k i) := by
  rw [show k i = Set.range (Subtype.val ∘ (e i)) from Set.ext fun x =>
    ⟨fun hx => ⟨(e i).symm ⟨x, hx⟩, by simp⟩, fun ⟨a, ha⟩ => ha ▸ (e i a).property⟩]
  exact isCompact_range (continuous_subtype_val.comp (e i).continuous)

lemma nonempty_ki {ι : Type*} {A : ι → Type*} {E : ι → Type*}
    [∀ i, TopologicalSpace (A i)] [∀ i, Nonempty (A i)]
    [∀ i, TopologicalSpace (E i)]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i) (i : ι) :
    (k i).Nonempty :=
  ⟨_, (e i (Classical.arbitrary (A i))).property⟩

/-- Decode a point in the product space `∏ k i` to a strategy profile. -/
noncomputable def decode {ι : Type*} {A : ι → Type*} {E : ι → Type*}
    [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (E i)]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i)
    (x : ↑(Set.univ.pi k)) : (i : ι) → A i :=
  fun i => (e i).symm ⟨x.val i, x.property i (Set.mem_univ i)⟩

/-- Encode a strategy profile as a point in `∏ E i`. -/
noncomputable def encode {ι : Type*} {A : ι → Type*} {E : ι → Type*}
    [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (E i)]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i)
    (a : (i : ι) → A i) : (i : ι) → E i :=
  fun i => ((e i) (a i)).val

lemma encode_mem {ι : Type*} {A : ι → Type*} {E : ι → Type*}
    [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (E i)]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i)
    (a : (i : ι) → A i) : encode e a ∈ Set.univ.pi k :=
  fun i _ => ((e i) (a i)).property

/-! ## Best response correspondence -/

/-- The best response correspondence maps a point in the product space to the set of
strategy profiles where each player plays a best response. -/
noncomputable def bestResponseCorr {ι : Type*} {A : ι → Type*} {O : Type*} {E : ι → Type*}
    [DecidableEq ι] [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (E i)]
    [TopologicalSpace O]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i)
    (G : Game A O) (P : PayoffStructure O ι) :
    ↑(Set.univ.pi k) → Set ((i : ι) → E i) :=
  fun x =>
    let a := decode e x
    { y | ∃ (hy : ∀ i, y i ∈ k i),
      ∀ i (s : A i), P.payoff i (G.outcome (Function.update a i s)) ≤
        P.payoff i (G.outcome (Function.update a i ((e i).symm ⟨y i, hy i⟩))) }

lemma bestResponseCorr_subset {ι : Type*} {A : ι → Type*} {O : Type*} {E : ι → Type*}
    [DecidableEq ι] [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (E i)]
    [TopologicalSpace O]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i)
    (G : Game A O) (P : PayoffStructure O ι)
    (x : ↑(Set.univ.pi k)) :
    bestResponseCorr e G P x ⊆ Set.univ.pi k := fun _ ⟨hyk, _⟩ i _ => hyk i

lemma payoff_update_continuous {ι : Type*} {A : ι → Type*} {O : Type*}
    [DecidableEq ι] [∀ i, TopologicalSpace (A i)] [TopologicalSpace O]
    (G : Game A O) (P : PayoffStructure O ι)
    [G.Continuous] [P.Continuous]
    (a : (i : ι) → A i) (i : ι) :
    Continuous (fun s => P.payoff i (G.outcome (Function.update a i s))) :=
  (PayoffStructure.continuous_payoff i).comp <|
    (Game.continuous_outcome (G := G)).comp (continuous_const.update i continuous_id)

lemma exists_payoff_maximizer {ι : Type*} {A : ι → Type*} {O : Type*}
    [DecidableEq ι] [∀ i, TopologicalSpace (A i)] [TopologicalSpace O]
    (G : Game A O) (P : PayoffStructure O ι)
    [G.Continuous] [P.Continuous]
    [∀ i, CompactSpace (A i)] [∀ i, Nonempty (A i)]
    (a : (i : ι) → A i) (i : ι) :
    ∃ s_i : A i, ∀ s : A i,
      P.payoff i (G.outcome (Function.update a i s)) ≤
        P.payoff i (G.outcome (Function.update a i s_i)) :=
  let ⟨x, _, hx⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    (payoff_update_continuous G P a i).continuousOn
  ⟨x, fun s => hx (Set.mem_univ s)⟩

lemma decode_encode_component {ι : Type*} {A : ι → Type*} {E : ι → Type*}
    [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (E i)]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i)
    (maximizers : (i : ι) → A i) (i : ι)
    (hy : ∀ j, encode e maximizers j ∈ k j) :
    (e i).symm ⟨encode e maximizers i, hy i⟩ = maximizers i :=
  (congrArg (e i).symm (Subtype.ext rfl)).trans ((e i).symm_apply_apply (maximizers i))

lemma bestResponseCorr_nonempty {ι : Type*} {A : ι → Type*} {O : Type*} {E : ι → Type*}
    [Fintype ι] [DecidableEq ι]
    [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)] [∀ i, Nonempty (A i)]
    [∀ i, TopologicalSpace (E i)]
    [TopologicalSpace O]
    (G : Game A O) (P : PayoffStructure O ι)
    [G.Continuous] [P.Continuous]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i)
    (x : ↑(Set.univ.pi k)) :
    (bestResponseCorr e G P x).Nonempty := by
  choose maximizers hmax using fun i => exists_payoff_maximizer G P (decode e x) i
  have hy : ∀ i, encode e maximizers i ∈ k i := fun i => encode_mem e maximizers i (Set.mem_univ i)
  exact ⟨encode e maximizers, hy, fun i s =>
    (decode_encode_component e maximizers i hy) ▸ hmax i s⟩

lemma extend_eq_payoff {ι : Type*} {A : ι → Type*} {O : Type*} {E : ι → Type*}
    [DecidableEq ι] [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (E i)]
    [TopologicalSpace O]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i)
    (G : Game A O) (P : PayoffStructure O ι)
    (a : (i : ι) → A i) (i : ι) (z : E i) (hz : z ∈ k i) :
    Subtype.val.extend
      ((fun s ↦ P.payoff i (G.outcome (Function.update a i s))) ∘ (e i).symm) 0 z =
    P.payoff i (G.outcome (Function.update a i ((e i).symm ⟨z, hz⟩))) := by
  simpa using Subtype.val_injective.extend_apply
    ((fun s ↦ P.payoff i (G.outcome (Function.update a i s))) ∘ (e i).symm) 0 ⟨z, hz⟩

lemma bestResponseCorr_convex {ι : Type*} {A : ι → Type*} {O : Type*} {E : ι → Type*}
    [Fintype ι] [DecidableEq ι]
    [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)] [∀ i, Nonempty (A i)]
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)] [∀ i, TopologicalSpace (E i)]
    [TopologicalSpace O]
    (G : Game A O) (P : PayoffStructure O ι)
    [G.Continuous] [P.Continuous]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i)
    (hs : ∀ i, Convex ℝ (k i))
    (h_quasiconcave : ∀ a i, QuasiconcaveOn ℝ (k i) <| Subtype.val.extend
      ((fun s ↦ P.payoff i (G.outcome (Function.update a i s))) ∘ (e i).symm) 0)
    (x : ↑(Set.univ.pi k)) :
    Convex ℝ (bestResponseCorr e G P x) := by
  have superlevel : ∀ y, y ∈ bestResponseCorr e G P x → ∀ i (s : A i),
      P.payoff i (G.outcome (Function.update (decode e x) i s)) ≤ Subtype.val.extend
        ((fun s ↦ P.payoff i (G.outcome (Function.update (decode e x) i s))) ∘ (e i).symm)
        0 (y i) := fun _ ⟨hyk, hbr⟩ i s => by
    rw [extend_eq_payoff e G P (decode e x) i _ (hyk i)]
    exact hbr i s
  intro y₁ hy₁ y₂ hy₂ a b ha hb hab
  refine ⟨fun i => (hs i) (hy₁.1 i) (hy₂.1 i) ha hb hab, fun i s => ?_⟩
  have := ((h_quasiconcave (decode e x) i)
    (P.payoff i (G.outcome (Function.update (decode e x) i s)))
    ⟨hy₁.1 i, superlevel y₁ hy₁ i s⟩ ⟨hy₂.1 i, superlevel y₂ hy₂ i s⟩ ha hb hab).2
  rwa [extend_eq_payoff] at this

lemma bestResponse_isCompact {ι : Type*} {A : ι → Type*} {O : Type*}
    [DecidableEq ι]
    [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)]
    [TopologicalSpace O]
    (G : Game A O) (P : PayoffStructure O ι)
    [G.Continuous] [P.Continuous]
    (a : (i : ι) → A i) (i : ι) :
    IsCompact { s : A i | ∀ t : A i,
      P.payoff i (G.outcome (Function.update a i t)) ≤
        P.payoff i (G.outcome (Function.update a i s)) } := by
  apply IsClosed.isCompact
  rw [show { s : A i | ∀ t, P.payoff i (G.outcome (Function.update a i t)) ≤
      P.payoff i (G.outcome (Function.update a i s)) } =
    ⋂ t, { s | P.payoff i (G.outcome (Function.update a i t)) ≤
      P.payoff i (G.outcome (Function.update a i s)) } from by
    ext
    simp [Set.mem_iInter]]
  exact isClosed_iInter fun t => isClosed_le continuous_const (payoff_update_continuous G P a i)

lemma bestResponseCorr_eq_pi {ι : Type*} {A : ι → Type*} {O : Type*} {E : ι → Type*}
    [DecidableEq ι] [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (E i)]
    [TopologicalSpace O]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i)
    (G : Game A O) (P : PayoffStructure O ι)
    (x : ↑(Set.univ.pi k)) :
    bestResponseCorr e G P x = Set.univ.pi (fun i =>
      (fun s : A i => ((e i) s : E i)) '' { s : A i | ∀ t : A i,
        P.payoff i (G.outcome (Function.update (decode e x) i t)) ≤
          P.payoff i (G.outcome (Function.update (decode e x) i s)) }) := by
  ext y
  constructor
  · intro ⟨hyk, hbr⟩
    exact Set.mem_univ_pi.mpr fun i => (Set.mem_image _ _ _).mpr
      ⟨(e i).symm ⟨y i, hyk i⟩, hbr i,
        congrArg Subtype.val ((e i).apply_symm_apply ⟨y i, hyk i⟩)⟩
  · intro hy_mem
    simp only [Set.mem_univ_pi] at hy_mem
    choose si hsi_br hsi_eq using fun i => (Set.mem_image _ _ _).mp (hy_mem i)
    obtain rfl : y = encode e si := funext fun i => (hsi_eq i).symm
    exact ⟨Set.mem_univ_pi.mp (encode_mem e si), fun i s => by
      rw [decode_encode_component]
      exact hsi_br i s⟩

lemma bestResponseCorr_compact {ι : Type*} {A : ι → Type*} {O : Type*} {E : ι → Type*}
    [Fintype ι] [DecidableEq ι]
    [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)] [∀ i, Nonempty (A i)]
    [∀ i, TopologicalSpace (E i)]
    [TopologicalSpace O]
    (G : Game A O) (P : PayoffStructure O ι)
    [G.Continuous] [P.Continuous]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i)
    (x : ↑(Set.univ.pi k)) :
    IsCompact (bestResponseCorr e G P x) := by
  rw [bestResponseCorr_eq_pi]
  exact isCompact_univ_pi fun i =>
    (bestResponse_isCompact G P (decode e x) i).image (continuous_subtype_val.comp (e i).continuous)

lemma continuous_decode {ι : Type*} {A : ι → Type*} {E : ι → Type*}
    [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (E i)]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i) :
    Continuous (decode e) :=
  continuous_pi fun i => (e i).symm.continuous.comp
    (Continuous.subtype_mk ((continuous_apply i).comp continuous_subtype_val) _)

lemma isClosed_payoff_le {ι : Type*} {A : ι → Type*} {O : Type*} {E : ι → Type*}
    [Fintype ι] [DecidableEq ι]
    [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)] [∀ i, Nonempty (A i)]
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)] [∀ i, TopologicalSpace (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul ℝ (E i)]
    [∀ i, T2Space (E i)] [∀ i, LocallyConvexSpace ℝ (E i)]
    [TopologicalSpace O]
    (G : Game A O) (P : PayoffStructure O ι)
    [G.Continuous] [P.Continuous]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i) (i : ι) (s : A i) :
    IsClosed {p : ↑(Set.univ.pi k) × ↑(Set.univ.pi k) |
      P.payoff i (G.outcome (Function.update (decode e p.1) i s)) ≤
        P.payoff i (G.outcome (Function.update (decode e p.1) i (decode e p.2 i)))} :=
  let hcd := continuous_decode e
  isClosed_le
    ((PayoffStructure.continuous_payoff i).comp (Game.continuous_outcome.comp
      (Continuous.update (hcd.comp continuous_fst) i continuous_const)))
    ((PayoffStructure.continuous_payoff i).comp (Game.continuous_outcome.comp
      (Continuous.update (hcd.comp continuous_fst) i
        ((continuous_apply i).comp (hcd.comp continuous_snd)))))

lemma graph_eq_iInter {ι : Type*} {A : ι → Type*} {O : Type*} {E : ι → Type*}
    [Fintype ι] [DecidableEq ι]
    [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)] [∀ i, Nonempty (A i)]
    [∀ i, TopologicalSpace (E i)] [TopologicalSpace O]
    (G : Game A O) (P : PayoffStructure O ι)
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i) :
    {p : ↑(Set.univ.pi k) × ↑(Set.univ.pi k) | p.2.val ∈ bestResponseCorr e G P p.1} =
      ⋂ i, ⋂ s, {p : ↑(Set.univ.pi k) × ↑(Set.univ.pi k) |
        P.payoff i (G.outcome (Function.update (decode e p.1) i s)) ≤
          P.payoff i (G.outcome (Function.update (decode e p.1) i (decode e p.2 i)))} := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_iInter]
  exact ⟨fun ⟨_, h⟩ => h, fun hp => ⟨fun i => p.2.property i (Set.mem_univ i), hp⟩⟩

lemma bestResponseCorr_isClosed_graph {ι : Type*} {A : ι → Type*} {O : Type*} {E : ι → Type*}
    [Fintype ι] [DecidableEq ι]
    [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)] [∀ i, Nonempty (A i)]
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)] [∀ i, TopologicalSpace (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul ℝ (E i)]
    [∀ i, T2Space (E i)] [∀ i, LocallyConvexSpace ℝ (E i)]
    [TopologicalSpace O]
    (G : Game A O) (P : PayoffStructure O ι)
    [G.Continuous] [P.Continuous]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i) :
    IsClosed {p : ↑(Set.univ.pi k) × ((i : ι) → E i) | p.2 ∈ bestResponseCorr e G P p.1} := by
  have hk := fun i => isCompact_ki e i
  rw [show {p : ↑(Set.univ.pi k) × ((i : ι) → E i) | p.2 ∈ bestResponseCorr e G P p.1} =
    (Prod.map id Subtype.val) ''
      {p : ↑(Set.univ.pi k) × ↑(Set.univ.pi k) | p.2.val ∈ bestResponseCorr e G P p.1} from by
    ext ⟨x, y⟩
    simp only [Set.mem_setOf_eq, Set.mem_image, Prod.exists, Prod.map]
    exact ⟨fun hy => ⟨x, ⟨y, bestResponseCorr_subset e G P x hy⟩, hy, rfl⟩,
      fun ⟨_, _, hb, heq⟩ => by
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        exact hb⟩]
  exact (IsProperMap.prodMap isProperMap_id
    ((isClosed_set_pi fun i _ => (hk i).isClosed).isProperMap_subtypeVal)).isClosedMap _ <| by
    rw [graph_eq_iInter G P e]
    exact isClosed_iInter fun i => isClosed_iInter fun s => isClosed_payoff_le G P e i s

/-! ## Upper hemicontinuity -/

private lemma uhc_compl_eq_fst_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {F : X → Set Y} {V : Set Y} :
    {x : X | F x ⊆ V}ᶜ = Prod.fst '' ({p : X × Y | p.2 ∈ F p.1} ∩ (Set.univ ×ˢ Vᶜ)) := by
  ext x
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_image, Set.mem_inter_iff,
    Set.mem_prod, Set.mem_univ, true_and]
  exact ⟨fun hx => by
      rw [Set.not_subset] at hx
      obtain ⟨y, hy_mem, hy_not⟩ := hx
      exact ⟨(x, y), ⟨hy_mem, Set.mem_compl hy_not⟩, rfl⟩,
    fun ⟨⟨_, b⟩, ⟨hb_mem, hb_compl⟩, rfl⟩ h => hb_compl (h hb_mem)⟩

lemma uhc_of_closedGraph_compact {ι : Type*} {E : ι → Type*}
    [∀ i, TopologicalSpace (E i)]
    [∀ i, T2Space (E i)]
    {k : (i : ι) → Set (E i)}
    (hk : ∀ i, IsCompact (k i))
    {F : ↑(Set.univ.pi k) → Set ((i : ι) → E i)}
    (hF_sub : ∀ x, F x ⊆ Set.univ.pi k)
    (hF_closed : IsClosed {p : ↑(Set.univ.pi k) × ((i : ι) → E i) | p.2 ∈ F p.1}) :
    UpperHemicontinuous F := by
  rw [upperHemicontinuous_iff_isOpen_of_isOpen]
  intro V hV
  rw [← isClosed_compl_iff, uhc_compl_eq_fst_image]
  have hK := isCompact_univ_pi hk
  have : CompactSpace ↑(Set.univ.pi k) := isCompact_iff_compactSpace.mp hK
  exact (((isCompact_univ.prod hK).of_isClosed_subset
    (hF_closed.inter (IsClosed.prod isClosed_univ hV.isClosed_compl))
    (fun p hp => ⟨Set.mem_univ _, hF_sub p.1 hp.1⟩)).image continuous_fst).isClosed

lemma bestResponseCorr_uhc {ι : Type*} {A : ι → Type*} {O : Type*} {E : ι → Type*}
    [Fintype ι] [DecidableEq ι]
    [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)] [∀ i, Nonempty (A i)]
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)] [∀ i, TopologicalSpace (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul ℝ (E i)]
    [∀ i, T2Space (E i)] [∀ i, LocallyConvexSpace ℝ (E i)]
    [TopologicalSpace O]
    (G : Game A O) (P : PayoffStructure O ι)
    [G.Continuous] [P.Continuous]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i) :
    UpperHemicontinuous (bestResponseCorr e G P) :=
  uhc_of_closedGraph_compact (fun i => isCompact_ki e i)
    (fun x => bestResponseCorr_subset e G P x)
    (bestResponseCorr_isClosed_graph G P e)

/-! ## Fixed point to Nash equilibrium -/

/-- A fixed point of the best response correspondence yields a Nash equilibrium. -/
lemma fixed_point_is_nash {ι : Type*} {A : ι → Type*} {O : Type*} {E : ι → Type*}
    [Fintype ι] [DecidableEq ι]
    [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)] [∀ i, Nonempty (A i)]
    [∀ i, TopologicalSpace (E i)] [TopologicalSpace O]
    (G : Game A O) (P : PayoffStructure O ι)
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i)
    (x : ↑(Set.univ.pi k))
    (hfp : x.val ∈ bestResponseCorr e G P x) :
    G.IsNashEquilibrium P (decode e x) := by
  obtain ⟨hy, hfp⟩ := hfp
  intro i s
  have := hfp i s
  rwa [show (e i).symm ⟨x.val i, hy i⟩ = decode e x i from by simp [decode],
    Function.update_eq_self] at this

end Helpers

/-- Any game whose action spaces are nonempty compact convex subsets of locally convex vector spaces
and whose payoff functions are quasiconcave admits a pure Nash equilibrium.
Instead of requiring the action spaces to be literal subsets of vector spaces, we simply ask
homeomorphisms between the action spaces and such subsets for which the appropriate compositions
with the payoff functions are quasiconcave. -/
public theorem Game.exists_isNashEquilibrium_of_quasiconcaveOn
    (G : Game A O) (P : PayoffStructure O ι)
    [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)] [∀ i, Nonempty (A i)]
    [TopologicalSpace O] [G.Continuous] [P.Continuous]
    [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)] [∀ i, TopologicalSpace (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul ℝ (E i)] [∀ i, T2Space (E i)]
    [∀ i, LocallyConvexSpace ℝ (E i)]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i) (hs : ∀ i, Convex ℝ (k i))
    (h_quasiconcave : ∀ a i, QuasiconcaveOn ℝ (k i) <| Subtype.val.extend
      ((fun s ↦ P.payoff i (G.outcome (Function.update a i s))) ∘ (e i).symm) 0) :
    ∃ a, G.IsNashEquilibrium P a := by
  -- Apply Kakutani-Glicksberg-Fan to the product space with best response correspondence
  obtain ⟨x_star, hx_star⟩ := kakutaniGlicksbergFan (E := (i : ι) → E i) (k := Set.univ.pi k)
    (isCompact_univ_pi fun i => isCompact_ki e i)
    (convex_pi fun i _ => hs i)
    (Set.univ_pi_nonempty_iff.mpr fun i => nonempty_ki e i)
    (F := bestResponseCorr e G P) (hF := bestResponseCorr_uhc G P e)
    (bestResponseCorr_subset e G P)
    (bestResponseCorr_compact G P e)
    (bestResponseCorr_convex G P e hs h_quasiconcave)
    (bestResponseCorr_nonempty G P e)
  exact ⟨decode e x_star, fixed_point_is_nash G P e x_star hx_star⟩

section Helpers

open MeasureTheory ProbabilityTheory

/-- Homeomorphism from `ProbabilityMeasure α` onto the range of `toWeakDualContinuousMap`,
via continuous injection from compact to Hausdorff being a closed embedding. -/
noncomputable def toWeakDualContinuousMap_homeomorph {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [BorelSpace α] [CompactSpace α] [TopologicalSpace.MetrizableSpace α] :
    ProbabilityMeasure α ≃ₜ Set.range (ProbabilityMeasure.toWeakDualContinuousMap (α := α)) :=
  ProbabilityMeasure.toWeakDualContinuousMap_isClosedEmbedding.toHomeomorph

/-- The expected payoff for player `i` with mixed strategy `μ` equals a weak dual evaluation
`(toWeakDualContinuousMap μ)(φ)` for an appropriate `φ : C(A i, ℝ)`, using linearity of
integration and Fubini on pi types. -/
lemma payoff_eq_eval_weakDual {ι : Type*} {A : ι → Type*} {O : Type*}
    (G : Game A O) (P : PayoffStructure O ι) [Fintype ι] [DecidableEq ι]
    [∀ i, TopologicalSpace (A i)] [TopologicalSpace O]
    [∀ i, CompactSpace (A i)] [∀ i, TopologicalSpace.MetrizableSpace (A i)] [∀ i, Nonempty (A i)]
    [∀ i, MeasurableSpace (A i)] [MeasurableSpace O] [∀ i, BorelSpace (A i)] [BorelSpace O]
    [G.Continuous] [P.Continuous] [G.Measurable] [G.toMixed.Continuous] [P.toExpected.Continuous]
    (a : (i : ι) → ProbabilityMeasure (A i)) (i : ι) :
    ∀ μ : ProbabilityMeasure (A i),
      P.toExpected.payoff i (G.toMixed.outcome (Function.update a i μ)) =
        (ProbabilityMeasure.toWeakDualContinuousMap μ)
          ⟨(fun μ ↦ P.toExpected.payoff i (G.toMixed.outcome (Function.update a i μ))) ∘ diracProba,
            (PayoffStructure.continuous_payoff i).comp <| Game.continuous_outcome.comp <|
              continuous_const.update _  continuous_diracProba⟩ := by
  intro μ
  dsimp [ProbabilityMeasure.toWeakDualContinuousMap]
  change _ = integral _ _
  dsimp [PayoffStructure.toExpected]
  rw [integral_map G.measurable_outcome.aemeasurable (P.measurable_payoff i).aestronglyMeasurable,
    ← Measure.pi_map_piSplitAt i, integral_map (MeasurableEquiv.measurable _).aemeasurable
      (by exact ((P.measurable_payoff i).comp G.measurable_outcome).aestronglyMeasurable),
    Function.update_self, integral_prod]
  · congr 1
    ext x
    rw [integral_map G.measurable_outcome.aemeasurable (P.measurable_payoff i).aestronglyMeasurable,
      ← Measure.pi_map_piSplitAt i, integral_map (MeasurableEquiv.measurable _).aemeasurable
        (by exact ((P.measurable_payoff i).comp G.measurable_outcome).aestronglyMeasurable),
      Function.update_self, integral_prod,
      show (diracProba x).toMeasure = Measure.dirac x from rfl, integral_dirac]
    · grind
    · exact ((P.continuous_payoff i).comp <|
        G.continuous_outcome.comp (Homeomorph.piSplitAt i _).continuous_invFun).integrable
  · exact ((P.continuous_payoff i).comp <|
      G.continuous_outcome.comp (Homeomorph.piSplitAt i _).continuous_invFun).integrable

/-- The `Function.extend` of the payoff via `Subtype.val` agrees with the weak dual evaluation
on the range of `toWeakDualContinuousMap`. -/
lemma extend_payoff_eq_eval {ι : Type*} {A : ι → Type*} {O : Type*}
    (G : Game A O) (P : PayoffStructure O ι) [Fintype ι] [DecidableEq ι]
    [∀ i, TopologicalSpace (A i)] [TopologicalSpace O]
    [∀ i, CompactSpace (A i)] [∀ i, TopologicalSpace.MetrizableSpace (A i)] [∀ i, Nonempty (A i)]
    [∀ i, MeasurableSpace (A i)] [MeasurableSpace O] [∀ i, BorelSpace (A i)] [BorelSpace O]
    [G.Continuous] [P.Continuous] [G.Measurable] [G.toMixed.Continuous] [P.toExpected.Continuous]
    (a : (i : ι) → ProbabilityMeasure (A i)) (i : ι) :
    let φ : C(A i, ℝ) := ⟨(fun μ ↦ P.toExpected.payoff i (G.toMixed.outcome
      (Function.update a i μ))) ∘ diracProba,
      (PayoffStructure.continuous_payoff i).comp <| Game.continuous_outcome.comp <|
        continuous_const.update _ continuous_diracProba⟩
    ∀ v ∈ Set.range (ProbabilityMeasure.toWeakDualContinuousMap (α := A i)),
      (Subtype.val.extend
        ((fun s ↦ P.toExpected.payoff i (G.toMixed.outcome (Function.update a i s))) ∘
          toWeakDualContinuousMap_homeomorph.symm) 0) v =
      v φ := by
  intro φ v ⟨μ, hμ⟩
  subst hμ
  simp only [Function.comp_def]
  have h := Subtype.val_injective.extend_apply
    ((fun s ↦ P.toExpected.payoff i (G.toMixed.outcome (Function.update a i s))) ∘
      toWeakDualContinuousMap_homeomorph.symm)
    (0 : WeakDual ℝ C(A i, ℝ) → ℝ)
    ⟨ProbabilityMeasure.toWeakDualContinuousMap μ, ⟨μ, rfl⟩⟩
  simp only [Function.comp_def] at h
  have hsymm : toWeakDualContinuousMap_homeomorph.symm
      ⟨ProbabilityMeasure.toWeakDualContinuousMap μ, ⟨μ, rfl⟩⟩ = μ :=
    ProbabilityMeasure.toWeakDualContinuousMap_injective <| congrArg Subtype.val <| by
      have := toWeakDualContinuousMap_homeomorph.apply_symm_apply
        ⟨ProbabilityMeasure.toWeakDualContinuousMap μ, ⟨μ, rfl⟩⟩
      simp only [toWeakDualContinuousMap_homeomorph, Topology.IsEmbedding.toHomeomorph] at this
      exact this
  rw [h, hsymm]
  exact payoff_eq_eval_weakDual G P a i μ

/-- The expected payoff, extended to the weak dual, is quasiconcave on the range of
`toWeakDualContinuousMap`: it agrees with a linear functional on this convex set. -/
lemma payoff_quasiconcave {ι : Type*} {A : ι → Type*} {O : Type*}
    (G : Game A O) (P : PayoffStructure O ι) [Fintype ι] [DecidableEq ι]
    [∀ i, TopologicalSpace (A i)] [TopologicalSpace O]
    [∀ i, CompactSpace (A i)] [∀ i, TopologicalSpace.MetrizableSpace (A i)] [∀ i, Nonempty (A i)]
    [∀ i, MeasurableSpace (A i)] [MeasurableSpace O] [∀ i, BorelSpace (A i)] [BorelSpace O]
    [G.Continuous] [P.Continuous] [G.Measurable] [G.toMixed.Continuous] [P.toExpected.Continuous]
    (a : (i : ι) → ProbabilityMeasure (A i)) (i : ι) :
    QuasiconcaveOn ℝ (Set.range (ProbabilityMeasure.toWeakDualContinuousMap (α := A i)))
      (Subtype.val.extend
        ((fun s ↦ P.toExpected.payoff i (G.toMixed.outcome (Function.update a i s))) ∘
          toWeakDualContinuousMap_homeomorph.symm) 0) := by
  have hconv := ProbabilityMeasure.convex_range_toWeakDualContinuousMap (α := A i)
  have heq := extend_payoff_eq_eval G P a i
  let φ : C(A i, ℝ) := ⟨(fun μ ↦ P.toExpected.payoff i (G.toMixed.outcome
    (Function.update a i μ))) ∘ diracProba,
    (PayoffStructure.continuous_payoff i).comp <| Game.continuous_outcome.comp <|
      continuous_const.update _ continuous_diracProba⟩
  exact ((((WeakBilin.eval (topDualPairing ℝ C(A i, ℝ)) φ).toLinearMap).concaveOn hconv).congr
    (fun v hv ↦ (heq v hv).symm)).quasiconcaveOn

end Helpers

/-- Any game with nonempty compact metrisable action spaces and continuous payoff functions
admits a mixed Nash equilibrium. -/
public theorem Game.exists_isNashEquilibrium_of_isCompact {ι : Type*} {A : ι → Type*} {O : Type*}
    (G : Game A O) (P : PayoffStructure O ι) [Fintype ι] [DecidableEq ι]
    [∀ i, TopologicalSpace (A i)] [TopologicalSpace O]
    [∀ i, CompactSpace (A i)] [∀ i, TopologicalSpace.MetrizableSpace (A i)] [∀ i, Nonempty (A i)]
    [∀ i, MeasurableSpace (A i)] [MeasurableSpace O] [∀ i, BorelSpace (A i)] [BorelSpace O]
    [G.Continuous] [P.Continuous] [P.toExpected.Continuous] :
    ∃ a, G.toMixed.IsNashEquilibrium P.toExpected a := by
  haveI : ∀ i, Nonempty (MeasureTheory.ProbabilityMeasure (A i)) :=
    fun i ↦ ⟨⟨MeasureTheory.Measure.dirac (Classical.arbitrary (A i)),
      MeasureTheory.Measure.dirac.isProbabilityMeasure⟩⟩
  haveI : ∀ i, LocallyConvexSpace ℝ (WeakDual ℝ C(A i, ℝ)) :=
    fun _ ↦ WeakBilin.locallyConvexSpace
  exact G.toMixed.exists_isNashEquilibrium_of_quasiconcaveOn P.toExpected
    (fun _ ↦ toWeakDualContinuousMap_homeomorph)
    (fun _ ↦ MeasureTheory.ProbabilityMeasure.convex_range_toWeakDualContinuousMap)
    (fun a i ↦ payoff_quasiconcave G P a i)

/-- Any finite game (i.e. any game with finitely many players and finite action spaces)
admits a mixed Nash equilibrium. -/
public theorem Game.exists_isNashEquilibrium_of_finite (G : Game A O) (P : PayoffStructure O ι)
    [∀ i, MeasurableSpace (A i)] [MeasurableSpace O]
    [∀ i, DiscreteMeasurableSpace (A i)] [DiscreteMeasurableSpace O] [G.Measurable]
    [Fintype ι] [DecidableEq ι] [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [Fintype O] :
    ∃ a, G.toMixed.IsNashEquilibrium P.toExpected a := by
  let _ i : TopologicalSpace (A i) := ⊥
  let _ : TopologicalSpace O := ⊥
  have _ i : DiscreteTopology (A i) := ⟨rfl⟩
  have _ : DiscreteTopology O := ⟨rfl⟩
  have : G.Continuous := ⟨continuous_of_discreteTopology⟩
  have : P.Continuous := ⟨fun i ↦ continuous_of_discreteTopology⟩
  exact G.exists_isNashEquilibrium_of_isCompact P

end GameTheory
