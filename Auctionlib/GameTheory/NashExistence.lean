module

public import Auctionlib.GameTheory.Basic
public import Mathlib.Analysis.Convex.Quasiconvex

import Auctionlib.ForMathlib.ApproximateSelection
import Auctionlib.ForMathlib.Schauder

/-!
# Existence of Nash equilibria
This file contains an auto-formalisation of the existence of mixed-strategy Nash equilibria for
finite games. More classic results on the existence of Nash equilibria in other situations will be
added later on.

Currently, the only public declaration in this file are:
* Todo.
All other declarations are kept private.
-/

namespace GameTheory

variable {ι : Type} {A : ι → Type} {O : Type}

section Continuous

variable [∀ i, TopologicalSpace (A i)] [TopologicalSpace O]

namespace Game

protected class Continuous (G : Game A O) where
  continuous_outcome : Continuous G.outcome

export Continuous (continuous_outcome)

end Game

namespace PayoffStructure

protected class Continuous (P : PayoffStructure O ι) where
  continuous_payoff i : Continuous (P.payoff i)

export Continuous (continuous_payoff)

end PayoffStructure

end Continuous

def KakutaniGlicksbergFan : Prop :=
  ∀ {E : Type} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [LocallyConvexSpace ℝ E]
    {k : Set E} (_hk : IsCompact k) (_hk' : Convex ℝ k) (_hk'' : k.Nonempty)
    {F : k → Set E} {_hF : UpperHemicontinuous F} (_hF' : ∀ x, F x ⊆ k)
    (_hF'' : ∀ x, IsCompact (F x)) (_hF''' : ∀ x, Convex ℝ (F x))
    (_hF'''' : ∀ x, (F x).Nonempty),
    ∃ x, ↑x ∈ F x

/-! ## Encoding/decoding between strategy profiles and product spaces -/

lemma isCompact_ki {ι : Type} {A : ι → Type} {E : ι → Type}
    [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)]
    [∀ i, TopologicalSpace (E i)]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i) (i : ι) :
    IsCompact (k i) := by
  rw [show k i = Set.range (Subtype.val ∘ (e i)) from Set.ext fun x =>
    ⟨fun hx => ⟨(e i).symm ⟨x, hx⟩, by simp⟩, fun ⟨a, ha⟩ => ha ▸ (e i a).property⟩]
  exact isCompact_range (continuous_subtype_val.comp (e i).continuous)

lemma nonempty_ki {ι : Type} {A : ι → Type} {E : ι → Type}
    [∀ i, TopologicalSpace (A i)] [∀ i, Nonempty (A i)]
    [∀ i, TopologicalSpace (E i)]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i) (i : ι) :
    (k i).Nonempty :=
  ⟨_, (e i (Classical.arbitrary (A i))).property⟩

/-- Decode a point in the product space `∏ k i` to a strategy profile. -/
noncomputable def decode {ι : Type} {A : ι → Type} {E : ι → Type}
    [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (E i)]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i)
    (x : ↑(Set.univ.pi k)) : (i : ι) → A i :=
  fun i => (e i).symm ⟨x.val i, x.property i (Set.mem_univ i)⟩

/-- Encode a strategy profile as a point in `∏ E i`. -/
noncomputable def encode {ι : Type} {A : ι → Type} {E : ι → Type}
    [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (E i)]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i)
    (a : (i : ι) → A i) : (i : ι) → E i :=
  fun i => ((e i) (a i)).val

lemma encode_mem {ι : Type} {A : ι → Type} {E : ι → Type}
    [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (E i)]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i)
    (a : (i : ι) → A i) : encode e a ∈ Set.univ.pi k :=
  fun i _ => ((e i) (a i)).property

/-! ## Best response correspondence -/

/-- The best response correspondence maps a point in the product space to the set of
strategy profiles where each player plays a best response. -/
noncomputable def bestResponseCorr {ι : Type} {A : ι → Type} {O : Type} {E : ι → Type}
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

lemma bestResponseCorr_subset {ι : Type} {A : ι → Type} {O : Type} {E : ι → Type}
    [DecidableEq ι] [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (E i)]
    [TopologicalSpace O]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i)
    (G : Game A O) (P : PayoffStructure O ι)
    (x : ↑(Set.univ.pi k)) :
    bestResponseCorr e G P x ⊆ Set.univ.pi k := fun _ ⟨hyk, _⟩ i _ => hyk i

lemma payoff_update_continuous {ι : Type} {A : ι → Type} {O : Type}
    [DecidableEq ι] [∀ i, TopologicalSpace (A i)] [TopologicalSpace O]
    (G : Game A O) (P : PayoffStructure O ι)
    [G.Continuous] [P.Continuous]
    (a : (i : ι) → A i) (i : ι) :
    Continuous (fun s => P.payoff i (G.outcome (Function.update a i s))) :=
  (PayoffStructure.continuous_payoff i).comp <|
    (Game.continuous_outcome (G := G)).comp (continuous_const.update i continuous_id)

lemma exists_payoff_maximizer {ι : Type} {A : ι → Type} {O : Type}
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

lemma decode_encode_component {ι : Type} {A : ι → Type} {E : ι → Type}
    [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (E i)]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i)
    (maximizers : (i : ι) → A i) (i : ι)
    (hy : ∀ j, encode e maximizers j ∈ k j) :
    (e i).symm ⟨encode e maximizers i, hy i⟩ = maximizers i :=
  (congrArg (e i).symm (Subtype.ext rfl)).trans ((e i).symm_apply_apply (maximizers i))

lemma bestResponseCorr_nonempty {ι : Type} {A : ι → Type} {O : Type} {E : ι → Type}
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

lemma extend_eq_payoff {ι : Type} {A : ι → Type} {O : Type} {E : ι → Type}
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

lemma bestResponseCorr_convex {ι : Type} {A : ι → Type} {O : Type} {E : ι → Type}
    [Fintype ι] [DecidableEq ι]
    [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)] [∀ i, Nonempty (A i)]
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)] [∀ i, TopologicalSpace (E i)]
    [TopologicalSpace O]
    (G : Game A O) (P : PayoffStructure O ι)
    [G.Continuous] [P.Continuous]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i)
    (hs : ∀ i, Convex ℝ (k i))
    (h_quasiconcave : ∀ (a : (i : ι) → A i) i, QuasiconcaveOn ℝ (k i)
      (Subtype.val.extend ((fun s ↦ P.payoff i (G.outcome (Function.update a i s))) ∘ (e i).symm) 0))
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

lemma bestResponse_isCompact {ι : Type} {A : ι → Type} {O : Type}
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

lemma bestResponseCorr_eq_pi {ι : Type} {A : ι → Type} {O : Type} {E : ι → Type}
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

lemma bestResponseCorr_compact {ι : Type} {A : ι → Type} {O : Type} {E : ι → Type}
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

lemma continuous_decode {ι : Type} {A : ι → Type} {E : ι → Type}
    [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (E i)]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i) :
    Continuous (decode e) :=
  continuous_pi fun i => (e i).symm.continuous.comp
    (Continuous.subtype_mk ((continuous_apply i).comp continuous_subtype_val) _)

lemma isClosed_payoff_le {ι : Type} {A : ι → Type} {O : Type} {E : ι → Type}
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

lemma graph_eq_iInter {ι : Type} {A : ι → Type} {O : Type} {E : ι → Type}
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

lemma bestResponseCorr_isClosed_graph {ι : Type} {A : ι → Type} {O : Type} {E : ι → Type}
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

lemma uhc_of_closedGraph_compact {ι : Type} {E : ι → Type}
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

lemma bestResponseCorr_uhc {ι : Type} {A : ι → Type} {O : Type} {E : ι → Type}
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
lemma fixed_point_is_nash {ι : Type} {A : ι → Type} {O : Type} {E : ι → Type}
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

/-! ## Main theorem -/

theorem exists_isNashEquilibrium_of_isCompact_convex (G : Game A O) (P : PayoffStructure O ι)
    [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)] [∀ i, Nonempty (A i)]
    [TopologicalSpace O] [G.Continuous] [P.Continuous]
    [Fintype ι] [DecidableEq ι]
    {E : ι → Type} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)] [∀ i, TopologicalSpace (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul ℝ (E i)] [∀ i, T2Space (E i)]
    [∀ i, LocallyConvexSpace ℝ (E i)]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i) (hs : ∀ i, Convex ℝ (k i))
    (h_quasiconcave : ∀ (a : (i : ι) → A i) i, QuasiconcaveOn ℝ (k i)
      (Subtype.val.extend ((fun s ↦ P.payoff i (G.outcome (Function.update a i s))) ∘ (e i).symm) 0))
    (kakutani : KakutaniGlicksbergFan) :
    ∃ a, G.IsNashEquilibrium P a := by
  -- Apply Kakutani-Glicksberg-Fan to the product space with best response correspondence
  obtain ⟨x_star, hx_star⟩ := kakutani (E := (i : ι) → E i) (k := Set.univ.pi k)
    (isCompact_univ_pi fun i => isCompact_ki e i)
    (convex_pi fun i _ => hs i)
    (Set.univ_pi_nonempty_iff.mpr fun i => nonempty_ki e i)
    (F := bestResponseCorr e G P) (_hF := bestResponseCorr_uhc G P e)
    (bestResponseCorr_subset e G P)
    (bestResponseCorr_compact G P e)
    (bestResponseCorr_convex G P e hs h_quasiconcave)
    (bestResponseCorr_nonempty G P e)
  exact ⟨decode e x_star, fixed_point_is_nash G P e x_star hx_star⟩

end GameTheory

namespace GameTheory

/-! ## Nash equilibrium existence in finite games via the best-response map -/

section NashExistence

open MeasureTheory Classical

variable {ι : Type*} {A : ι → Type*} {O : Type*}
  [Fintype ι] [DecidableEq ι] [∀ i, Fintype (A i)]
  (G : Game A O) (P : PayoffStructure O ι)

noncomputable def expectedPayoffPure (x : (i : ι) → A i → ℝ) (i : ι) (s : A i) : ℝ :=
  ∑ a : (j : ι) → A j,
    (∏ j ∈ Finset.univ.filter (· ≠ i), x j (a j)) *
    if a i = s then P.payoff i (G.outcome a) else 0

noncomputable def expectedPayoffMixed (x : (i : ι) → A i → ℝ) (i : ι) : ℝ :=
  ∑ a : (j : ι) → A j, (∏ j, x j (a j)) * P.payoff i (G.outcome a)

noncomputable def gain (x : (i : ι) → A i → ℝ) (i : ι) (s : A i) : ℝ :=
  max 0 (expectedPayoffPure G P x i s - expectedPayoffMixed G P x i)

noncomputable def unnormalizedResponse (x : (i : ι) → A i → ℝ) (i : ι) (s : A i) : ℝ :=
  x i s + gain G P x i s

noncomputable def normDenom (x : (i : ι) → A i → ℝ) (i : ι) : ℝ :=
  ∑ s, unnormalizedResponse G P x i s

noncomputable def bestResponseMap (x : (i : ι) → A i → ℝ) : (i : ι) → A i → ℝ :=
  fun i s ↦ unnormalizedResponse G P x i s / normDenom G P x i

lemma gain_nonneg (x : (i : ι) → A i → ℝ) (i : ι) (s : A i) :
    0 ≤ gain G P x i s :=
  le_max_left 0 _

lemma normDenom_eq (x : (i : ι) → A i → ℝ)
    (hx : x ∈ Set.univ.pi (fun i ↦ stdSimplex ℝ (A i))) (i : ι) :
    normDenom G P x i = 1 + ∑ s, gain G P x i s := by
  simp only [normDenom, unnormalizedResponse, Finset.sum_add_distrib,
    (Set.mem_univ_pi.mp hx i).2]

lemma normDenom_ge_one (x : (i : ι) → A i → ℝ)
    (hx : x ∈ Set.univ.pi (fun i ↦ stdSimplex ℝ (A i))) (i : ι) :
    1 ≤ normDenom G P x i := by
  rw [normDenom_eq G P x hx i]
  linarith [Finset.sum_nonneg fun s (_ : s ∈ Finset.univ) ↦ gain_nonneg G P x i s]

lemma bestResponseMap_mapsTo :
    Set.MapsTo (bestResponseMap G P)
      (Set.univ.pi (fun i ↦ stdSimplex ℝ (A i)))
      (Set.univ.pi (fun i ↦ stdSimplex ℝ (A i))) := by
  intro x hx
  simp only [Set.mem_univ_pi] at hx ⊢
  intro i
  have hnd_pos : 0 < normDenom G P x i :=
    one_pos.trans_le <| normDenom_ge_one G P x (Set.mem_univ_pi.mpr hx) i
  refine ⟨fun s ↦ div_nonneg (add_nonneg ((hx i).1 s) (le_max_left 0 _)) hnd_pos.le, ?_⟩
  show ∑ s, unnormalizedResponse G P x i s / normDenom G P x i = 1
  rw [← Finset.sum_div]
  exact div_self hnd_pos.ne'

private lemma continuous_unnormalizedResponse (i : ι) (s : A i) :
    Continuous (fun x ↦ unnormalizedResponse G P x i s) := by
  unfold unnormalizedResponse gain expectedPayoffPure expectedPayoffMixed
  fun_prop

lemma bestResponseMap_continuousOn :
    ContinuousOn (bestResponseMap G P)
      (Set.univ.pi (fun i ↦ stdSimplex ℝ (A i))) := by
  unfold bestResponseMap
  simp_rw [continuousOn_pi]
  intro i s
  exact (continuous_unnormalizedResponse G P i s).continuousOn.div
    (continuous_finset_sum _ fun t _ ↦
      continuous_unnormalizedResponse G P i t).continuousOn
    fun x hx ↦ (one_pos.trans_le (normDenom_ge_one G P x hx i)).ne'

lemma expectedPayoffMixed_eq_sum (x : (i : ι) → A i → ℝ) (i : ι) :
    expectedPayoffMixed G P x i =
    ∑ s, x i s * expectedPayoffPure G P x i s := by
  simp only [expectedPayoffMixed, expectedPayoffPure, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ ↦ by
    simp only [mul_ite, mul_zero, ← mul_assoc]
    rw [Fintype.sum_ite_eq, Finset.filter_ne',
      Finset.mul_prod_erase Finset.univ (fun j ↦ x j (a j)) (Finset.mem_univ i)]

lemma gain_eq_mul_sub (x : (i : ι) → A i → ℝ)
    (hx : x ∈ Set.univ.pi (fun i ↦ stdSimplex ℝ (A i)))
    (hfixed : bestResponseMap G P x = x) (i : ι) (s : A i) :
    gain G P x i s = x i s * (normDenom G P x i - 1) := by
  have hnd_pos := one_pos.trans_le (normDenom_ge_one G P x hx i)
  have key : unnormalizedResponse G P x i s / normDenom G P x i = x i s :=
    congr_fun (congr_fun hfixed i) s
  rw [div_eq_iff hnd_pos.ne'] at key
  simp only [unnormalizedResponse] at key
  linarith

private lemma weighted_avg_lt {α : Type*} [Fintype α] (w : α → ℝ) (f : α → ℝ) (c : ℝ)
    (hw_nonneg : ∀ a, 0 ≤ w a) (hw_sum : ∑ a, w a = 1)
    (hcf : ∀ a, 0 < w a → c < f a) (ha : ∃ a, 0 < w a) :
    c < ∑ a, w a * f a := by
  rw [show c = ∑ a : α, w a * c from by rw [← Finset.sum_mul, hw_sum, one_mul]]
  obtain ⟨a₀, ha₀⟩ := ha
  exact Finset.sum_lt_sum
    (fun a _ ↦ by
      rcases (hw_nonneg a).eq_or_lt' with heq | hw_pos
      · simp [heq]
      · exact mul_le_mul_of_nonneg_left (hcf a hw_pos).le (hw_nonneg a))
    ⟨a₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (hcf a₀ ha₀) ha₀⟩

lemma fixedPoint_gains_zero (x : (i : ι) → A i → ℝ)
    (hx : x ∈ Set.univ.pi (fun i ↦ stdSimplex ℝ (A i)))
    (hfixed : bestResponseMap G P x = x)
    (i : ι) (s : A i) : gain G P x i s = 0 := by
  have hxi := Set.mem_univ_pi.mp hx i
  have hgain_eq := gain_eq_mul_sub G P x hx hfixed i
  by_contra h
  have hs_pos := (gain_nonneg G P x i s).lt_of_ne' h
  have hnd_sub : 0 < normDenom G P x i - 1 := by
    rw [normDenom_eq G P x hx i]
    linarith [Finset.sum_pos' (fun t _ ↦ gain_nonneg G P x i t)
      ⟨s, Finset.mem_univ s, hs_pos⟩]
  have hpure_gt (t : A i) (hxt : 0 < x i t) :
      expectedPayoffMixed G P x i < expectedPayoffPure G P x i t := by
    have := hgain_eq t ▸ mul_pos hxt hnd_sub
    simp only [gain, lt_max_iff] at this
    linarith [this.resolve_left (by linarith)]
  obtain ⟨t, ht⟩ : ∃ t, 0 < x i t := by
    by_contra hall
    push_neg at hall
    linarith [hxi.2, Finset.sum_nonpos fun t (_ : t ∈ Finset.univ) ↦ hall t]
  exact (expectedPayoffMixed_eq_sum G P x i ▸
    weighted_avg_lt (x i) _ _ hxi.1 hxi.2 hpure_gt ⟨t, ht⟩).ne rfl

/-! ### Connecting the simplex formulation to the measure-theoretic one -/

private lemma equivStdSimplex_symm_singleton_toReal
    {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α] [Fintype α]
    (w : α → ℝ) (hw : w ∈ stdSimplex ℝ α) (a : α) :
    ((↑(ProbabilityMeasure.equivStdSimplex.symm ⟨w, hw⟩) : Measure α) {a}).toReal = w a := by
  simp [ProbabilityMeasure.equivStdSimplex, Set.indicator]; rfl

variable [∀ i, MeasurableSpace (A i)] [MeasurableSpace O]
  [∀ i, DiscreteMeasurableSpace (A i)] [DiscreteMeasurableSpace O] [G.Measurable]

lemma integral_pi_eq_weighted_sum
    (σ : (j : ι) → ProbabilityMeasure (A j))
    (f : ((j : ι) → A j) → ℝ) :
    ∫ a, f a ∂(ProbabilityMeasure.pi σ) =
    ∑ a : (j : ι) → A j, (∏ j, ((σ j) {a j}).toReal) * f a := by
  rw [integral_fintype f Integrable.of_finite]
  exact Finset.sum_congr rfl fun a _ ↦ by
    rw [Measure.real.eq_1, smul_eq_mul, ProbabilityMeasure.toMeasure_pi,
      Measure.pi_singleton, ENNReal.toReal_prod]
    simp [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]

lemma payoff_as_weighted_sum
    (σ : (j : ι) → ProbabilityMeasure (A j)) (i : ι) :
    P.toExpected.payoff i (G.toMixed.outcome σ) =
    ∑ a : (j : ι) → A j, (∏ j, ((σ j) {a j}).toReal) * P.payoff i (G.outcome a) := by
  simp only [PayoffStructure.toExpected, Game.toMixed_outcome,
    ProbabilityMeasure.toMeasure_map, integral_map G.measurable_outcome.aemeasurable
    Measurable.of_discrete.aestronglyMeasurable, integral_pi_eq_weighted_sum]

lemma payoff_baseline_eq (x : (i : ι) → A i → ℝ)
    (hx_mem : ∀ j, x j ∈ stdSimplex ℝ (A j)) (i : ι) :
    P.toExpected.payoff i (G.toMixed.outcome
      (fun j ↦ ProbabilityMeasure.equivStdSimplex.symm ⟨x j, hx_mem j⟩)) =
    expectedPayoffMixed G P x i := by
  simp only [payoff_as_weighted_sum, expectedPayoffMixed]
  exact Finset.sum_congr rfl fun a _ ↦
    congrArg (· * _) (Finset.prod_congr rfl fun j _ ↦
      equivStdSimplex_symm_singleton_toReal (x j) (hx_mem j) (a j))

lemma prod_update_eq (x : (i : ι) → A i → ℝ)
    (hx_mem : ∀ j, x j ∈ stdSimplex ℝ (A j))
    (i : ι) (μ : ProbabilityMeasure (A i)) (a : (j : ι) → A j) :
    (∏ j, ((Function.update
      (fun j ↦ ProbabilityMeasure.equivStdSimplex.symm ⟨x j, hx_mem j⟩) i μ) j
      {a j}).toReal) =
    (μ {a i}).toReal * ∏ j ∈ Finset.univ.filter (· ≠ i), x j (a j) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  refine congr_arg₂ (· * ·) (by simp [Function.update_self]) ?_
  rw [Finset.filter_ne']
  exact Finset.prod_congr rfl fun j hj ↦ by
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
    exact equivStdSimplex_symm_singleton_toReal (x j) (hx_mem j) (a j)

lemma payoff_deviation_eq (x : (i : ι) → A i → ℝ)
    (hx_mem : ∀ j, x j ∈ stdSimplex ℝ (A j))
    (i : ι) (μ : ProbabilityMeasure (A i)) :
    P.toExpected.payoff i (G.toMixed.outcome
      (Function.update (fun j ↦ ProbabilityMeasure.equivStdSimplex.symm ⟨x j, hx_mem j⟩) i μ)) =
    ∑ s : A i, (μ {s}).toReal * expectedPayoffPure G P x i s := by
  rw [payoff_as_weighted_sum]
  simp_rw [prod_update_eq x hx_mem i μ, expectedPayoffPure, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ ↦ by
    simp_rw [mul_ite, mul_zero, ← mul_assoc]
    rw [Fintype.sum_ite_eq]

lemma nash_from_simplex_le (x : (i : ι) → A i → ℝ)
    (hx : x ∈ Set.univ.pi (fun i ↦ stdSimplex ℝ (A i)))
    (hle : ∀ i (s : A i), expectedPayoffPure G P x i s ≤ expectedPayoffMixed G P x i) :
    G.toMixed.IsNashEquilibrium P.toExpected
      (fun j ↦ ProbabilityMeasure.equivStdSimplex.symm ⟨x j, Set.mem_univ_pi.mp hx j⟩) := by
  intro i μ
  rw [payoff_deviation_eq G P x (Set.mem_univ_pi.mp hx) i μ,
    payoff_baseline_eq G P x (Set.mem_univ_pi.mp hx) i]
  calc ∑ s, (μ {s}).toReal * expectedPayoffPure G P x i s
      ≤ ∑ s, (μ {s}).toReal * expectedPayoffMixed G P x i :=
        Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left (hle i s) ENNReal.toReal_nonneg
    _ = expectedPayoffMixed G P x i := by
        simp_rw [← Finset.sum_mul, ← μ.measureReal_eq_coe_coeFn, sum_measureReal_singleton]
        simp

end NashExistence

@[expose] public section

variable {ι : Type*} {A : ι → Type*} {O : Type*}

lemma Game.exists_isNashEquilibrium_of_finite (G : Game A O) (P : PayoffStructure O ι)
    [∀ i, MeasurableSpace (A i)] [MeasurableSpace O]
    [∀ i, DiscreteMeasurableSpace (A i)] [DiscreteMeasurableSpace O] [G.Measurable]
    [Fintype ι] [DecidableEq ι] [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] :
    ∃ a, G.toMixed.IsNashEquilibrium P.toExpected a := by
  obtain ⟨⟨x, hx⟩, hfixed⟩ := Continuous.exists_fixedPt_of_isConvex_isCompact
    (isCompact_univ_pi fun i ↦ isCompact_stdSimplex (A i))
    (convex_pi fun i _ ↦ convex_stdSimplex ℝ (A i))
    (Set.univ_pi_nonempty_iff.mpr fun i ↦
      ⟨_, (stdSimplex.instNonemptyElemForall (S := ℝ) (X := A i)).some.2⟩)
    ((bestResponseMap_continuousOn G P).mapsToRestrict (bestResponseMap_mapsTo G P))
  have hfixed' : bestResponseMap G P x = x := by
    simpa [Set.MapsTo.restrict] using congr_arg Subtype.val hfixed
  exact ⟨_, nash_from_simplex_le G P x hx fun i s ↦ by
    have h := fixedPoint_gains_zero G P x hx hfixed' i s
    simp only [gain, max_eq_left_iff] at h
    linarith⟩

end

end GameTheory
