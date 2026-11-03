/-
Copyright (c) 2026 Ben Eltschig, Ruiz Chen, Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig, Ruiz Chen, Daniel Lyng
-/
module

public import MathEconLib.ForMathlib.Quasiconvex
public import MathEconLib.GameTheory.Strategic.Mixed.Finite
import MathEconLib.ForMathlib.ApproximateSelection
import MathEconLib.ForMathlib.Kakutani
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Existence of Nash equilibria

Continuous games with linearly ordered payoffs and finitely many players on compact convex action
sets have pure equilibria when the payoff order is closed and each own-action payoff is
quasiconcave. The action sets may be represented by homeomorphisms into locally convex spaces.
Continuous games on compact metrizable spaces and finite games also admit mixed equilibria with
real-valued payoffs.

## Main statements

* `OutcomeGame.exists_isNash_of_quasiconcaveOn` and `StrategicGame.exists_isNash_of_quasiconcaveOn`
  give pure equilibrium existence.
* `OutcomeGame.exists_isNash_of_isCompact` and `StrategicGame.exists_isMixedNash_of_isCompact` give
  mixed equilibrium existence for compact metrizable action spaces.
* `OutcomeGame.exists_isNash_of_finite`, `StrategicGame.exists_isMixedNash_of_finite`, and
  `StrategicGame.exists_isFiniteMixedNash` give mixed equilibrium existence for finite games.

## Tags

nash equilibrium, mixed strategies, quasiconcavity, fixed points
-/

open MeasureTheory ProbabilityMeasure

namespace MathEconLib.GameTheory

variable {ι : Type*} {A : ι → Type*} {O : Type*} {V : Type*}

section Helpers

/-! ## Strategy profiles and product spaces -/

/-- Each representing action set is compact when the corresponding action space is compact. -/
lemma isCompact_ki {ι : Type*} {A : ι → Type*} {E : ι → Type*}
    [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)]
    [∀ i, TopologicalSpace (E i)]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i) (i : ι) :
    IsCompact (k i) := by
  rw [show k i = Set.range (Subtype.val ∘ (e i)) from Set.ext fun x =>
    ⟨fun hx => ⟨(e i).symm ⟨x, hx⟩, by simp⟩, fun ⟨a, ha⟩ => ha ▸ (e i a).property⟩]
  exact isCompact_range (continuous_subtype_val.comp (e i).continuous)

/-- Each representing action set is nonempty when the corresponding action space is nonempty. -/
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

/-- An encoded strategy profile belongs to the product of the representing action sets. -/
lemma encode_mem {ι : Type*} {A : ι → Type*} {E : ι → Type*}
    [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (E i)]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i)
    (a : (i : ι) → A i) : encode e a ∈ Set.univ.pi k :=
  fun i _ => ((e i) (a i)).property

/-! ## Best response correspondence -/

/-- The best response correspondence maps a point in the product space to the set of strategy
profiles where each player plays a best response. -/
noncomputable def bestResponseCorr {ι : Type*} {A : ι → Type*} {O : Type*} {E : ι → Type*}
    [DecidableEq ι] [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (E i)]
    [TopologicalSpace O]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i)
    [LE V]
    (G : OutcomeGame ι A O) (P : PayoffStructure ι O V) :
    ↑(Set.univ.pi k) → Set ((i : ι) → E i) :=
  fun x =>
    let a := decode e x
    { y | ∃ (hy : ∀ i, y i ∈ k i),
      ∀ i (s : A i), P.payoff i (G.outcome (Function.update a i s)) ≤
        P.payoff i (G.outcome (Function.update a i ((e i).symm ⟨y i, hy i⟩))) }

/-- Every best response profile belongs to the product of the representing action sets. -/
lemma bestResponseCorr_subset {ι : Type*} {A : ι → Type*} {O : Type*} {E : ι → Type*}
    [DecidableEq ι] [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (E i)]
    [TopologicalSpace O]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i)
    [LE V]
    (G : OutcomeGame ι A O) (P : PayoffStructure ι O V)
    (x : ↑(Set.univ.pi k)) :
    bestResponseCorr e G P x ⊆ Set.univ.pi k := fun _ ⟨hyk, _⟩ i _ => hyk i

/-- A player’s payoff is continuous in their own action when opponents’ actions are fixed. -/
lemma payoff_update_continuous {ι : Type*} {A : ι → Type*} {O : Type*}
    [DecidableEq ι] [∀ i, TopologicalSpace (A i)] [TopologicalSpace O]
    [TopologicalSpace V]
    (G : OutcomeGame ι A O) (P : PayoffStructure ι O V)
    [G.Continuous] [P.Continuous]
    (a : (i : ι) → A i) (i : ι) :
    Continuous (fun s => P.payoff i (G.outcome (Function.update a i s))) :=
  (PayoffStructure.continuous_payoff i).comp <|
    (OutcomeGame.continuous_outcome (G := G)).comp (continuous_const.update i continuous_id)

/-- Each player has a payoff-maximizing action against any fixed profile of opponents’ actions. -/
lemma exists_payoff_maximizer {ι : Type*} {A : ι → Type*} {O : Type*}
    [DecidableEq ι] [∀ i, TopologicalSpace (A i)] [TopologicalSpace O]
    [LinearOrder V] [TopologicalSpace V] [ClosedIciTopology V]
    (G : OutcomeGame ι A O) (P : PayoffStructure ι O V)
    [G.Continuous] [P.Continuous]
    [∀ i, CompactSpace (A i)] [∀ i, Nonempty (A i)]
    (a : (i : ι) → A i) (i : ι) :
    ∃ s_i : A i, ∀ s : A i,
      P.payoff i (G.outcome (Function.update a i s)) ≤
        P.payoff i (G.outcome (Function.update a i s_i)) :=
  let ⟨x, _, hx⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    (payoff_update_continuous G P a i).continuousOn
  ⟨x, fun s => hx (Set.mem_univ s)⟩

/-- Decoding an encoded action recovers the original action. -/
lemma decode_encode_component {ι : Type*} {A : ι → Type*} {E : ι → Type*}
    [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (E i)]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i)
    (maximizers : (i : ι) → A i) (i : ι)
    (hy : ∀ j, encode e maximizers j ∈ k j) :
    (e i).symm ⟨encode e maximizers i, hy i⟩ = maximizers i :=
  (congrArg (e i).symm (Subtype.ext rfl)).trans ((e i).symm_apply_apply (maximizers i))

/-- The best response correspondence has nonempty values on nonempty compact action spaces. -/
lemma bestResponseCorr_nonempty {ι : Type*} {A : ι → Type*} {O : Type*} {E : ι → Type*}
    [Finite ι] [DecidableEq ι]
    [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)] [∀ i, Nonempty (A i)]
    [∀ i, TopologicalSpace (E i)]
    [TopologicalSpace O]
    [LinearOrder V] [TopologicalSpace V] [ClosedIciTopology V]
    (G : OutcomeGame ι A O) (P : PayoffStructure ι O V)
    [G.Continuous] [P.Continuous]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i)
    (x : ↑(Set.univ.pi k)) :
    (bestResponseCorr e G P x).Nonempty := by
  choose maximizers hmax using fun i => exists_payoff_maximizer G P (decode e x) i
  have hencode_mem : ∀ i, encode e maximizers i ∈ k i :=
    fun i => encode_mem e maximizers i (Set.mem_univ i)
  exact ⟨encode e maximizers, hencode_mem, fun i s =>
    (decode_encode_component e maximizers i hencode_mem) ▸ hmax i s⟩

/-- The extended payoff agrees with the original payoff on the representing action set. -/
lemma extend_eq_payoff {ι : Type*} {A : ι → Type*} {O : Type*} {E : ι → Type*}
    [DecidableEq ι] [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (E i)]
    [TopologicalSpace O]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i)
    (G : OutcomeGame ι A O) (P : PayoffStructure ι O V)
    (a : (i : ι) → A i) (i : ι) {d : E i → V} (z : E i) (hz : z ∈ k i) :
    Subtype.val.extend
      ((fun s ↦ P.payoff i (G.outcome (Function.update a i s))) ∘ (e i).symm) d z =
    P.payoff i (G.outcome (Function.update a i ((e i).symm ⟨z, hz⟩))) := by
  simpa using Subtype.val_injective.extend_apply
    ((fun s ↦ P.payoff i (G.outcome (Function.update a i s))) ∘ (e i).symm) d ⟨z, hz⟩

/-- Quasiconcave own-action payoffs give convex values of the best response correspondence. -/
lemma bestResponseCorr_convex {ι : Type*} {A : ι → Type*} {O : Type*} {E : ι → Type*}
    [Finite ι] [DecidableEq ι]
    [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)] [∀ i, Nonempty (A i)]
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)] [∀ i, TopologicalSpace (E i)]
    [TopologicalSpace O]
    [LE V]
    (G : OutcomeGame ι A O) (P : PayoffStructure ι O V)
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i)
    (hs : ∀ i, Convex ℝ (k i))
    (h_quasiconcave : ∀ a i, QuasiconcaveOn ℝ (k i) <| Subtype.val.extend
      ((fun s ↦ P.payoff i (G.outcome (Function.update a i s))) ∘ (e i).symm)
      (fun _ => P.payoff i (G.outcome a)))
    (x : ↑(Set.univ.pi k)) :
    Convex ℝ (bestResponseCorr e G P x) := by
  have hpayoff_le_extend : ∀ y, y ∈ bestResponseCorr e G P x → ∀ i (s : A i),
      P.payoff i (G.outcome (Function.update (decode e x) i s)) ≤ Subtype.val.extend
        ((fun s ↦ P.payoff i (G.outcome (Function.update (decode e x) i s))) ∘ (e i).symm)
        (fun _ => P.payoff i (G.outcome (decode e x))) (y i) := fun _ ⟨hyk, hbr⟩ i s => by
    rw [extend_eq_payoff e G P (decode e x) i _ (hyk i)]
    exact hbr i s
  intro y₁ hy₁ y₂ hy₂ a b ha hb hab
  refine ⟨fun i => (hs i) (hy₁.1 i) (hy₂.1 i) ha hb hab, fun i s => ?_⟩
  have hpayoff_le_combination := ((h_quasiconcave (decode e x) i)
    (P.payoff i (G.outcome (Function.update (decode e x) i s)))
    ⟨hy₁.1 i, hpayoff_le_extend y₁ hy₁ i s⟩ ⟨hy₂.1 i, hpayoff_le_extend y₂ hy₂ i s⟩ ha hb hab).2
  rwa [extend_eq_payoff] at hpayoff_le_combination

/-- A player’s best responses form a compact set when the action space is compact. -/
lemma bestResponse_isCompact {ι : Type*} {A : ι → Type*} {O : Type*}
    [DecidableEq ι]
    [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)]
    [TopologicalSpace O]
    [Preorder V] [TopologicalSpace V] [OrderClosedTopology V]
    (G : OutcomeGame ι A O) (P : PayoffStructure ι O V)
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

/-- The best response correspondence is the product of the players’ encoded best response sets. -/
lemma bestResponseCorr_eq_pi {ι : Type*} {A : ι → Type*} {O : Type*} {E : ι → Type*}
    [DecidableEq ι] [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (E i)]
    [TopologicalSpace O]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i)
    [LE V]
    (G : OutcomeGame ι A O) (P : PayoffStructure ι O V)
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

/-- The best response correspondence has compact values on compact action spaces. -/
lemma bestResponseCorr_compact {ι : Type*} {A : ι → Type*} {O : Type*} {E : ι → Type*}
    [Finite ι] [DecidableEq ι]
    [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)] [∀ i, Nonempty (A i)]
    [∀ i, TopologicalSpace (E i)]
    [TopologicalSpace O]
    [Preorder V] [TopologicalSpace V] [OrderClosedTopology V]
    (G : OutcomeGame ι A O) (P : PayoffStructure ι O V)
    [G.Continuous] [P.Continuous]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i)
    (x : ↑(Set.univ.pi k)) :
    IsCompact (bestResponseCorr e G P x) := by
  rw [bestResponseCorr_eq_pi]
  exact isCompact_univ_pi fun i =>
    (bestResponse_isCompact G P (decode e x) i).image (continuous_subtype_val.comp (e i).continuous)

/-- Decoding is continuous from the product of representing action sets to strategy profiles. -/
lemma continuous_decode {ι : Type*} {A : ι → Type*} {E : ι → Type*}
    [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (E i)]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i) :
    Continuous (decode e) :=
  continuous_pi fun i => (e i).symm.continuous.comp
    (Continuous.subtype_mk ((continuous_apply i).comp continuous_subtype_val) _)

/-- The pairs of profiles satisfying a fixed unilateral-deviation payoff inequality form a closed
set. -/
lemma isClosed_payoff_le {ι : Type*} {A : ι → Type*} {O : Type*} {E : ι → Type*}
    [Finite ι] [DecidableEq ι]
    [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)] [∀ i, Nonempty (A i)]
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)] [∀ i, TopologicalSpace (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul ℝ (E i)]
    [∀ i, T2Space (E i)] [∀ i, LocallyConvexSpace ℝ (E i)]
    [TopologicalSpace O]
    [Preorder V] [TopologicalSpace V] [OrderClosedTopology V]
    (G : OutcomeGame ι A O) (P : PayoffStructure ι O V)
    [G.Continuous] [P.Continuous]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i) (i : ι) (s : A i) :
    IsClosed {p : ↑(Set.univ.pi k) × ↑(Set.univ.pi k) |
      P.payoff i (G.outcome (Function.update (decode e p.1) i s)) ≤
        P.payoff i (G.outcome (Function.update (decode e p.1) i (decode e p.2 i)))} :=
  let hcd := continuous_decode e
  isClosed_le
    ((PayoffStructure.continuous_payoff i).comp (OutcomeGame.continuous_outcome.comp
      (Continuous.update (hcd.comp continuous_fst) i continuous_const)))
    ((PayoffStructure.continuous_payoff i).comp (OutcomeGame.continuous_outcome.comp
      (Continuous.update (hcd.comp continuous_fst) i
        ((continuous_apply i).comp (hcd.comp continuous_snd)))))

/-- The best response graph is the intersection of all unilateral-deviation payoff inequalities. -/
lemma graph_eq_iInter {ι : Type*} {A : ι → Type*} {O : Type*} {E : ι → Type*}
    [Finite ι] [DecidableEq ι]
    [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)] [∀ i, Nonempty (A i)]
    [∀ i, TopologicalSpace (E i)] [TopologicalSpace O]
    [LE V]
    (G : OutcomeGame ι A O) (P : PayoffStructure ι O V)
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i) :
    {p : ↑(Set.univ.pi k) × ↑(Set.univ.pi k) | p.2.val ∈ bestResponseCorr e G P p.1} =
      ⋂ i, ⋂ s, {p : ↑(Set.univ.pi k) × ↑(Set.univ.pi k) |
        P.payoff i (G.outcome (Function.update (decode e p.1) i s)) ≤
          P.payoff i (G.outcome (Function.update (decode e p.1) i (decode e p.2 i)))} := by
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  exact ⟨fun ⟨_, h⟩ => h, fun hp => ⟨fun i => p.2.property i (Set.mem_univ i), hp⟩⟩

/-- The best response correspondence has a closed graph for continuous payoffs. -/
lemma bestResponseCorr_isClosed_graph {ι : Type*} {A : ι → Type*} {O : Type*} {E : ι → Type*}
    [Finite ι] [DecidableEq ι]
    [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)] [∀ i, Nonempty (A i)]
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)] [∀ i, TopologicalSpace (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul ℝ (E i)]
    [∀ i, T2Space (E i)] [∀ i, LocallyConvexSpace ℝ (E i)]
    [TopologicalSpace O]
    [Preorder V] [TopologicalSpace V] [OrderClosedTopology V]
    (G : OutcomeGame ι A O) (P : PayoffStructure ι O V)
    [G.Continuous] [P.Continuous]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i) :
    IsClosed {p : ↑(Set.univ.pi k) × ((i : ι) → E i) | p.2 ∈ bestResponseCorr e G P p.1} := by
  have hk_compact := fun i => isCompact_ki e i
  rw [show {p : ↑(Set.univ.pi k) × ((i : ι) → E i) | p.2 ∈ bestResponseCorr e G P p.1} =
    (Prod.map id Subtype.val) ''
      {p : ↑(Set.univ.pi k) × ↑(Set.univ.pi k) | p.2.val ∈ bestResponseCorr e G P p.1} from by
    ext ⟨x, y⟩
    simp only [Set.mem_ofPred_eq, Set.mem_image, Prod.exists, Prod.map]
    exact ⟨fun hy => ⟨x, ⟨y, bestResponseCorr_subset e G P x hy⟩, hy, rfl⟩,
      fun ⟨_, _, hb, heq⟩ => by
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        exact hb⟩]
  exact (IsProperMap.prodMap isProperMap_id
    (isClosed_set_pi fun i _ => (hk_compact i).isClosed).isProperMap_subtypeVal).isClosedMap _ <| by
    rw [graph_eq_iInter G P e]
    exact isClosed_iInter fun i => isClosed_iInter fun s => isClosed_payoff_le G P e i s

/-! ## Upper hemicontinuity -/

/-- Failure of a correspondence to lie in a set is the projection of its graph outside that set. -/
private lemma uhc_compl_eq_fst_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {F : X → Set Y} {V : Set Y} :
    {x : X | F x ⊆ V}ᶜ = Prod.fst '' ({p : X × Y | p.2 ∈ F p.1} ∩ (Set.univ ×ˢ Vᶜ)) := by
  ext x
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_image, Set.mem_inter_iff,
    Set.mem_prod, Set.mem_univ, true_and]
  exact ⟨fun hx => by
      rw [Set.not_subset] at hx
      obtain ⟨y, hy_mem, hy_not⟩ := hx
      exact ⟨(x, y), ⟨hy_mem, Set.mem_compl hy_not⟩, rfl⟩,
    fun ⟨⟨_, b⟩, ⟨hb_mem, hb_compl⟩, rfl⟩ h => hb_compl (h hb_mem)⟩

/-- A correspondence into compact action sets is upper hemicontinuous when its graph is closed. -/
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
  have hproduct_compact := isCompact_univ_pi hk
  have hcompactSpace : CompactSpace ↑(Set.univ.pi k) :=
    isCompact_iff_compactSpace.mp hproduct_compact
  exact (((isCompact_univ.prod hproduct_compact).of_isClosed_subset
    (hF_closed.inter (IsClosed.prod isClosed_univ hV.isClosed_compl))
    (fun p hp => ⟨Set.mem_univ _, hF_sub p.1 hp.1⟩)).image continuous_fst).isClosed

/-- The best response correspondence is upper hemicontinuous for continuous payoffs on compact
spaces. -/
lemma bestResponseCorr_uhc {ι : Type*} {A : ι → Type*} {O : Type*} {E : ι → Type*}
    [Finite ι] [DecidableEq ι]
    [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)] [∀ i, Nonempty (A i)]
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)] [∀ i, TopologicalSpace (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul ℝ (E i)]
    [∀ i, T2Space (E i)] [∀ i, LocallyConvexSpace ℝ (E i)]
    [TopologicalSpace O]
    [Preorder V] [TopologicalSpace V] [OrderClosedTopology V]
    (G : OutcomeGame ι A O) (P : PayoffStructure ι O V)
    [G.Continuous] [P.Continuous]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i) :
    UpperHemicontinuous (bestResponseCorr e G P) :=
  uhc_of_closedGraph_compact (fun i => isCompact_ki e i)
    (fun x => bestResponseCorr_subset e G P x)
    (bestResponseCorr_isClosed_graph G P e)

/-! ## Fixed point to Nash equilibrium -/

/-- A fixed point of the best response correspondence yields a Nash equilibrium. -/
lemma fixed_point_is_nash {ι : Type*} {A : ι → Type*} {O : Type*} {E : ι → Type*}
    [Finite ι] [DecidableEq ι]
    [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)] [∀ i, Nonempty (A i)]
    [∀ i, TopologicalSpace (E i)] [TopologicalSpace O]
    [LE V]
    (G : OutcomeGame ι A O) (P : PayoffStructure ι O V)
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i)
    (x : ↑(Set.univ.pi k))
    (hfp : x.val ∈ bestResponseCorr e G P x) :
    (StrategicGame.ofOutcome G P).IsNash (decode e x) := by
  obtain ⟨hy, hfp⟩ := hfp
  rw [StrategicGame.isNash_iff]
  intro i s
  have hdeviation_payoff_le := hfp i s
  rwa [show (e i).symm ⟨x.val i, hy i⟩ = decode e x i from by simp [decode],
    Function.update_eq_self] at hdeviation_payoff_le

end Helpers

/-- A continuous game with finitely many players and nonempty compact convex action sets admits a
pure Nash equilibrium when payoffs take values in a linearly ordered space with closed order and
each own-action payoff is quasiconcave. Action spaces may be represented by homeomorphisms into
locally convex real vector spaces. The extension uses the incumbent payoff outside each action set;
`quasiconcaveOn_subtype_val_extend_iff` makes the quasiconcavity hypothesis independent of these
outside values, so the payoff space need not have a zero. -/
public theorem OutcomeGame.exists_isNash_of_quasiconcaveOn
    [LinearOrder V] [TopologicalSpace V] [OrderClosedTopology V]
    (G : OutcomeGame ι A O) (P : PayoffStructure ι O V)
    [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)] [∀ i, Nonempty (A i)]
    [TopologicalSpace O] [G.Continuous] [P.Continuous]
    [Finite ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)] [∀ i, TopologicalSpace (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul ℝ (E i)] [∀ i, T2Space (E i)]
    [∀ i, LocallyConvexSpace ℝ (E i)]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i) (hs : ∀ i, Convex ℝ (k i))
    (h_quasiconcave : ∀ a i, QuasiconcaveOn ℝ (k i) <| Subtype.val.extend
      ((fun s ↦ P.payoff i (G.outcome (Function.update a i s))) ∘ (e i).symm)
      (fun _ => P.payoff i (G.outcome a))) :
    ∃ a, (StrategicGame.ofOutcome G P).IsNash a := by
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

/-- The homeomorphism from probability measures onto their image in the weak dual. -/
noncomputable def toWeakDualContinuousMap_homeomorph {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [BorelSpace α] [CompactSpace α] [TopologicalSpace.MetrizableSpace α] :
    ProbabilityMeasure α ≃ₜ Set.range (toWeakDualContinuousMap (α := α)) :=
  toWeakDualContinuousMap_isClosedEmbedding.toHomeomorph

/-- The expected payoff for player `i` with mixed strategy `μ` equals a weak dual evaluation
`(toWeakDualContinuousMap μ)(φ)` for an appropriate `φ : C(A i, ℝ)`. -/
lemma payoff_eq_eval_weakDual {ι : Type*} {A : ι → Type*} {O : Type*}
    (G : OutcomeGame ι A O) (P : PayoffStructure ι O ℝ) [Fintype ι] [DecidableEq ι]
    [∀ i, TopologicalSpace (A i)] [TopologicalSpace O]
    [∀ i, CompactSpace (A i)] [∀ i, TopologicalSpace.MetrizableSpace (A i)] [∀ i, Nonempty (A i)]
    [∀ i, MeasurableSpace (A i)] [MeasurableSpace O] [∀ i, BorelSpace (A i)] [BorelSpace O]
    [G.Continuous] [P.Continuous] [G.Measurable] [G.mixed.Continuous] [P.expected.Continuous]
    (a : (i : ι) → ProbabilityMeasure (A i)) (i : ι) :
    ∀ μ : ProbabilityMeasure (A i),
      P.expected.payoff i (G.mixed.outcome (Function.update a i μ)) =
        toWeakDualContinuousMap μ
          ⟨(fun μ ↦ P.expected.payoff i (G.mixed.outcome (Function.update a i μ))) ∘ diracProba,
            (PayoffStructure.continuous_payoff i).comp <| OutcomeGame.continuous_outcome.comp <|
              continuous_const.update _ continuous_diracProba⟩ := by
  intro μ
  dsimp [toWeakDualContinuousMap]
  change _ = integral _ _
  dsimp [PayoffStructure.expected]
  rw [OutcomeGame.mixed_outcome, ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_pi,
    integral_map G.measurable_outcome.aemeasurable (P.measurable_payoff i).aestronglyMeasurable,
    ← Measure.pi_map_piSplitAt i, integral_map (MeasurableEquiv.measurable _).aemeasurable
      (by exact ((P.measurable_payoff i).comp G.measurable_outcome).aestronglyMeasurable),
    Function.update_self, integral_prod]
  · congr 1
    ext x
    change _ = ∫ o, P.payoff i o ∂(G.mixed.outcome (Function.update a i (diracProba x))).toMeasure
    rw [OutcomeGame.mixed_outcome, ProbabilityMeasure.toMeasure_map,
      ProbabilityMeasure.toMeasure_pi,
      integral_map G.measurable_outcome.aemeasurable (P.measurable_payoff i).aestronglyMeasurable,
      ← Measure.pi_map_piSplitAt i, integral_map (MeasurableEquiv.measurable _).aemeasurable
        (by exact ((P.measurable_payoff i).comp G.measurable_outcome).aestronglyMeasurable),
      Function.update_self, integral_prod,
      show (diracProba x).toMeasure = Measure.dirac x from rfl, integral_dirac]
    · grind
    · exact ((P.continuous_payoff i).comp <|
        G.continuous_outcome.comp (Homeomorph.piSplitAt i _).continuous_invFun).integrable
  · exact ((P.continuous_payoff i).comp <|
      G.continuous_outcome.comp (Homeomorph.piSplitAt i _).continuous_invFun).integrable

/-- The `Function.extend` of the payoff via `Subtype.val` agrees with the weak dual evaluation on
the range of `toWeakDualContinuousMap`. -/
lemma extend_payoff_eq_eval {ι : Type*} {A : ι → Type*} {O : Type*}
    (G : OutcomeGame ι A O) (P : PayoffStructure ι O ℝ) [Fintype ι] [DecidableEq ι]
    [∀ i, TopologicalSpace (A i)] [TopologicalSpace O]
    [∀ i, CompactSpace (A i)] [∀ i, TopologicalSpace.MetrizableSpace (A i)] [∀ i, Nonempty (A i)]
    [∀ i, MeasurableSpace (A i)] [MeasurableSpace O] [∀ i, BorelSpace (A i)] [BorelSpace O]
    [G.Continuous] [P.Continuous] [G.Measurable] [G.mixed.Continuous] [P.expected.Continuous]
    (a : (i : ι) → ProbabilityMeasure (A i)) (i : ι) :
    let φ : C(A i, ℝ) := ⟨(fun μ ↦ P.expected.payoff i (G.mixed.outcome
      (Function.update a i μ))) ∘ diracProba,
      (PayoffStructure.continuous_payoff i).comp <| OutcomeGame.continuous_outcome.comp <|
        continuous_const.update _ continuous_diracProba⟩
    ∀ v ∈ Set.range (toWeakDualContinuousMap (α := A i)), (Subtype.val.extend
      ((fun s ↦ P.expected.payoff i (G.mixed.outcome (Function.update a i s))) ∘
        toWeakDualContinuousMap_homeomorph.symm)
        (fun _ => P.expected.payoff i (G.mixed.outcome a))) v = v φ := by
  intro φ v ⟨μ, hμ⟩
  subst hμ
  simp only [Function.comp_def]
  have hextend_payoff := Subtype.val_injective.extend_apply
    ((fun s ↦ P.expected.payoff i (G.mixed.outcome (Function.update a i s))) ∘
      toWeakDualContinuousMap_homeomorph.symm)
        (fun _ => P.expected.payoff i (G.mixed.outcome a)) ⟨toWeakDualContinuousMap μ, ⟨μ, rfl⟩⟩
  simp only [Function.comp_def] at hextend_payoff
  have hsymm : toWeakDualContinuousMap_homeomorph.symm ⟨toWeakDualContinuousMap μ, ⟨μ, rfl⟩⟩ = μ :=
    toWeakDualContinuousMap_injective <| congrArg Subtype.val <| by
      have happly_symm :=
        toWeakDualContinuousMap_homeomorph.apply_symm_apply ⟨_, ⟨μ, rfl⟩⟩
      simp only [toWeakDualContinuousMap_homeomorph, Topology.IsEmbedding.toHomeomorph]
        at happly_symm
      exact happly_symm
  rw [hextend_payoff, hsymm]
  exact payoff_eq_eval_weakDual G P a i μ

/-- The expected payoff, extended to the weak dual, is quasiconcave on the range of
`toWeakDualContinuousMap`. -/
lemma payoff_quasiconcave {ι : Type*} {A : ι → Type*} {O : Type*}
    (G : OutcomeGame ι A O) (P : PayoffStructure ι O ℝ) [Fintype ι] [DecidableEq ι]
    [∀ i, TopologicalSpace (A i)] [TopologicalSpace O]
    [∀ i, CompactSpace (A i)] [∀ i, TopologicalSpace.MetrizableSpace (A i)] [∀ i, Nonempty (A i)]
    [∀ i, MeasurableSpace (A i)] [MeasurableSpace O] [∀ i, BorelSpace (A i)] [BorelSpace O]
    [G.Continuous] [P.Continuous] [G.Measurable] [G.mixed.Continuous] [P.expected.Continuous]
    (a : (i : ι) → ProbabilityMeasure (A i)) (i : ι) :
    QuasiconcaveOn ℝ (Set.range (toWeakDualContinuousMap (α := A i)))
      (Subtype.val.extend
        ((fun s ↦ P.expected.payoff i (G.mixed.outcome (Function.update a i s))) ∘
          toWeakDualContinuousMap_homeomorph.symm)
        (fun _ => P.expected.payoff i (G.mixed.outcome a))) := by
  have hrange_convex := convex_range_toWeakDualContinuousMap (α := A i)
  have hextend_eq_eval := extend_payoff_eq_eval G P a i
  let φ : C(A i, ℝ) := ⟨(fun μ ↦ P.expected.payoff i (G.mixed.outcome
    (Function.update a i μ))) ∘ diracProba,
    (PayoffStructure.continuous_payoff i).comp <| OutcomeGame.continuous_outcome.comp <|
      continuous_const.update _ continuous_diracProba⟩
  exact ((((WeakBilin.eval (topDualPairing ℝ C(A i, ℝ)) φ).toLinearMap).concaveOn
    hrange_convex).congr
    (fun v hv ↦ (hextend_eq_eval v hv).symm)).quasiconcaveOn

end Helpers

/-- Any game with nonempty compact metrizable action spaces and continuous payoff functions admits
a mixed Nash equilibrium. -/
public theorem OutcomeGame.exists_isNash_of_isCompact {ι : Type*} {A : ι → Type*} {O : Type*}
    (G : OutcomeGame ι A O) (P : PayoffStructure ι O ℝ) [Fintype ι] [DecidableEq ι]
    [∀ i, TopologicalSpace (A i)] [TopologicalSpace O]
    [∀ i, CompactSpace (A i)] [∀ i, TopologicalSpace.MetrizableSpace (A i)] [∀ i, Nonempty (A i)]
    [∀ i, MeasurableSpace (A i)] [MeasurableSpace O] [∀ i, BorelSpace (A i)] [BorelSpace O]
    [G.Continuous] [P.Continuous] [P.expected.Continuous] :
    ∃ a, (StrategicGame.ofOutcome G.mixed P.expected).IsNash a := by
  have hnonempty_measure : ∀ i, Nonempty (ProbabilityMeasure (A i)) :=
    fun i ↦ ⟨diracProba (Classical.arbitrary _)⟩
  have hlocallyConvex : ∀ i, LocallyConvexSpace ℝ (WeakDual ℝ C(A i, ℝ)) :=
    fun _ ↦ WeakBilin.locallyConvexSpace
  exact G.mixed.exists_isNash_of_quasiconcaveOn P.expected
    (fun _ ↦ toWeakDualContinuousMap_homeomorph)
    (fun _ ↦ convex_range_toWeakDualContinuousMap)
    (fun a i ↦ payoff_quasiconcave G P a i)

/-- Any finite game (i.e. any game with finitely many players and finite action spaces) admits a
mixed Nash equilibrium. -/
public theorem OutcomeGame.exists_isNash_of_finite (G : OutcomeGame ι A O)
    (P : PayoffStructure ι O ℝ)
    [∀ i, MeasurableSpace (A i)] [MeasurableSpace O]
    [∀ i, DiscreteMeasurableSpace (A i)] [DiscreteMeasurableSpace O] [G.Measurable]
    [Fintype ι] [DecidableEq ι] [∀ i, Finite (A i)] [∀ i, Nonempty (A i)] [Finite O] :
    ∃ a, (StrategicGame.ofOutcome G.mixed P.expected).IsNash a := by
  let _ i : TopologicalSpace (A i) := ⊥
  let _ : TopologicalSpace O := ⊥
  have hdiscrete_action i : DiscreteTopology (A i) := ⟨rfl⟩
  have hdiscrete_outcome : DiscreteTopology O := ⟨rfl⟩
  have hcontinuous_outcome : G.Continuous := ⟨continuous_of_discreteTopology⟩
  have hcontinuous_payoff : P.Continuous := ⟨fun i ↦ continuous_of_discreteTopology⟩
  exact G.exists_isNash_of_isCompact P

@[expose] public section

namespace StrategicGame

/-- Compact convex action sets and continuous quasiconcave own-action payoffs in a linearly ordered
space with closed order admit a pure Nash equilibrium. The extension uses the incumbent payoff
outside each action set; `quasiconcaveOn_subtype_val_extend_iff` makes the quasiconcavity
hypothesis independent of these outside values, so the payoff space need not have a zero. -/
theorem exists_isNash_of_quasiconcaveOn (G : StrategicGame ι A V)
    [LinearOrder V] [TopologicalSpace V] [OrderClosedTopology V]
    [∀ i, TopologicalSpace (A i)] [∀ i, CompactSpace (A i)] [∀ i, Nonempty (A i)]
    [G.Continuous] [Finite ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)] [∀ i, TopologicalSpace (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul ℝ (E i)] [∀ i, T2Space (E i)]
    [∀ i, LocallyConvexSpace ℝ (E i)]
    {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i) (hs : ∀ i, Convex ℝ (k i))
    (h_quasiconcave : ∀ a i, QuasiconcaveOn ℝ (k i) <| Subtype.val.extend
      ((fun s ↦ G.payoff i (Function.update a i s)) ∘ (e i).symm) (fun _ => G.payoff i a)) :
    ∃ a, G.IsNash a := by
  exact G.outcomeGame.exists_isNash_of_quasiconcaveOn G.payoffStructure e hs h_quasiconcave

/-- Continuous payoffs on nonempty compact metrizable action spaces admit a mixed equilibrium. -/
theorem exists_isMixedNash_of_isCompact (G : StrategicGame ι A ℝ)
    [Fintype ι] [DecidableEq ι] [∀ i, TopologicalSpace (A i)]
    [∀ i, CompactSpace (A i)] [∀ i, TopologicalSpace.MetrizableSpace (A i)] [∀ i, Nonempty (A i)]
    [∀ i, MeasurableSpace (A i)] [∀ i, BorelSpace (A i)] [G.Continuous] :
    ∃ σ, G.IsMixedNash σ := by
  have hexists : ∃ σ, G.mixedExtension.IsNash σ := by
    rw [mixedExtension_eq_ofOutcome]
    exact G.outcomeGame.exists_isNash_of_isCompact G.payoffStructure
  obtain ⟨σ, hσ⟩ := hexists
  refine ⟨σ, (isMixedNash_iff_isNash_of_integrable G σ ?_).2 hσ⟩
  intro i τ
  exact (Continuous.continuous_payoff (G := G) i).integrable

/-- Every finite strategic game with nonempty discrete measurable action spaces has a mixed Nash
equilibrium. -/
theorem exists_isMixedNash_of_finite (G : StrategicGame ι A ℝ) [Fintype ι] [DecidableEq ι]
    [∀ i, Finite (A i)] [∀ i, Nonempty (A i)] [∀ i, MeasurableSpace (A i)]
    [∀ i, DiscreteMeasurableSpace (A i)] : ∃ σ, G.IsMixedNash σ := by
  have hexists : ∃ σ, G.mixedExtension.IsNash σ := by
    rw [mixedExtension_eq_ofOutcome]
    exact G.outcomeGame.exists_isNash_of_finite G.payoffStructure
  obtain ⟨σ, hσ⟩ := hexists
  refine ⟨σ, (isMixedNash_iff_isNash_of_integrable G σ ?_).2 hσ⟩
  intro i τ
  exact Integrable.of_finite

/-- Every finite strategic game with nonempty action spaces has an equilibrium in finite
probability weights. -/
theorem exists_isFiniteMixedNash (G : StrategicGame ι A ℝ) [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] : ∃ σ, G.IsFiniteMixedNash σ := by
  let _ i : MeasurableSpace (A i) := ⊤
  have hdiscrete_measurable i : DiscreteMeasurableSpace (A i) := ⟨fun _ ↦ trivial⟩
  obtain ⟨σ, hσ⟩ := G.exists_isMixedNash_of_finite
  refine ⟨toSimplex σ, (isFiniteMixedNash_iff_isMixedNash G _).2 ?_⟩
  rwa [toProbability_toSimplex]

end StrategicGame

end

end MathEconLib.GameTheory
