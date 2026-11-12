/-
Copyright (c) 2026 Victor H. Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor H. Aguiar
-/
module

public import MathEconLib.ForMathlib.LogicalCompactness
public import MathEconLib.RevealedPreference.RenyFinite
public import MathEconLib.RevealedPreference.RenyNormalization
public import MathEconLib.RevealedPreference.RenyStrictness
public import MathEconLib.RevealedPreference.RenyWeights
public import Mathlib.Topology.Order.Compact

/-!
# Infinite-data Afriat rationalization

This proves Theorem 1 of Philip J. Reny (2015), *A Characterization of Rationalizable
Consumer Behavior*, Econometrica 83(1), 175--192, DOI: 10.3982/ECTA12345,
with the prescribed-gap compactness architecture of Yannai A. Gonczarowski,
Scott Duke Kominers and Ran I. Shorrer (2025), *To infinity and beyond:
A general framework for scaling economic theories*, Theoretical Economics
20(2), 511--542, DOI: 10.3982/TE5878, Theorem 8.
The compact space consists of ordinary real-valued utilities in a unit cube;
no nonstandard-real representation or continuity conclusion is used.
The proof adapts the source argument using finite scalar utility threshold steps,
rather than formalizing its encoded propositional utility syntax. This module
covers the consumer-rationalization application, not all applications in that paper.
Utility is represented on all real bundles, with its economic requirements restricted
to the nonnegative orthant; values outside that orthant are immaterial.

## References and Lean provenance

Ported from Victor H. Aguiar's Apache-2.0 Lean development
[WGARP Lean](https://github.com/vaguiarl/wgarp-lean), module `InfiniteAfriat`.
-/

@[expose] public section

set_option autoImplicit false

namespace MathEconLib.RevealedPreference

open scoped BigOperators

variable {L : ℕ} {T : Type*}

/-- The nonnegative commodity orthant is convex. -/
private theorem convex_nonnegative_bundles (L : ℕ) :
    Convex ℝ {x : Bundle L | Nonnegative x} :=
  convex_Ici (0 : Bundle L)

namespace InfiniteAfriat

/-- Every coordinate of this cube is an ordinary real interval. -/
abbrev UtilityCube (L : ℕ) := Bundle L → Set.Icc (0 : ℝ) 1

def cubeUtility (v : UtilityCube L) : Utility L := fun x => (v x : ℝ)

/-- Closed requirements on a utility; mathematical side conditions are fixed
parameters, not restrictions on the topology of the utility cube. -/
inductive Constraint (L : ℕ) (T : Type*) where
  | budget (t : T) (y : Bundle L)
  | monotone (x y : Bundle L)
  | quasiconcave (x y : Bundle L) (a b : ℝ)
  | gap (r : RationalStrongPair L)

def Satisfies (p q : T → Bundle L) (w : RationalStrongPair L → ℝ)
    (c : Constraint L T) (v : UtilityCube L) : Prop :=
  match c with
  | .budget t y => Nonnegative y → dot (p t) y ≤ dot (p t) (q t) →
      cubeUtility v y ≤ cubeUtility v (q t)
  | .monotone x y => Nonnegative x → Nonnegative y → x ≤ y →
      cubeUtility v x ≤ cubeUtility v y
  | .quasiconcave x y a b => Nonnegative x → Nonnegative y →
      0 ≤ a → 0 ≤ b → a + b = 1 →
      min (cubeUtility v x) (cubeUtility v y) ≤ cubeUtility v (a • x + b • y)
  | .gap r => cubeUtility v r.lower + w r ≤ cubeUtility v r.upper

private theorem continuous_cubeUtility (x : Bundle L) :
    Continuous (fun v : UtilityCube L => cubeUtility v x) :=
  continuous_subtype_val.comp (continuous_apply x)

private theorem satisfies_isClosed (p q : T → Bundle L) (w : RationalStrongPair L → ℝ)
    (c : Constraint L T) : IsClosed {v | Satisfies p q w c v} := by
  cases c with
  | budget t y =>
      simp only [Satisfies, Set.ofPred_forall]
      exact isClosed_iInter fun _ => isClosed_iInter fun _ =>
        isClosed_le (continuous_cubeUtility y) (continuous_cubeUtility (q t))
  | monotone x y =>
      simp only [Satisfies, Set.ofPred_forall]
      exact isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
        isClosed_le (continuous_cubeUtility x) (continuous_cubeUtility y)
  | quasiconcave x y a b =>
      simp only [Satisfies, Set.ofPred_forall]
      exact isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
        isClosed_iInter fun _ => isClosed_iInter fun _ =>
          isClosed_le ((continuous_cubeUtility x).min (continuous_cubeUtility y))
            (continuous_cubeUtility (a • x + b • y))
  | gap r =>
      exact isClosed_le ((continuous_cubeUtility r.lower).add continuous_const)
        (continuous_cubeUtility r.upper)

/-- Observation indices mentioned by a finite collection of requirements. -/
private noncomputable def observedSupport
    (s : Finset (Constraint L T)) : Finset T := by
  classical
  exact s.biUnion fun c => match c with
    | .budget t _ => {t}
    | _ => ∅

/-- Rational margins mentioned by a finite collection of requirements. -/
private noncomputable def gapSupport
    (s : Finset (Constraint L T)) : Finset (RationalStrongPair L) := by
  classical
  exact s.biUnion fun c => match c with
    | .gap r => {r}
    | _ => ∅

private theorem budget_mem_observedSupport (s : Finset (Constraint L T)) (t : T) (y : Bundle L)
    (h : Constraint.budget t y ∈ s) : t ∈ observedSupport s := by
  classical
  exact Finset.mem_biUnion.mpr ⟨.budget t y, h, Finset.mem_singleton_self t⟩

private theorem gap_mem_gapSupport (s : Finset (Constraint L T)) (r : RationalStrongPair L)
    (h : Constraint.gap r ∈ s) : r ∈ gapSupport s := by
  classical
  exact Finset.mem_biUnion.mpr ⟨.gap r, h, Finset.mem_singleton_self r⟩

/-- Bounded normalization of a finite Afriat utility. Outside the commodity
orthant its value is immaterial, and is set to zero. -/
private noncomputable def normalizedCube (U : Utility L)
    (hmono : MonotoneOn U {x | Nonnegative x})
    (K : Finset (RationalStrongPair L)) (w : RationalStrongPair L → ℝ)
    (hw : ∀ r, 0 ≤ w r) (hsum : ∑ r ∈ K, w r ≤ 1 / 2) : UtilityCube L := by
  classical
  intro x
  exact if hx : Nonnegative x then
    ⟨renyFiniteTransform K w (fun r => U r.upper) (U 0) (U x),
      renyFiniteTransform_nonneg K w _ _ (fun r _ => hw r)
        (hmono (fun _ => le_rfl) hx hx),
      (renyFiniteTransform_lt_one K w _ _ (fun r _ => hw r) hsum
        (hmono (fun _ => le_rfl) hx hx)).le⟩
    else ⟨0, le_rfl, zero_le_one⟩

private theorem cubeUtility_normalizedCube (U : Utility L)
    (hmono : MonotoneOn U {x | Nonnegative x})
    (K : Finset (RationalStrongPair L)) (w : RationalStrongPair L → ℝ)
    (hw : ∀ r, 0 ≤ w r) (hsum : ∑ r ∈ K, w r ≤ 1 / 2)
    (x : Bundle L) (hx : Nonnegative x) :
    cubeUtility (normalizedCube U hmono K w hw hsum) x =
      renyFiniteTransform K w (fun r => U r.upper) (U 0) (U x) := by
  simp [cubeUtility, normalizedCube, hx]

private theorem finite_constraints_satisfiable (hL : 0 < L) (p q : T → Bundle L)
    (hp : RenyPriceAdmissible p) (hq : RenyChoiceAdmissible q)
    (hg : GraphGARP p q) (w : RationalStrongPair L → ℝ)
    (hw : ∀ r, 0 ≤ w r) (hsum : ∀ K : Finset (RationalStrongPair L),
      ∑ r ∈ K, w r ≤ 1 / 2) (s : Finset (Constraint L T)) :
    ∃ v : UtilityCube L, ∀ c ∈ s, Satisfies p q w c v := by
  classical
  let F := observedSupport s
  let K := gapSupport s
  obtain ⟨U, _hcont, hconc, hmono, hstrict, hrat⟩ :=
    hasFiniteRegularRenyRationalization_of_graphGARP hL (fun t : F => p t) (fun t : F => q t)
      (fun t => hp t) (graphGARP_reindex p q (fun t : F => (t : T)) hg)
  let v := normalizedCube U hmono K w hw (hsum K)
  have heval (x : Bundle L) (hx : Nonnegative x) :
      cubeUtility v x = renyFiniteTransform K w (fun r => U r.upper) (U 0) (U x) :=
    cubeUtility_normalizedCube U hmono K w hw (hsum K) x hx
  have hanchor (x : Bundle L) (hx : Nonnegative x) : U 0 ≤ U x :=
    hmono (fun _ => le_rfl) hx hx
  refine ⟨v, ?_⟩
  intro c hc
  cases c with
  | budget t y =>
      intro hy hb
      rw [heval y hy, heval (q t) (hq t)]
      exact renyFiniteTransform_preserves_le K w _ _ U (fun r _ => hw r)
        (hanchor y hy) (hanchor (q t) (hq t))
        ((hrat ⟨t, budget_mem_observedSupport s t y hc⟩ y hy).1 hb)
  | monotone x y =>
      intro hx hy hxy
      rw [heval x hx, heval y hy]
      exact renyFiniteTransform_preserves_le K w _ _ U (fun r _ => hw r)
        (hanchor x hx) (hanchor y hy) (hmono hx hy hxy)
  | quasiconcave x y a b =>
      intro hx hy ha hb hab
      have hz := convex_nonnegative_bundles L hx hy ha hb hab
      rw [heval x hx, heval y hy, heval (a • x + b • y) hz]
      exact renyFiniteTransform_preserves_min_le K w _ _ U (fun r _ => hw r)
        (hanchor x hx) (hanchor y hy) (hanchor _ hz)
        ((quasiconcaveOn_iff_min_le.mp hconc.quasiconcaveOn).2
          (Set.mem_univ x) (Set.mem_univ y) ha hb hab)
  | gap r =>
      change cubeUtility v r.lower + w r ≤ cubeUtility v r.upper
      rw [heval r.lower r.lower_nonnegative, heval r.upper r.upper_nonnegative]
      exact renyFiniteTransform_gap K w _ _ (fun r _ => hw r)
        (gap_mem_gapSupport s r hc) (hanchor r.lower r.lower_nonnegative)
        (hstrict r.lower r.upper r.lower_nonnegative r.upper_nonnegative r.lower_lt_upper)

/-- One positive margin schedule is chosen for the full rational-pair
family BEFORE quantifying over finite constraint subfamilies. Every finite
witness satisfies those same prescribed margins. The schedule may vary
across rational pairs; it may not be reselected or shrunk with `s`.

This packages an invariant already present in `finite_constraints_satisfiable`
and makes the quantifier order visible to callers of the compactness step. -/
theorem exists_fixed_margins_and_finite_witnesses
    (hL : 0 < L) (p q : T → Bundle L)
    (hp : RenyPriceAdmissible p) (hq : RenyChoiceAdmissible q)
    (hg : GraphGARP p q) :
    ∃ w : RationalStrongPair L → ℝ,
      (∀ r, 0 < w r) ∧
      (∀ K : Finset (RationalStrongPair L), ∑ r ∈ K, w r ≤ 1 / 2) ∧
      ∀ s : Finset (Constraint L T),
        ∃ v : UtilityCube L, ∀ c ∈ s, Satisfies p q w c v := by
  obtain ⟨w, hw, hsum⟩ := exists_rationalStrongPair_margins L
  exact ⟨w, hw, hsum,
    finite_constraints_satisfiable hL p q hp hq hg w (fun r => (hw r).le) hsum⟩

/-- Read the economic properties back from the closed constraint system. -/
private theorem regular_rationalization_of_satisfying_constraints (p q : T → Bundle L)
    (hp : RenyPriceAdmissible p) (w : RationalStrongPair L → ℝ)
    (hw : ∀ r, 0 < w r) (v : UtilityCube L)
    (hv : ∀ c : Constraint L T, Satisfies p q w c v) :
    MonotoneOn (cubeUtility v) {x | Nonnegative x} ∧
    QuasiconcaveOn ℝ {x | Nonnegative x} (cubeUtility v) ∧
    SemiStrictlyIncreasingOnNonnegative (cubeUtility v) ∧
    RenyRationalizes p q (cubeUtility v) := by
  have hmono : MonotoneOn (cubeUtility v) {x | Nonnegative x} := by
    intro x hx y hy hxy
    exact hv (.monotone x y) hx hy hxy
  have hquasi : QuasiconcaveOn ℝ {x | Nonnegative x} (cubeUtility v) := by
    apply quasiconcaveOn_iff_min_le.mpr
    refine ⟨convex_nonnegative_bundles L, ?_⟩
    intro x hx y hy a b ha hb hab
    exact hv (.quasiconcave x y a b) hx hy ha hb hab
  have hstrict : SemiStrictlyIncreasingOnNonnegative (cubeUtility v) :=
    semiStrict_of_rationalStrongPair_margins (cubeUtility v) hmono w hw
      (fun r => hv (.gap r))
  refine ⟨hmono, hquasi, hstrict, ?_⟩
  exact renyRationalizes_of_weak_of_semiStrict p q (cubeUtility v) hp
    (fun t y hy hb => hv (.budget t y) hy hb) hstrict

end InfiniteAfriat

/-- Reny's infinite-data regularity: nondecreasing, quasiconcave and strictly
increasing when every coordinate increases. Continuity, concavity and unique
maximization are deliberately not part of this conclusion. -/
def HasRegularRenyRationalization (p q : T → Bundle L) : Prop :=
  ∃ u : Utility L,
    MonotoneOn u {x | Nonnegative x} ∧
    QuasiconcaveOn ℝ {x | Nonnegative x} u ∧
    SemiStrictlyIncreasingOnNonnegative u ∧ RenyRationalizes p q u

/-- Finite regular rationalization entails the regularity required by the
infinite-data theorem, without any assumption on the observation type. -/
theorem finiteRegularRenyRationalization_implies_regularRenyRationalization
    (p q : T → Bundle L) (h : HasFiniteRegularRenyRationalization p q) :
    HasRegularRenyRationalization p q := by
  obtain ⟨u, _hcontinuous, hconcave, hmono, hsemi, hrat⟩ := h
  refine ⟨u, hmono, ?_, hsemi, hrat⟩
  exact Convex.quasiconcaveOn_restrict hconcave.quasiconcaveOn
    (Set.subset_univ _) (convex_nonnegative_bundles L)

/-- Reny's infinite-data sufficiency theorem, with arbitrary observation
cardinality. The proof uses fixed positive gaps and standard-real compactness
as in the logical-compactness approach of Gonczarowski--Kominers--Shorrer. -/
theorem hasRegularRenyRationalization_of_graphGARP
    (hL : 0 < L) (p q : T → Bundle L)
    (hp : RenyPriceAdmissible p) (hq : RenyChoiceAdmissible q)
    (hg : GraphGARP p q) : HasRegularRenyRationalization p q := by
  obtain ⟨w, hw, _hsum, hfinite⟩ :=
    InfiniteAfriat.exists_fixed_margins_and_finite_witnesses hL p q hp hq hg
  obtain ⟨v, hv⟩ := LogicalCompactness.exists_satisfying_closed_constraints
    (InfiniteAfriat.Satisfies p q w) (InfiniteAfriat.satisfies_isClosed p q w) hfinite
  exact ⟨InfiniteAfriat.cubeUtility v,
    InfiniteAfriat.regular_rationalization_of_satisfying_constraints p q hp w hw v hv⟩

/-- Infinite Afriat/Reny: GARP is equivalent to regular Reny rationalization.
There are finitely many goods but no finiteness/countability assumption on
observations, and empty datasets, free goods and zero income are allowed. -/
theorem graphGARP_iff_hasRegularRenyRationalization
    (hL : 0 < L) (p q : T → Bundle L)
    (hp : RenyPriceAdmissible p) (hq : RenyChoiceAdmissible q) :
    GraphGARP p q ↔ HasRegularRenyRationalization p q := by
  constructor
  · exact hasRegularRenyRationalization_of_graphGARP hL p q hp hq
  · rintro ⟨u, _hmono, _hquasi, _hstrict, hrat⟩
    exact graphGARP_of_renyRationalizes p q u hq hrat

/-- All three clauses of Reny's characterization, with ordinary
rationalizability understood in his strict-affordability convention. -/
theorem infinite_reny_characterization
    (hL : 0 < L) (p q : T → Bundle L)
    (hp : RenyPriceAdmissible p) (hq : RenyChoiceAdmissible q) :
    ((∃ u : Utility L, RenyRationalizes p q u) ↔ GraphGARP p q) ∧
    (GraphGARP p q ↔ HasRegularRenyRationalization p q) := by
  refine ⟨⟨?_, ?_⟩, graphGARP_iff_hasRegularRenyRationalization hL p q hp hq⟩
  · rintro ⟨u, hu⟩
    exact graphGARP_of_renyRationalizes p q u hq hu
  · intro hg
    obtain ⟨u, _hmono, _hquasi, _hstrict, hrat⟩ :=
      hasRegularRenyRationalization_of_graphGARP hL p q hp hq hg
    exact ⟨u, hrat⟩

end MathEconLib.RevealedPreference
