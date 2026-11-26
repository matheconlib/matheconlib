/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
import MathEconLib

/-!
# Encoded best responses through the public import

Pin the product representation at its original order assumptions and apply its strategic
bridge to membership of arbitrary encoded profiles.
-/

namespace MathEconLibTest.GameTheory.BestResponseEncoding

open MathEconLib.GameTheory

variable {ι : Type*} {A : ι → Type*} {O V : Type*} {E : ι → Type*}
  [DecidableEq ι] [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (E i)]
  [TopologicalSpace O] {k : (i : ι) → Set (E i)} (e : ∀ i, A i ≃ₜ k i)
  (G : OutcomeGame ι A O) (P : PayoffStructure ι O V) (x : ↑(Set.univ.pi k))

example [LE V] :
    bestResponseCorr e G P x = Set.univ.pi (fun i ↦
      (fun s : A i ↦ ((e i) s : E i)) '' {s : A i | ∀ t : A i,
        P.payoff i (G.outcome (Function.update (decode e x) i t)) ≤
          P.payoff i (G.outcome (Function.update (decode e x) i s))}) :=
  bestResponseCorr_eq_pi e G P x

example [Preorder V] :
    bestResponseCorr e G P x = Set.univ.pi (fun i ↦
      (fun s : A i ↦ ((e i) s : E i)) ''
        (StrategicGame.ofOutcome G P).bestResponses i (decode e x)) :=
  bestResponseCorr_eq_pi_bestResponses e G P x

example [Preorder V] (a : ∀ i, A i) :
    encode e a ∈ bestResponseCorr e G P x ↔
      ∀ i, a i ∈ (StrategicGame.ofOutcome G P).bestResponses i (decode e x) := by
  rw [bestResponseCorr_eq_pi_bestResponses]
  simp only [Set.mem_univ_pi, Set.mem_image]
  constructor
  · intro h i
    obtain ⟨s, hs, hsa⟩ := h i
    have h : s = a i := (e i).injective (Subtype.ext hsa)
    exact h ▸ hs
  · intro h i
    exact ⟨a i, h i, rfl⟩

#print axioms bestResponseCorr_eq_pi_bestResponses

end MathEconLibTest.GameTheory.BestResponseEncoding
