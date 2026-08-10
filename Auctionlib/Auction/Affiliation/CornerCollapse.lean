module

public import Auctionlib.Auction.Affiliation.CondValue
public import Auctionlib.Auction.Affiliation.Symmetry
public import Mathlib

/-! # The symmetric collapse of the corner conditional value

## Main results

* `Auction.Affiliation.comp_perm_mem_maxAt_iff` :
  `z ∘ σ ∈ maxAt i j ↔ z ∈ maxAt (σ i) (σ j)`.
* `Auction.Affiliation.topDensity_comp_perm` : for `f` invariant under precomposition with
  `σ`, `topDensity f i j (z ∘ σ) = topDensity f (σ i) (σ j) z`.
* `Auction.Affiliation.otherRivals_map_swap_perm` :
  `((otherRivals i j').map (Equiv.swap j j')).Perm (otherRivals i j)` for `j ≠ i`, `j' ≠ i`.
* `Auction.Affiliation.IsSymmetricModel.cornerNumer_eq`,
  `Auction.Affiliation.IsSymmetricModel.cornerDenom_eq` : under `IsSymmetricModel E`, the
  corner numerator and denominator are independent of the designated rival index,
  `cornerNumer μ E i j' x y = cornerNumer μ E i j x y` and likewise for `cornerDenom`.
* `Auction.Affiliation.IsSymmetricModel.w_eq`,
  `Auction.Affiliation.IsSymmetricModel.bidII_eq` : the corner conditional value `w` and its
  diagonal `bidII` are independent of the designated rival index.
* `Auction.Affiliation.sumNumer`, `Auction.Affiliation.sumDenom` : the corners summed over
  all rivals of `i`.
* `Auction.Affiliation.IsSymmetricModel.sumNumer_eq`,
  `Auction.Affiliation.IsSymmetricModel.sumDenom_eq` : under `IsSymmetricModel E`, each sum
  is `n − 1` times the corner at any designated rival.
* `Auction.Affiliation.IsSymmetricModel.sumNumer_div_sumDenom` : under `IsSymmetricModel E`,
  `sumNumer μ E i x y / sumDenom μ E i x y = w μ E i j x y` at any rival `j ≠ i`.

The collapse: under `IsSymmetricModel E` the value family is equivariant and the signal
density is exchangeable, so relabelling the bidders by the transposition `Equiv.swap j j'`
(which fixes `i`) carries the corner at rival `j'` to the corner at rival `j`. Hence
`cornerNumer`, `cornerDenom`, `w` and `bidII` do not depend on which rival index is
designated, and the `n − 1` corners of the joint density of `(Xᵢ, maxₖ≠ᵢ Xₖ)` are all equal.

`sumNumer`/`sumDenom` are the corners summed over every rival `j ≠ i`. They upgrade the
reading of `w` from "one corner of the joint density of `(Xᵢ, maxₖ≠ᵢ Xₖ)`" to "the full
rival-symmetric ratio": the sum runs over the `n − 1` rivals, and under `IsSymmetricModel E`
each corner is equal, so `sumNumer / sumDenom = w` at any designated rival, by the exact and
unconditional `mul_div_mul_left` identity — no positivity of `cornerDenom` is needed and the
identity holds off the signal box as well.

The corners overlap: `maxAt i j ∩ maxAt i j'` contains every profile in which rivals `j` and
`j'` tie at the rival maximum, so `sumDenom` is the multiplicity-weighted corner mass, each
profile counted once per rival attaining the maximum. It is therefore *not* literally the
density of `(Xᵢ, Y)` with `Y = maxₖ≠ᵢ Xₖ`: with an atomic `μ` the overcount is genuine. Under
an atomless `μ` each pairwise overlap forces `z_m = y` at a marginalized coordinate `m`, whose
one-dimensional integral vanishes, so the overlap contributes nothing to any iterated marginal
and `sumDenom` coincides with the `(Xᵢ, Y)`-density reading; but the library has no
`(Xᵢ, Y)`-density object (no `MeasureTheory.condExp`, no disintegration kernel, as in
`Auction.Affiliation.CondExpGeneral`), so this is an interpretive caveat, not a theorem.
`sumNumer / sumDenom` is stated as the exact ratio identity: numerator and denominator
overcount the same tie sets with the same weights, so the ratio is the natural
argmax-multiplicity-weighted conditional value even with atoms, and under symmetry it equals
`w`. The residual gap to `E[Vᵢ | Xᵢ = x, Y = y]` is (a) reading iterated marginals as
densities and (b) the measure-zero-ties convention, licensed when `μ` has no atoms and not
formalized here; no theorem here identifies `sumNumer / sumDenom` with that conditional
expectation.
-/

@[expose] public section

open MeasureTheory

namespace Auction.Affiliation

/-! ### Relabelling the corner index -/

/-- `z ∘ σ ∈ maxAt i j ↔ z ∈ maxAt (σ i) (σ j)`: precomposition by a permutation `σ`
translates the `maxAt` corner along `σ`. -/
theorem comp_perm_mem_maxAt_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) (i j : Fin n)
    (z : Fin n → ℝ) : z ∘ σ ∈ maxAt i j ↔ z ∈ maxAt (σ i) (σ j) := by
  simp only [mem_maxAt_iff, Function.comp_apply]
  constructor
  · intro h m hmi hmj
    have hk := h (σ.symm m)
      (fun hc => hmi (by rw [← hc, Equiv.apply_symm_apply]))
      (fun hc => hmj (by rw [← hc, Equiv.apply_symm_apply]))
    rwa [Equiv.apply_symm_apply] at hk
  · intro h k hki hkj
    exact h (σ k) (fun hc => hki (σ.injective hc)) (fun hc => hkj (σ.injective hc))

/-- For `f` invariant under precomposition with `σ`,
`topDensity f i j (z ∘ σ) = topDensity f (σ i) (σ j) z`. -/
theorem topDensity_comp_perm {n : ℕ} {f : (Fin n → ℝ) → ℝ} (σ : Equiv.Perm (Fin n))
    (hf : ∀ X : Fin n → ℝ, f (X ∘ σ) = f X) (i j : Fin n) (z : Fin n → ℝ) :
    topDensity f i j (z ∘ σ) = topDensity f (σ i) (σ j) z := by
  by_cases hz : z ∘ σ ∈ maxAt i j
  · have hz' : z ∈ maxAt (σ i) (σ j) := (comp_perm_mem_maxAt_iff σ i j z).1 hz
    rw [topDensity_of_mem f i j hz, topDensity_of_mem f (σ i) (σ j) hz', hf]
  · have hz' : z ∉ maxAt (σ i) (σ j) :=
      fun hc => hz ((comp_perm_mem_maxAt_iff σ i j z).2 hc)
    rw [topDensity_of_notMem f i j hz, topDensity_of_notMem f (σ i) (σ j) hz']

/-- The corner list at `j'`, reindexed by the transposition `Equiv.swap j j'`, is a
permutation of the corner list at `j`. -/
theorem otherRivals_map_swap_perm {n : ℕ} {i j j' : Fin n} (hj : j ≠ i) (hj' : j' ≠ i) :
    ((otherRivals i j').map (Equiv.swap j j' : Fin n → Fin n)).Perm (otherRivals i j) := by
  refine List.perm_of_nodup_nodup_toFinset_eq
    (((nodup_rivals i).sublist
        (show List.Sublist ((rivals i).erase j') (rivals i) from List.erase_sublist)).map
      (Equiv.swap j j').injective)
    ((nodup_rivals i).sublist
      (show List.Sublist ((rivals i).erase j) (rivals i) from List.erase_sublist)) ?_
  ext k
  simp only [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [mem_otherRivals_iff] at ha
    obtain ⟨hai, haj'⟩ := ha
    rw [mem_otherRivals_iff]
    refine ⟨fun hc => hai ((Equiv.swap j j').injective
        (hc.trans (Equiv.swap_apply_of_ne_of_ne (Ne.symm hj) (Ne.symm hj')).symm)),
      fun hc => haj' ((Equiv.swap j j').injective
        (hc.trans (Equiv.swap_apply_right j j').symm))⟩
  · intro hk
    rw [mem_otherRivals_iff] at hk
    obtain ⟨hki, hkj⟩ := hk
    refine ⟨Equiv.swap j j' k, ?_, Equiv.swap_apply_self j j' k⟩
    rw [mem_otherRivals_iff]
    exact ⟨fun hc => hki ((Equiv.swap j j').injective
        (hc.trans (Equiv.swap_apply_of_ne_of_ne (Ne.symm hj) (Ne.symm hj')).symm)),
      fun hc => hkj ((Equiv.swap j j').injective
        (hc.trans (Equiv.swap_apply_left j j').symm))⟩

/-! ### The rival-index collapse -/

/-- Under `IsSymmetricModel E`, the corner numerator is independent of the designated rival
index: `cornerNumer μ E i j' x y = cornerNumer μ E i j x y` for any two rivals `j`, `j'` of
`i`. Only integrability at the single reference rival `j` is required. -/
theorem IsSymmetricModel.cornerNumer_eq {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]
    {E : SignalValueEnv n} (hE : IsSymmetricModel E) {i j j' : Fin n}
    (hj : j ≠ i) (hj' : j' ≠ i) (x y : ℝ)
    (hnum : PermFibreIntegrable μ
      (fun z => E.v i (Function.update (Function.update z i x) j y)
        * topDensity E.f i j (Function.update (Function.update z i x) j y))
      (otherRivals i j)) :
    cornerNumer μ E i j' x y = cornerNumer μ E i j x y := by
  set σ : Equiv.Perm (Fin n) := Equiv.swap j j' with hσdef
  have hσi : σ i = i := by
    rw [hσdef]; exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hj) (Ne.symm hj')
  have hσj : σ j = j' := by rw [hσdef]; exact Equiv.swap_apply_left j j'
  have hσj' : σ j' = j := by rw [hσdef]; exact Equiv.swap_apply_right j j'
  have hσsymm : σ.symm = σ := by rw [hσdef]; exact Equiv.symm_swap j j'
  have hstep : ∀ z : Fin n → ℝ,
      Function.update (Function.update (z ∘ σ) i x) j y
        = Function.update (Function.update z i x) j' y ∘ σ := by
    intro z
    rw [update_comp_perm σ (Function.update z i x) j' y, update_comp_perm σ z i x, hσsymm,
      hσi, hσj']
  have hpt : ∀ z : Fin n → ℝ,
      (fun z' => E.v i (Function.update (Function.update z' i x) j y)
          * topDensity E.f i j (Function.update (Function.update z' i x) j y)) (z ∘ σ)
        = E.v i (Function.update (Function.update z i x) j' y)
          * topDensity E.f i j' (Function.update (Function.update z i x) j' y) := by
    intro z
    show E.v i (Function.update (Function.update (z ∘ σ) i x) j y)
        * topDensity E.f i j (Function.update (Function.update (z ∘ σ) i x) j y) = _
    rw [hstep z, hE.1.rival_symm i hσi (Function.update (Function.update z i x) j' y),
      topDensity_comp_perm σ (hE.2 σ) i j, hσi, hσj]
  have hfun : (fun z => E.v i (Function.update (Function.update z i x) j' y)
        * topDensity E.f i j' (Function.update (Function.update z i x) j' y))
      = fun z => (fun z' => E.v i (Function.update (Function.update z' i x) j y)
          * topDensity E.f i j (Function.update (Function.update z' i x) j y)) (z ∘ σ) :=
    funext fun z => (hpt z).symm
  simp only [cornerNumer]
  rw [hfun, marginalList_comp_perm μ σ (otherRivals i j')
      (fun z' => E.v i (Function.update (Function.update z' i x) j y)
        * topDensity E.f i j (Function.update (Function.update z' i x) j y)) 0,
    hσsymm]
  have h0 : (0 : Fin n → ℝ) ∘ σ = 0 := by funext m; rfl
  rw [h0, hσdef]
  exact marginalList_perm (otherRivals_map_swap_perm hj hj')
    (hnum.of_perm (otherRivals_map_swap_perm hj hj').symm) 0

/-- Under `IsSymmetricModel E`, the corner denominator is independent of the designated
rival index: `cornerDenom μ E i j' x y = cornerDenom μ E i j x y`. Only integrability at the
single reference rival `j` is required. -/
theorem IsSymmetricModel.cornerDenom_eq {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]
    {E : SignalValueEnv n} (hE : IsSymmetricModel E) {i j j' : Fin n}
    (hj : j ≠ i) (hj' : j' ≠ i) (x y : ℝ)
    (hden : PermFibreIntegrable μ
      (fun z => topDensity E.f i j (Function.update (Function.update z i x) j y))
      (otherRivals i j)) :
    cornerDenom μ E i j' x y = cornerDenom μ E i j x y := by
  set σ : Equiv.Perm (Fin n) := Equiv.swap j j' with hσdef
  have hσi : σ i = i := by
    rw [hσdef]; exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hj) (Ne.symm hj')
  have hσj : σ j = j' := by rw [hσdef]; exact Equiv.swap_apply_left j j'
  have hσj' : σ j' = j := by rw [hσdef]; exact Equiv.swap_apply_right j j'
  have hσsymm : σ.symm = σ := by rw [hσdef]; exact Equiv.symm_swap j j'
  have hstep : ∀ z : Fin n → ℝ,
      Function.update (Function.update (z ∘ σ) i x) j y
        = Function.update (Function.update z i x) j' y ∘ σ := by
    intro z
    rw [update_comp_perm σ (Function.update z i x) j' y, update_comp_perm σ z i x, hσsymm,
      hσi, hσj']
  have hpt : ∀ z : Fin n → ℝ,
      (fun z' => topDensity E.f i j (Function.update (Function.update z' i x) j y)) (z ∘ σ)
        = topDensity E.f i j' (Function.update (Function.update z i x) j' y) := by
    intro z
    show topDensity E.f i j (Function.update (Function.update (z ∘ σ) i x) j y) = _
    rw [hstep z, topDensity_comp_perm σ (hE.2 σ) i j, hσi, hσj]
  have hfun : (fun z => topDensity E.f i j' (Function.update (Function.update z i x) j' y))
      = fun z => (fun z' => topDensity E.f i j
          (Function.update (Function.update z' i x) j y)) (z ∘ σ) :=
    funext fun z => (hpt z).symm
  simp only [cornerDenom]
  rw [hfun, marginalList_comp_perm μ σ (otherRivals i j')
      (fun z' => topDensity E.f i j (Function.update (Function.update z' i x) j y)) 0,
    hσsymm]
  have h0 : (0 : Fin n → ℝ) ∘ σ = 0 := by funext m; rfl
  rw [h0, hσdef]
  exact marginalList_perm (otherRivals_map_swap_perm hj hj')
    (hden.of_perm (otherRivals_map_swap_perm hj hj').symm) 0

/-- Under `IsSymmetricModel E`, the corner conditional value `w` is independent of the
designated rival index: `w μ E i j' x y = w μ E i j x y`. -/
theorem IsSymmetricModel.w_eq {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]
    {E : SignalValueEnv n} (hE : IsSymmetricModel E) {i j j' : Fin n}
    (hj : j ≠ i) (hj' : j' ≠ i) (x y : ℝ)
    (hnum : PermFibreIntegrable μ
      (fun z => E.v i (Function.update (Function.update z i x) j y)
        * topDensity E.f i j (Function.update (Function.update z i x) j y))
      (otherRivals i j))
    (hden : PermFibreIntegrable μ
      (fun z => topDensity E.f i j (Function.update (Function.update z i x) j y))
      (otherRivals i j)) :
    w μ E i j' x y = w μ E i j x y := by
  simp only [w, hE.cornerNumer_eq hj hj' x y hnum, hE.cornerDenom_eq hj hj' x y hden]

/-- Under `IsSymmetricModel E`, the diagonal corner conditional value `bidII` is independent
of the designated rival index: `bidII μ E i j' x = bidII μ E i j x`. -/
theorem IsSymmetricModel.bidII_eq {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]
    {E : SignalValueEnv n} (hE : IsSymmetricModel E) {i j j' : Fin n}
    (hj : j ≠ i) (hj' : j' ≠ i) (x : ℝ)
    (hnum : PermFibreIntegrable μ
      (fun z => E.v i (Function.update (Function.update z i x) j x)
        * topDensity E.f i j (Function.update (Function.update z i x) j x))
      (otherRivals i j))
    (hden : PermFibreIntegrable μ
      (fun z => topDensity E.f i j (Function.update (Function.update z i x) j x))
      (otherRivals i j)) :
    bidII μ E i j' x = bidII μ E i j x := by
  simp only [bidII, hE.w_eq hj hj' x x hnum hden]

/-! ### The rival-symmetric sums -/

/-- `sumNumer μ E i x y = ∑ j ∈ Finset.univ.erase i, cornerNumer μ E i j x y`: the corner
numerator summed over all rivals of `i`. -/
noncomputable def sumNumer {n : ℕ} (μ : Measure ℝ) (E : SignalValueEnv n) (i : Fin n)
    (x y : ℝ) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, cornerNumer μ E i j x y

/-- `sumDenom μ E i x y = ∑ j ∈ Finset.univ.erase i, cornerDenom μ E i j x y`: the corner
denominator summed over all rivals of `i`. It is the multiplicity-weighted corner mass —
each profile is counted once per rival attaining the rival maximum, so at a tie
`maxAt i j ∩ maxAt i j'` the profile is counted more than once. Under an atomless `μ` the
overlap is `μ`-null in every iterated marginal and `sumDenom` reads as the density of
`(Xᵢ, maxₖ≠ᵢ Xₖ)`; with atoms it strictly overcounts. This is an interpretive caveat: the
library has no density-of-`(Xᵢ, Y)` object, and no theorem here identifies `sumNumer /
sumDenom` with `E[Vᵢ | Xᵢ = x, Y = y]`. -/
noncomputable def sumDenom {n : ℕ} (μ : Measure ℝ) (E : SignalValueEnv n) (i : Fin n)
    (x y : ℝ) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, cornerDenom μ E i j x y

/-- Under `IsSymmetricModel E`, the rival-summed numerator is `n − 1` times the corner at
any single designated rival `j ≠ i`. -/
theorem IsSymmetricModel.sumNumer_eq {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]
    {E : SignalValueEnv n} (hE : IsSymmetricModel E) {i j : Fin n} (hj : j ≠ i)
    (x y : ℝ)
    (hnum : PermFibreIntegrable μ
      (fun z => E.v i (Function.update (Function.update z i x) j y)
        * topDensity E.f i j (Function.update (Function.update z i x) j y))
      (otherRivals i j)) :
    sumNumer μ E i x y = ((n - 1 : ℕ) : ℝ) * cornerNumer μ E i j x y := by
  rw [sumNumer, Finset.sum_congr rfl (fun j' hj' =>
    hE.cornerNumer_eq hj (Finset.mem_erase.1 hj').1 x y hnum),
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-- Under `IsSymmetricModel E`, the rival-summed denominator is `n − 1` times the corner at
any single designated rival `j ≠ i`. -/
theorem IsSymmetricModel.sumDenom_eq {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]
    {E : SignalValueEnv n} (hE : IsSymmetricModel E) {i j : Fin n} (hj : j ≠ i)
    (x y : ℝ)
    (hden : PermFibreIntegrable μ
      (fun z => topDensity E.f i j (Function.update (Function.update z i x) j y))
      (otherRivals i j)) :
    sumDenom μ E i x y = ((n - 1 : ℕ) : ℝ) * cornerDenom μ E i j x y := by
  rw [sumDenom, Finset.sum_congr rfl (fun j' hj' =>
    hE.cornerDenom_eq hj (Finset.mem_erase.1 hj').1 x y hden),
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-- **The faithful bridge.** Under `IsSymmetricModel E`, the rival-symmetric ratio equals
the corner conditional value `w` at any designated rival `j ≠ i`:
`sumNumer μ E i x y / sumDenom μ E i x y = w μ E i j x y`.

This is the exact and unconditional ratio identity. The common factor `n − 1` cancels by
`mul_div_mul_left`, which holds in `ℝ` even where `cornerDenom μ E i j x y = 0` (both sides
are then `0`), so no positivity of the denominator is assumed and the identity holds off the
signal box as well. The numerator and denominator overcount the same tie sets with the same
weights, so the ratio is the argmax-multiplicity-weighted conditional value even under an
atomic `μ`; under symmetry it equals `w`. It is *not* claimed to equal
`E[Vᵢ | Xᵢ = x, Y = y]`: that identification needs (a) reading iterated marginals as
densities and (b) the measure-zero-ties convention (an atomless `μ`), neither formalized
here. -/
theorem IsSymmetricModel.sumNumer_div_sumDenom {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]
    {E : SignalValueEnv n} (hE : IsSymmetricModel E) {i j : Fin n} (hj : j ≠ i)
    (x y : ℝ)
    (hnum : PermFibreIntegrable μ
      (fun z => E.v i (Function.update (Function.update z i x) j y)
        * topDensity E.f i j (Function.update (Function.update z i x) j y))
      (otherRivals i j))
    (hden : PermFibreIntegrable μ
      (fun z => topDensity E.f i j (Function.update (Function.update z i x) j y))
      (otherRivals i j)) :
    sumNumer μ E i x y / sumDenom μ E i x y = w μ E i j x y := by
  have hnt : Nontrivial (Fin n) := ⟨⟨j, i, hj⟩⟩
  have h1n : 1 < n := by
    have := Fintype.one_lt_card_iff_nontrivial.2 hnt
    simpa using this
  have hn1 : ((n - 1 : ℕ) : ℝ) ≠ 0 := by
    have : n - 1 ≠ 0 := by omega
    exact_mod_cast this
  rw [hE.sumNumer_eq hj x y hnum, hE.sumDenom_eq hj x y hden, w,
    mul_div_mul_left _ _ hn1]

end Auction.Affiliation

end
