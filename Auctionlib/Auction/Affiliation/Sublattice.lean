module

public import Auctionlib.Auction.Affiliation.Basic
public import Auctionlib.ForMathlib.UpdateLattice
public import Mathlib

/-! # Affiliation of products, sublattice indicators, and the top-rival density

## Main results

* `Auction.Affiliation.Affiliated.mul` : `Affiliated f`, `Affiliated g`, `0 ≤ f` and
  `0 ≤ g` imply `Affiliated fun x => f x * g x`.
* `Auction.Affiliation.affiliated_indicator_of_isSublattice` : for `IsSublattice S`,
  `Affiliated (S.indicator 1)`.
* `Auction.Affiliation.indicator_one_nonneg` : `0 ≤ S.indicator 1`.
* `Auction.Affiliation.Affiliated.update_slice` : `Affiliated f` implies
  `Affiliated fun z => f (Function.update z k c)`.
* `Auction.Affiliation.maxAt` : `maxAt i j = {z | ∀ k, k ≠ i → k ≠ j → z k ≤ z j}`, with
  `Auction.Affiliation.mem_maxAt_iff`.
* `Auction.Affiliation.isSublattice_maxAt` : `IsSublattice (maxAt i j)`.
* `Auction.Affiliation.topDensity` :
  `topDensity f i j = fun z => f z * (maxAt i j).indicator 1 z`.
* `Auction.Affiliation.topDensity_nonneg` : `0 ≤ f` implies `0 ≤ topDensity f i j`.
* `Auction.Affiliation.topDensity_of_mem`, `Auction.Affiliation.topDensity_of_notMem` :
  `topDensity f i j z = f z` for `z ∈ maxAt i j` and `topDensity f i j z = 0` otherwise.
* `Auction.Affiliation.affiliated_topDensity` : `Affiliated f` and `0 ≤ f` imply
  `Affiliated (topDensity f i j)`.
-/

@[expose] public section

namespace Auction.Affiliation

/-- `Affiliated f`, `Affiliated g`, `0 ≤ f` and `0 ≤ g` imply
`Affiliated fun x => f x * g x`. -/
theorem Affiliated.mul {n : ℕ} {f g : (Fin n → ℝ) → ℝ} (hf : Affiliated f)
    (hg : Affiliated g) (hf0 : 0 ≤ f) (hg0 : 0 ≤ g) :
    Affiliated fun x => f x * g x := by
  intro x y
  have key : f x * f y * (g x * g y)
      ≤ f (x ⊔ y) * f (x ⊓ y) * (g (x ⊔ y) * g (x ⊓ y)) :=
    mul_le_mul (hf x y) (hg x y) (mul_nonneg (hg0 x) (hg0 y))
      (mul_nonneg (hf0 _) (hf0 _))
  calc f x * g x * (f y * g y) = f x * f y * (g x * g y) := by ring
    _ ≤ f (x ⊔ y) * f (x ⊓ y) * (g (x ⊔ y) * g (x ⊓ y)) := key
    _ = f (x ⊔ y) * g (x ⊔ y) * (f (x ⊓ y) * g (x ⊓ y)) := by ring

/-- `0 ≤ S.indicator 1`. -/
theorem indicator_one_nonneg {n : ℕ} (S : Set (Fin n → ℝ)) :
    (0 : (Fin n → ℝ) → ℝ) ≤ S.indicator (1 : (Fin n → ℝ) → ℝ) :=
  fun _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _

/-- For `IsSublattice S`, the indicator `S.indicator 1` is affiliated. -/
theorem affiliated_indicator_of_isSublattice {n : ℕ} {S : Set (Fin n → ℝ)}
    (hS : IsSublattice S) : Affiliated (S.indicator (1 : (Fin n → ℝ) → ℝ)) := by
  intro x y
  by_cases hy : y ∈ S
  · by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy,
        Set.indicator_of_mem (hS.supClosed hx hy), Set.indicator_of_mem (hS.infClosed hx hy)]
      simp only [Pi.one_apply, mul_one, ge_iff_le, le_refl]
    · rw [Set.indicator_of_notMem hx, zero_mul]
      exact mul_nonneg (indicator_one_nonneg S _) (indicator_one_nonneg S _)
  · rw [Set.indicator_of_notMem hy, mul_zero]
    exact mul_nonneg (indicator_one_nonneg S _) (indicator_one_nonneg S _)

/-- `Affiliated f` implies `Affiliated fun z => f (Function.update z k c)`. -/
theorem Affiliated.update_slice {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : Affiliated f)
    (k : Fin n) (c : ℝ) : Affiliated fun z => f (Function.update z k c) := by
  intro x y
  have h := hf (Function.update x k c) (Function.update y k c)
  rwa [Function.update_sup_update, Function.update_inf_update, sup_idem, inf_idem] at h

/-- `maxAt i j = {z | ∀ k, k ≠ i → k ≠ j → z k ≤ z j}`: the profiles in which coordinate
`j` is at least every coordinate other than `i` and `j`. Coordinate `i` is unconstrained. -/
def maxAt {n : ℕ} (i j : Fin n) : Set (Fin n → ℝ) :=
  {z | ∀ k, k ≠ i → k ≠ j → z k ≤ z j}

/-- `z ∈ maxAt i j ↔ ∀ k, k ≠ i → k ≠ j → z k ≤ z j`. -/
theorem mem_maxAt_iff {n : ℕ} (i j : Fin n) (z : Fin n → ℝ) :
    z ∈ maxAt i j ↔ ∀ k, k ≠ i → k ≠ j → z k ≤ z j := Iff.rfl

/-- `IsSublattice (maxAt i j)`. -/
theorem isSublattice_maxAt {n : ℕ} (i j : Fin n) : IsSublattice (maxAt i j) where
  supClosed x hx y hy := fun k hki hkj => by
    simpa only [Pi.sup_apply] using sup_le_sup (hx k hki hkj) (hy k hki hkj)
  infClosed x hx y hy := fun k hki hkj => by
    simpa only [Pi.inf_apply] using inf_le_inf (hx k hki hkj) (hy k hki hkj)

/-- `topDensity f i j = fun z => f z * (maxAt i j).indicator 1 z`: the density `f`
restricted to the profiles in which coordinate `j` is the largest of the coordinates
other than `i`. -/
noncomputable def topDensity {n : ℕ} (f : (Fin n → ℝ) → ℝ) (i j : Fin n) :
    (Fin n → ℝ) → ℝ :=
  fun z => f z * (maxAt i j).indicator (1 : (Fin n → ℝ) → ℝ) z

/-- `topDensity f i j z = f z` for `z ∈ maxAt i j`. -/
theorem topDensity_of_mem {n : ℕ} (f : (Fin n → ℝ) → ℝ) (i j : Fin n) {z : Fin n → ℝ}
    (hz : z ∈ maxAt i j) : topDensity f i j z = f z := by
  simp only [topDensity, Set.indicator_of_mem hz, Pi.one_apply, mul_one]

/-- `topDensity f i j z = 0` for `z ∉ maxAt i j`. -/
theorem topDensity_of_notMem {n : ℕ} (f : (Fin n → ℝ) → ℝ) (i j : Fin n) {z : Fin n → ℝ}
    (hz : z ∉ maxAt i j) : topDensity f i j z = 0 := by
  simp only [topDensity, Set.indicator_of_notMem hz, mul_zero]

/-- `0 ≤ f` implies `0 ≤ topDensity f i j`. -/
theorem topDensity_nonneg {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf0 : 0 ≤ f) (i j : Fin n) :
    (0 : (Fin n → ℝ) → ℝ) ≤ topDensity f i j :=
  fun z => mul_nonneg (hf0 z) (indicator_one_nonneg _ z)

/-- `Affiliated f` and `0 ≤ f` imply `Affiliated (topDensity f i j)`. -/
theorem affiliated_topDensity {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : Affiliated f)
    (hf0 : 0 ≤ f) (i j : Fin n) : Affiliated (topDensity f i j) :=
  hf.mul (affiliated_indicator_of_isSublattice (isSublattice_maxAt i j)) hf0
    (indicator_one_nonneg _)

end Auction.Affiliation

end
