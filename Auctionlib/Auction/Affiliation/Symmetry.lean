module

public import Auctionlib.Auction.Affiliation.Marginal
public import Mathlib

/-! # The symmetric model (Def 7.1, symmetric variant)

## Main results

* `Auction.Affiliation.IsSymmetricValues` : `E.v (σ i) X = E.v i (X ∘ σ)` for every
  permutation `σ` of the bidders, every `i` and every profile `X`.
* `Auction.Affiliation.HasExchangeableSignals` : `E.f (X ∘ σ) = E.f X` for every
  permutation `σ` and every profile `X`.
* `Auction.Affiliation.IsSymmetricModel` : `IsSymmetricValues E ∧ HasExchangeableSignals E`.
* `Auction.Affiliation.IsSymmetricValues.rival_symm` : for `σ i = i`,
  `E.v i (X ∘ σ) = E.v i X`.
* `Auction.Affiliation.IsSymmetricValues.eq_u` : for `0 < n`,
  `E.v i X = E.v ⟨0, hn⟩ (X ∘ Equiv.swap ⟨0, hn⟩ i)`.
* `Auction.Affiliation.isSymmetricValues_of_swap` : `IsSymmetricValues E` follows from the
  defining equation for the transpositions `Equiv.swap a b` alone.
* `Auction.Affiliation.HasExchangeableSignals.of_swap` : `HasExchangeableSignals E` follows
  from `E.f (X ∘ Equiv.swap a b) = E.f X` alone.
* `Auction.Affiliation.update_comp_perm` :
  `Function.update x k s ∘ σ = Function.update (x ∘ σ) (σ.symm k) s`.
* `Auction.Affiliation.marginal_comp_perm` :
  `marginal μ (fun z => F (z ∘ σ)) k x = marginal μ F (σ.symm k) (x ∘ σ)`.
* `Auction.Affiliation.marginal_comp_perm_eq` :
  `marginal μ (fun z => F (z ∘ σ)) k = fun y => marginal μ F (σ.symm k) (y ∘ σ)`.
* `Auction.Affiliation.marginalList_comp_perm` :
  `marginalList μ (fun z => F (z ∘ σ)) l x = marginalList μ F (l.map σ.symm) (x ∘ σ)`.
* `Auction.Affiliation.fibreIntegrable_comp_perm` :
  `FibreIntegrable μ (fun z => F (z ∘ σ)) l ↔ FibreIntegrable μ F (l.map σ.symm)`.
-/

@[expose] public section

open MeasureTheory

namespace Auction.Affiliation

/-! ### The predicates -/

/-- **Def 7.1**, symmetric variant, value half: the family `v` is equivariant under
relabelling of the bidders, `E.v (σ i) X = E.v i (X ∘ σ)` for every permutation `σ` of
`Fin n`, every bidder `i` and every signal profile `X`.

For `σ = Equiv.swap i j` this reads `E.v j X = E.v i (X ∘ Equiv.swap i j)`. -/
def IsSymmetricValues {n : ℕ} (E : SignalValueEnv n) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (i : Fin n) (X : Fin n → ℝ), E.v (σ i) X = E.v i (X ∘ σ)

/-- **Def 7.1**, symmetric variant, signal half: the joint density is exchangeable,
`E.f (X ∘ σ) = E.f X` for every permutation `σ` of `Fin n` and every signal profile `X`. -/
def HasExchangeableSignals {n : ℕ} (E : SignalValueEnv n) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (X : Fin n → ℝ), E.f (X ∘ σ) = E.f X

/-- **Def 7.1**, symmetric variant: equivariance of the value family
(`IsSymmetricValues`) together with exchangeability of the signal density
(`HasExchangeableSignals`). -/
def IsSymmetricModel {n : ℕ} (E : SignalValueEnv n) : Prop :=
  IsSymmetricValues E ∧ HasExchangeableSignals E

/-! ### Symmetry in the rivals, and the single value map `u` -/

/-- Under `IsSymmetricValues E`, the map `E.v i` is invariant under the permutations
fixing `i`: if `σ i = i` then `E.v i (X ∘ σ) = E.v i X`. -/
theorem IsSymmetricValues.rival_symm {n : ℕ} {E : SignalValueEnv n}
    (h : IsSymmetricValues E) (i : Fin n) {σ : Equiv.Perm (Fin n)} (hσ : σ i = i)
    (X : Fin n → ℝ) : E.v i (X ∘ σ) = E.v i X := by
  have := h σ i X
  rw [hσ] at this
  exact this.symm

/-- Under `IsSymmetricValues E` with `0 < n`, the whole family `E.v` is determined by the
single map `E.v ⟨0, hn⟩` : `E.v i X = E.v ⟨0, hn⟩ (X ∘ Equiv.swap ⟨0, hn⟩ i)`. -/
theorem IsSymmetricValues.eq_u {n : ℕ} {E : SignalValueEnv n}
    (h : IsSymmetricValues E) (hn : 0 < n) (i : Fin n) (X : Fin n → ℝ) :
    E.v i X = E.v ⟨0, hn⟩ (X ∘ Equiv.swap ⟨0, hn⟩ i) := by
  have := h (Equiv.swap (⟨0, hn⟩ : Fin n) i) ⟨0, hn⟩ X
  rwa [Equiv.swap_apply_left] at this

/-! ### Introduction from transpositions -/

/-- `IsSymmetricValues E` follows from its defining equation for transpositions alone:
if `E.v (Equiv.swap a b i) X = E.v i (X ∘ Equiv.swap a b)` for all `a`, `b`, `i`, `X`,
then `E.v (σ i) X = E.v i (X ∘ σ)` for every permutation `σ`. -/
theorem isSymmetricValues_of_swap {n : ℕ} {E : SignalValueEnv n}
    (h : ∀ (a b i : Fin n) (X : Fin n → ℝ),
      E.v (Equiv.swap a b i) X = E.v i (X ∘ Equiv.swap a b)) :
    IsSymmetricValues E := by
  intro σ
  induction σ using Equiv.Perm.swap_induction_on with
  | one => intro i X; simp
  | swap_mul τ a b _ ih =>
    intro i X
    have h₁ : E.v (Equiv.swap a b (τ i)) X = E.v (τ i) (X ∘ Equiv.swap a b) :=
      h a b (τ i) X
    have h₂ : E.v (τ i) (X ∘ Equiv.swap a b) = E.v i ((X ∘ Equiv.swap a b) ∘ τ) :=
      ih i (X ∘ Equiv.swap a b)
    have h₃ : ((X ∘ Equiv.swap a b) ∘ τ) = X ∘ (Equiv.swap a b * τ : Equiv.Perm (Fin n)) := by
      rw [Equiv.Perm.coe_mul]
      rfl
    calc E.v ((Equiv.swap a b * τ : Equiv.Perm (Fin n)) i) X
        = E.v (Equiv.swap a b (τ i)) X := rfl
      _ = E.v i ((X ∘ Equiv.swap a b) ∘ τ) := h₁.trans h₂
      _ = E.v i (X ∘ (Equiv.swap a b * τ : Equiv.Perm (Fin n))) := by rw [h₃]

/-- `HasExchangeableSignals E` follows from invariance under transpositions alone:
if `E.f (X ∘ Equiv.swap a b) = E.f X` for all `a`, `b`, `X`, then `E.f (X ∘ σ) = E.f X`
for every permutation `σ`. -/
theorem HasExchangeableSignals.of_swap {n : ℕ} {E : SignalValueEnv n}
    (h : ∀ (a b : Fin n) (X : Fin n → ℝ), E.f (X ∘ Equiv.swap a b) = E.f X) :
    HasExchangeableSignals E := by
  intro σ
  induction σ using Equiv.Perm.swap_induction_on with
  | one => intro X; simp
  | swap_mul τ a b _ ih =>
    intro X
    have h₃ : ((X ∘ Equiv.swap a b) ∘ τ) = X ∘ (Equiv.swap a b * τ : Equiv.Perm (Fin n)) := by
      rw [Equiv.Perm.coe_mul]
      rfl
    calc E.f (X ∘ (Equiv.swap a b * τ : Equiv.Perm (Fin n)))
        = E.f ((X ∘ Equiv.swap a b) ∘ τ) := by rw [h₃]
      _ = E.f (X ∘ Equiv.swap a b) := ih (X ∘ Equiv.swap a b)
      _ = E.f X := h a b X

/-! ### Permutation equivariance of the iterated marginal -/

/-- `Function.update x k s ∘ σ = Function.update (x ∘ σ) (σ.symm k) s`. -/
theorem update_comp_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (k : Fin n)
    (s : ℝ) : Function.update x k s ∘ σ = Function.update (x ∘ σ) (σ.symm k) s := by
  funext m
  by_cases hm : m = σ.symm k
  · subst hm
    rw [Function.comp_apply, Equiv.apply_symm_apply, Function.update_self,
      Function.update_self]
  · have hσm : σ m ≠ k := fun hc => hm (by rw [← hc, Equiv.symm_apply_apply])
    simp [Function.comp_apply, Function.update_of_ne hm, Function.update_of_ne hσm]

/-- `marginal μ (fun z => F (z ∘ σ)) k x = marginal μ F (σ.symm k) (x ∘ σ)`. -/
theorem marginal_comp_perm {n : ℕ} (μ : Measure ℝ) (σ : Equiv.Perm (Fin n))
    (F : (Fin n → ℝ) → ℝ) (k : Fin n) (x : Fin n → ℝ) :
    marginal μ (fun z => F (z ∘ σ)) k x = marginal μ F (σ.symm k) (x ∘ σ) := by
  simp only [marginal, update_comp_perm]

/-- `marginal μ (fun z => F (z ∘ σ)) k = fun y => marginal μ F (σ.symm k) (y ∘ σ)`. -/
theorem marginal_comp_perm_eq {n : ℕ} (μ : Measure ℝ) (σ : Equiv.Perm (Fin n))
    (F : (Fin n → ℝ) → ℝ) (k : Fin n) :
    marginal μ (fun z => F (z ∘ σ)) k
      = fun y => marginal μ F (σ.symm k) (y ∘ σ) :=
  funext fun y => marginal_comp_perm μ σ F k y

/-- `marginalList μ (fun z => F (z ∘ σ)) l x = marginalList μ F (l.map σ.symm) (x ∘ σ)`. -/
theorem marginalList_comp_perm {n : ℕ} (μ : Measure ℝ) (σ : Equiv.Perm (Fin n)) :
    ∀ (l : List (Fin n)) (F : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ),
      marginalList μ (fun z => F (z ∘ σ)) l x
        = marginalList μ F (l.map (σ.symm : Fin n → Fin n)) (x ∘ σ) := by
  intro l
  induction l with
  | nil => intro F x; rfl
  | cons j l ih =>
    intro F x
    show marginalList μ (marginal μ (fun z => F (z ∘ σ)) j) l x
      = marginalList μ (marginal μ F (σ.symm j)) (l.map (σ.symm : Fin n → Fin n)) (x ∘ σ)
    rw [marginal_comp_perm_eq μ σ F j]
    exact ih (marginal μ F (σ.symm j)) x

/-- `FibreIntegrable μ (fun z => F (z ∘ σ)) l ↔ FibreIntegrable μ F (l.map σ.symm)`. -/
theorem fibreIntegrable_comp_perm {n : ℕ} (μ : Measure ℝ) (σ : Equiv.Perm (Fin n)) :
    ∀ (l : List (Fin n)) (F : (Fin n → ℝ) → ℝ),
      FibreIntegrable μ (fun z => F (z ∘ σ)) l
        ↔ FibreIntegrable μ F (l.map (σ.symm : Fin n → Fin n)) := by
  intro l
  induction l with
  | nil => intro F; exact Iff.rfl
  | cons j l ih =>
    intro F
    show ((∀ x : Fin n → ℝ, Integrable (fun s => F (Function.update x j s ∘ σ)) μ)
        ∧ FibreIntegrable μ (marginal μ (fun z => F (z ∘ σ)) j) l)
      ↔ ((∀ x : Fin n → ℝ, Integrable
            (fun s => F (Function.update x (σ.symm j) s)) μ)
        ∧ FibreIntegrable μ (marginal μ F (σ.symm j)) (l.map (σ.symm : Fin n → Fin n)))
    rw [marginal_comp_perm_eq μ σ F j, ih (marginal μ F (σ.symm j))]
    refine and_congr (Iff.intro (fun hF x => ?_) (fun hF x => ?_)) Iff.rfl
    · have := hF (x ∘ σ.symm)
      simp only [update_comp_perm σ (x ∘ σ.symm) j] at this
      have hx : (x ∘ (σ.symm : Fin n → Fin n)) ∘ (σ : Fin n → Fin n) = x := by
        funext m; simp
      rwa [hx] at this
    · simp only [update_comp_perm σ x j]
      exact hF (x ∘ σ)

end Auction.Affiliation
