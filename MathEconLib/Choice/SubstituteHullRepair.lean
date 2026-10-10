import MathEconLib.Choice.SubstituteHull
import MathEconLib.ForMathlib.Order.IterateFixedPoint
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Powerset
import Mathlib.Logic.Relation

/-!
# Accumulating repairs converge to the substitute hull

The elementary choice-rule repair adds `Y ∩ C Z` to the choice from `Y`,
where `Y ⊆ Z`, retaining every previously chosen contract. A strict repair
must change the rule. Every finite sequence of repairs starting from `C`
stays between `C` and `C.substituteHull`; a terminal rule is substitutable
and therefore equals the hull. On a finite alternative type no infinite
sequence of strict repairs exists, and a terminal sequence exists.

The update is the accumulating interpretation of Zhang (2016), proof of
Proposition 2, §5, p. 233. His construction processes menu cardinalities in
descending order. The schedule independence and convergence to the hull
for the repair relation below are proved here. They concern repairs of a
single choice function, not a market's cumulative-offer process.
Zhang's Proposition 2 asserts bare substitutable completability and leaves
IRC of the completion unestablished (§§5–6, p. 233). Here, if the original
rule satisfies IRC, the terminal rule satisfies IRC by
`substituteHull_consistent`; no claim of IRC preservation is made for
intermediate rules.

Reference: Jun Zhang (2016), *On sufficient conditions for the existence of
stable matchings with contracts*, Economics Letters 145, 230–234,
https://doi.org/10.1016/j.econlet.2016.06.029.
-/

namespace MathEconLib.Choice

universe u

namespace ChoiceFunction

variable {X : Type u} {C D E : ChoiceFunction X}

/-- Accumulate the choices from source menu `Z` that are available at
menu `Y`. Other menus retain their choices. The subset hypothesis
`Y ⊆ Z` belongs to the repair relation, not this definition. -/
def substituteRepair (C : ChoiceFunction X) (Y Z : Set X) : ChoiceFunction X where
  toFun W := C W ∪ {x | W = Y ∧ x ∈ W ∧ x ∈ C Z}
  choose_subset := by
    intro W x hx
    rcases hx with hx | ⟨_, hx, _⟩
    · exact C.choose_subset W hx
    · exact hx

@[simp] theorem mem_substituteRepair {Y Z W : Set X} {x : X} :
    x ∈ C.substituteRepair Y Z W ↔
      x ∈ C W ∨ W = Y ∧ x ∈ W ∧ x ∈ C Z := Iff.rfl

@[simp] theorem substituteRepair_apply (C : ChoiceFunction X) (Y Z : Set X) :
    C.substituteRepair Y Z Y = C Y ∪ (Y ∩ C Z) := by
  ext x
  simp

/-- An accumulating repair is a pointwise enlargement. -/
theorem le_substituteRepair (C : ChoiceFunction X) (Y Z : Set X) :
    C ≤ C.substituteRepair Y Z := by
  intro W x hx
  exact Or.inl hx

/-- Every substitutable upper bound is preserved by a repair. -/
theorem substituteRepair_le {Y Z : Set X} (hYZ : Y ⊆ Z)
    (hD : D.Substitutable) (hCD : C ≤ D) :
    C.substituteRepair Y Z ≤ D := by
  intro W x hx
  rcases hx with hx | ⟨rfl, hxY, hxZ⟩
  · exact hCD W hx
  · exact substitutable_iff_chernoff.mp hD hYZ ⟨hCD Z hxZ, hxY⟩

/-- A substitutable rule admits no effective repair. -/
theorem Substitutable.substituteRepair_eq (hC : C.Substitutable)
    {Y Z : Set X} (hYZ : Y ⊆ Z) : C.substituteRepair Y Z = C :=
  le_antisymm (substituteRepair_le hYZ hC le_rfl)
    (le_substituteRepair C Y Z)

/-- A strict accumulating repair: the source menu contains the target
menu, and the update changes the rule. Allowing `Y = Z` in the definition
is harmless because such an update cannot be strict. -/
def SubstituteRepairStep (C D : ChoiceFunction X) : Prop :=
  ∃ Y Z : Set X, Y ⊆ Z ∧ D = C.substituteRepair Y Z ∧ C ≠ D

/-- A strict repair increases the pointwise order. -/
theorem SubstituteRepairStep.lt (h : SubstituteRepairStep C D) : C < D := by
  rcases h with ⟨Y, Z, _, rfl, hne⟩
  exact lt_iff_le_and_ne.mpr ⟨le_substituteRepair C Y Z, hne⟩

/-- Repairs preserve every substitutable upper bound. -/
theorem SubstituteRepairStep.le_of_substitutable (h : SubstituteRepairStep C D)
    (hE : E.Substitutable) (hCE : C ≤ E) : D ≤ E := by
  rcases h with ⟨Y, Z, hYZ, rfl, _⟩
  exact substituteRepair_le hYZ hE hCE

/-- There is no effective elementary repair left to perform. -/
def SubstituteRepairTerminal (C : ChoiceFunction X) : Prop :=
  ∀ D, ¬ SubstituteRepairStep C D

/-- Absence of a repair is exactly substitutability, on arbitrary types. -/
theorem substituteRepairTerminal_iff :
    SubstituteRepairTerminal C ↔ C.Substitutable := by
  constructor
  · intro hterminal
    apply substitutable_iff_chernoff.mpr
    intro Y Z hYZ x hx
    by_contra hxC
    have hne : C ≠ C.substituteRepair Y Z := by
      intro heq
      have hxrepair : x ∈ C.substituteRepair Y Z Y :=
        Or.inr ⟨rfl, hx.2, hx.1⟩
      rw [← heq] at hxrepair
      exact hxC hxrepair
    exact hterminal _ ⟨Y, Z, hYZ, rfl, hne⟩
  · intro hC D hstep
    rcases hstep with ⟨Y, Z, hYZ, rfl, hne⟩
    exact hne (hC.substituteRepair_eq hYZ).symm

/-- A finite sequence of strict repairs, including the empty sequence.
Use the general reflexive transitive closure to express reachability. -/
abbrev SubstituteRepairReachable (C D : ChoiceFunction X) : Prop :=
  Relation.ReflTransGen SubstituteRepairStep C D

/-- Every repair sequence enlarges the initial choices. -/
theorem SubstituteRepairReachable.le (h : SubstituteRepairReachable C D) : C ≤ D := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact ih.trans hstep.lt.le

/-- Every repair sequence remains below the initial rule's hull. -/
theorem SubstituteRepairReachable.le_substituteHull
    (h : SubstituteRepairReachable C D) : D ≤ C.substituteHull := by
  induction h with
  | refl =>
      exact _root_.MathEconLib.Choice.ChoiceFunction.le_substituteHull C
  | tail _ hstep ih =>
      exact hstep.le_of_substitutable (substituteHull_substitutable C) ih

/-- Every terminal repair sequence has the same endpoint: the hull.
Finiteness of the alternative type is unnecessary for this conclusion
about a sequence that does terminate. -/
theorem SubstituteRepairReachable.eq_substituteHull
    (h : SubstituteRepairReachable C D) (hterminal : SubstituteRepairTerminal D) :
    D = C.substituteHull :=
  le_antisymm h.le_substituteHull
    (substituteHull_le (substituteRepairTerminal_iff.mp hterminal) h.le)

/-- IRC is guaranteed at the endpoint, without any hypothesis on the
intermediate repaired rules. -/
theorem SubstituteRepairReachable.consistent_of_terminal
    (h : SubstituteRepairReachable C D) (hterminal : SubstituteRepairTerminal D)
    (hC : C.Consistent) : D.Consistent := by
  rw [h.eq_substituteHull hterminal]
  exact substituteHull_consistent hC

/-- On a finite carrier there are only finitely many menu-to-choice maps.
Extensionality embeds choice rules into this finite function type. -/
private theorem finite_choiceRules [Finite X] : Finite (ChoiceFunction X) := by
  exact Finite.of_injective
    (fun C : ChoiceFunction X => (C : Set X → Set X)) DFunLike.coe_injective

/-- A finite carrier rules out an infinite sequence of strict repairs.
Combined with `SubstituteRepairReachable.eq_substituteHull`, this proves
termination and schedule independence for maximal strict repair runs. -/
theorem not_infinite_substituteRepairSteps [Finite X]
    (D : ℕ → ChoiceFunction X) : ¬ ∀ n, SubstituteRepairStep (D n) (D (n + 1)) := by
  letI : Finite (ChoiceFunction X) := finite_choiceRules
  intro hstep
  have hstrict : StrictMono D := strictMono_nat_of_lt_succ fun n => (hstep n).lt
  obtain ⟨m, n, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite D
  exact hne (hstrict.injective heq)

/-- Iteration of a selector that either waits or performs a repair gives
a finite repair sequence after every number of steps. -/
theorem substituteRepairReachable_iterate
    (next : ChoiceFunction X → ChoiceFunction X)
    (hnext : ∀ D, next D = D ∨ SubstituteRepairStep D (next D))
    (C : ChoiceFunction X) (n : ℕ) :
    SubstituteRepairReachable C (next^[n] C) := by
  induction n with
  | zero => exact .refl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      rcases hnext (next^[n] C) with heq | hstep
      · rw [heq]
        exact ih
      · exact ih.tail hstep

/-- Any selector that performs a strict repair whenever the rule is not
terminal reaches the hull on a finite carrier. This is a theorem about
arbitrary selectors, not an executable scheduling implementation. -/
theorem exists_iterate_eq_substituteHull_of_repair [Finite X]
    (next : ChoiceFunction X → ChoiceFunction X)
    (hnext : ∀ D, (SubstituteRepairTerminal D ∧ next D = D) ∨
      SubstituteRepairStep D (next D)) (C : ChoiceFunction X) :
    ∃ n, next^[n] C = C.substituteHull := by
  letI : Finite (ChoiceFunction X) := finite_choiceRules
  have hinfl : ∀ D, D ≤ next D := by
    intro D
    rcases hnext D with ⟨_, heq⟩ | hstep
    · exact heq.ge
    · exact hstep.lt.le
  have hreach (n : ℕ) : SubstituteRepairReachable C (next^[n] C) :=
    substituteRepairReachable_iterate next
      (fun D => (hnext D).elim (fun h => Or.inl h.2) Or.inr) C n
  obtain ⟨n, hfix⟩ := Function.exists_iterate_succ_eq_of_inflationary next hinfl C
  refine ⟨n, (hreach n).eq_substituteHull ?_⟩
  rcases hnext (next^[n] C) with ⟨hterminal, _⟩ | hstep
  · exact hterminal
  · have hfix' : next (next^[n] C) = next^[n] C := by
      simpa only [Function.iterate_succ_apply'] using hfix
    exact (ne_of_lt hstep.lt hfix'.symm).elim

/-- At least one finite sequence of strict repairs reaches the hull.
Together with uniqueness of terminal endpoints and absence of infinite
strict runs, this gives the maximal-sequence formulation. -/
theorem substituteRepairReachable_substituteHull [Finite X] (C : ChoiceFunction X) :
    SubstituteRepairReachable C C.substituteHull := by
  classical
  let next : ChoiceFunction X → ChoiceFunction X := fun D =>
    if h : ∃ E, SubstituteRepairStep D E then Classical.choose h else D
  have hnext (D : ChoiceFunction X) :
      (SubstituteRepairTerminal D ∧ next D = D) ∨ SubstituteRepairStep D (next D) := by
    by_cases h : ∃ E, SubstituteRepairStep D E
    · right
      simpa only [next, dif_pos h] using Classical.choose_spec h
    · left
      refine ⟨?_, ?_⟩
      · intro E hstep
        exact h ⟨E, hstep⟩
      · simp only [next, dif_neg h]
  obtain ⟨n, hn⟩ := exists_iterate_eq_substituteHull_of_repair next hnext C
  have hreach (n : ℕ) : SubstituteRepairReachable C (next^[n] C) :=
    substituteRepairReachable_iterate next
      (fun D => (hnext D).elim (fun h => Or.inl h.2) Or.inr) C n
  exact hn ▸ hreach n

/-- A finite repair run with no available strict continuation exists. -/
theorem exists_substituteRepairReachable_terminal [Finite X] (C : ChoiceFunction X) :
    ∃ D, SubstituteRepairReachable C D ∧ SubstituteRepairTerminal D :=
  ⟨C.substituteHull, substituteRepairReachable_substituteHull C,
    substituteRepairTerminal_iff.mpr (substituteHull_substitutable C)⟩

end ChoiceFunction

end MathEconLib.Choice
