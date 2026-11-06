# Substitute envelopes and completion: follow-on development

This development follows the choice/completion material originating in #103 and
the many-to-one market reduction in #174. The mathematical objects belong in
`MathEconLib.Choice`, even when they additionally use a counterparty map; they do
not require a market.

## Status and integration

`Choice/Matching/SubstituteEnvelope.lean` supplies proof scripts for the envelope,
the greatest-completion characterization, the feasible-contraction formulation
of unilateral substitutability, and the hull–envelope sandwich. These scripts
must pass the repository build and proof-integrity checks before merging.

The general path-independent minorant, path-independent envelope, and rejection-evidence
characterization now have Lean proof scripts in `Choice/PathIndependentMinorant.lean`,
`Choice/Matching/PathIndependentEnvelope.lean`, and `Choice/Matching/CompletionEvidence.lean`.
The concrete clients in `MathEconLibExamples/Choice/SubstituteEnvelope.lean` apply greatestness,
the sandwich, and a rejection obstruction. Validation of these additions is pending.
The finite obstruction bound and four-contract demand impossibility remain mathematical
specifications with proofs, not claims of completed Lean formalization. They are included here so the follow-on PR records the entire
research development rather than silently dropping its remaining components.

## Conventions

Write `s : X → A` for the counterparty map and call a set feasible when `s` is
injective on it. Write F for the family of feasible sets. A choice function C
satisfies C(Y) ⊆ Y. Order choice functions by pointwise inclusion.

A completion D of C satisfies, at every Y, either D(Y) = C(Y) or D(Y) is
infeasible. Completion does not mean enlargement and does not include IRC.
Use the existing `SubstitutablyCompletable` and
`HasConsistentSubstitutableCompletion` predicates without changing their meanings.

## 1. The substitute envelope

Define

    U_C(Y) = {x ∈ Y : for every feasible V ⊆ Y containing x, x ∈ C(V)}.

Equivalently, remove every rejection witnessed on a feasible sub-menu:

    U_C(Y) = Y \ ⋃ {V \ C(V) : V ⊆ Y, V feasible}.

This construction is substitutable: restricting Y reduces the collection of
tests. Any substitutable completion D lies below U_C. Indeed, if x ∈ D(Y) and
x ∈ V ⊆ Y with V feasible, substitutability gives x ∈ D(V) = C(V).

**Greatest-completion theorem.** If C satisfies IRC, then C has a substitutable
completion if and only if U_C is a completion. In that case U_C is the greatest
substitutable completion. No finiteness assumption is needed; this implication
does not even require that C be feasible-valued.

Proof. Let D be a substitutable completion, so D ≤ U_C. If U_C(Y) is feasible,
so is D(Y); hence D(Y) = C(Y) ⊆ U_C(Y). IRC gives C(U_C(Y)) = C(Y).
Testing the definition of U_C at the feasible sub-menu U_C(Y) shows
U_C(Y) ⊆ C(U_C(Y)). Thus U_C(Y) = C(Y), as required. The converse follows
from substitutability of U_C. Its greatestness follows from D ≤ U_C.

Do not call U_C a completion without the existence hypothesis. Do not infer
that it satisfies IRC from IRC of C.

## 2. Unilateral substitutability and the sandwich

The inequality C ≤ U_C is equivalent to the feasible-contraction axiom

    V ⊆ Y and V feasible  ⇒  C(Y) ∩ V ⊆ C(V).

The larger menu Y is unrestricted. For feasible, finite-valued IRC choice,
the existing hull theorem and the new envelope results give

    unilateral substitutability ⇔ C ≤ U_C ⇔ H_C ≤ U_C.

Here H_C is the existing substitute hull. Forward: H_C is a substitutable
completion and therefore lies below U_C. Reverse: any D with C ≤ D ≤ U_C
is a completion when C satisfies IRC. If D(Y) is feasible, IRC gives
C(D(Y)) = C(Y), and the envelope test gives D(Y) ⊆ C(D(Y)). Apply this to
D = U_C and use the existing converse from an enlarging substitutable completion.

More generally, for every IRC C and every D,

    D is a substitutable completion and C ≤ D
      ⇔ D is substitutable and H_C ≤ D ≤ U_C.

The interval describes enlarging completions only. Arbitrary completions may
delete original choices and need not lie above H_C. Unilateral substitutability
therefore means that completing the rule is possible without deleting any
original choice (under the stated feasibility and finite-valuedness hypotheses).

## 3. Rejection-evidence axiom for general completability

Assume C satisfies IRC. Feasible-valuedness is not needed. For any menu Y and any collection
of feasible sub-menus V_i ⊆ Y, put R = ⋃_i (V_i \ C(V_i)). Then substitutable
completability is equivalent to

    Y \ R feasible  ⇒  C(Y) ∩ R = ∅.

Necessity: any substitutable completion D rejects every member of R at Y, so
D(Y) ⊆ Y \ R. If that residual is feasible, D(Y) is feasible and equals C(Y).

Sufficiency: take all feasible sub-menus of Y, making the residual U_C(Y).
The axiom gives C(Y) ⊆ U_C(Y) whenever U_C(Y) is feasible. IRC and the envelope
test then give equality, proving that U_C is a completion.

On a finite carrier, failure has a finite witness: a menu Y and at most |Y|
feasible sub-menus whose rejection union removes an originally chosen contract
and leaves a feasible residual. Choose one witnessing sub-menu for each rejected
contract. This is an obstruction certificate, not an efficiency claim.

## 4. The path-independent envelope

Define P_C to be the greatest path-independent choice function below U_C, namely
the pointwise union of all path-independent rules below U_C. The empty rule is
included. This is the standard greatest-minorant/Plottization construction; do
not attribute that general construction to this development.

For completeness, arbitrary unions preserve substitutability. They also preserve
IRC: if the union's choice from Y lies in V ⊆ Y, each constituent's choice does
too, so IRC of each constituent identifies its choices from V and Y. Thus P_C
is path independent on arbitrary carriers and is the greatest such minorant.

For any original choice rule C, without assuming IRC,

    C has a substitutable IRC completion ⇔ P_C is a completion.

When these conditions hold, P_C is the greatest substitutable IRC completion.
Proof: any such completion D is path independent and lies below U_C, so
D ≤ P_C ≤ U_C. If P_C(Y) is feasible, D(Y) = C(Y) ⊆ P_C(Y).
IRC of D gives D(P_C(Y)) = D(Y). Since P_C(Y) is a feasible menu,
completion gives C(P_C(Y)) = D(P_C(Y)) = C(Y). The envelope test now
implies P_C(Y) ⊆ C(P_C(Y)) = C(Y), proving equality. Thus IRC is required
of the witnessing completion D, not of C. This argument works on arbitrary
contract types.

The three public results `pathIndependentEnvelope_isCompletionOf`,
`hasConsistentSubstitutableCompletion_iff_pathIndependentEnvelope_isCompletionOf`,
and `isGreatest_pathIndependentEnvelope` consequently no longer take an
original-rule IRC argument. Callers should omit that argument; the completion
predicate and conclusions are unchanged. The separate substitute-envelope and
sandwich theorems retain their stated IRC assumptions.

For feasible finite-valued IRC C satisfying unilateral substitutability, the
path-independent enlarging completions are exactly the path-independent D with
H_C ≤ D ≤ P_C. This does not show that bare and IRC completability coincide.

Placement: put the general greatest path-independent minorant in `Choice/`,
independent of counterparties. Its composition with U_C and the completion
theorems belong in `Choice/Matching/`. Reuse the existing equivalence between
path independence and substitutability plus consistency.

## 5. The law of aggregate demand cannot always be preserved

The existing `Choice.Conditions` already relates substitutability and the law of
aggregate demand to IRC. Reuse those results; be precise about their finiteness
hypotheses. The following obstruction holds on four contracts.

Let X = {a, a′, b, c}, with a and a′ sharing a counterparty, and b and c each
having a distinct other counterparty. Rank feasible bundles

    {b,c} > {b} > {a′,c} > {c} > {a} > {a′} > ∅,

with every unlisted feasible bundle below ∅. Let C choose the highest available
bundle. This is feasible and preference-induced, hence satisfies IRC.

Every nonempty menu has a nonempty choice. Its choice has size two exactly when
c is present and at least one of b and a′ is present. Thus C satisfies the law
of aggregate demand.

It is unilaterally substitutable. Contracts b and c are always chosen when
available. If a is its counterparty's only available contract and is rejected,
then b or c is present, and adding one contract cannot rescue a. If a′ is its
counterparty's only available contract and is rejected, b is present, and again
adding a contract cannot rescue it.

Nevertheless, **no substitutable completion satisfies the law of aggregate
demand**. Let D be any substitutable completion.

1. Every permissible D({a,a′,c}) contains a′: it either equals {a′,c} or is
   infeasible and therefore contains both a and a′. Substitutability forces
   a′ ∈ D({a,a′}). Since C({a,a′}) = {a}, completion forces D({a,a′}) = {a,a′}.
2. On the feasible menus {a,b} and {a′,b}, D equals C and chooses {b}.
   Substitutability therefore excludes a and a′ from D({a,a′,b}). Its choice
   is feasible, so completion forces D({a,a′,b}) = {b}.
3. Choice size falls from two to one between these nested menus.

This is stronger than failure of the substitute hull to preserve demand. It
rules out every substitutable completion, including completions that delete
original choices. It does not imply that a matching mechanism fails to be
strategy-proof. Priority of the counterexample/result remains to be checked.

Suggested formalization: a reusable example in `MathEconLibExamples/Choice/`,
using the existing preference-induced constructor if practical; direct
membership formulas are also possible. Prove the nonexistence theorem for
arbitrary D with the three-step argument above. Add an API regression importing
the example rather than duplicating it. Use kernel-checked proofs, not
`native_decide`. The finite Python check accompanying this document is auxiliary
verification only and does not replace Lean proofs.

The upper constructions need not preserve demand even when a good completion
exists: take unit-demand C with b > a > a′ > ∅, where a,a′ share a counterparty.
Then U_C = P_C chooses {b} whenever b is available and all available contracts
otherwise. It drops from two choices on {a,a′} to one on X, while C itself is a
substitutable, IRC, demand-monotone completion. Thus neither extremal construction
alone decides whether a demand-monotone completion exists.

## Remaining formalization checks

- Validate the formalized rejection-evidence axiom; formalize the finite obstruction bound.
- Validate the formalized general path-independent minorant and P_C completion theorem.
- Formalize the four-contract example and its universal nonexistence result.
- Validate the added concrete applications of the envelope, sandwich, and obstruction theorems.
- Build all targets, regenerate/verify imports, and run proof-integrity checks.

No changes to the manuscript, market definition, or completion predicates are
part of this follow-on. The public theorem generalizations are listed in Section 4.
