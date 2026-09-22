# Library design

## Motivation

While a formal economic library can guarantee mathematical correctness through the Lean kernel, _economic_ correctness—that is, the faithfulness of the library's theorems and definitions to the concepts they purport to represent—must be enforced through careful and consistent design. A shared design framework gives contributors a common way to evaluate the abstractions in the library and helps users understand how the parts of the library fit together.

The design principles described herein give the library a shared language in both form (the structure and shape of declarations) and in substance (the primitives those declarations share). Consistency in both of these domains helps to guarantee correctness by encouraging the reuse of fundamental concepts and constraining the "degrees of freedom" of contributors when defining new concepts or proving new theorems.

## Status and use

This is a living document and will be revised as the library develops and the
project learns from new applications. The principles are strong defaults for
new code and separately approved refactors, not rigid rules. A departure may be
appropriate when its reason is stated clearly. The principles do not by
themselves deprecate an existing API or authorize a change to a public
declaration.

Authoring requirements live in [`CONTRIBUTING.md`](CONTRIBUTING.md), review
policy lives in [`docs/REVIEWING.md`](docs/REVIEWING.md), and operational review
procedures live in [`docs/TOOLING.md`](docs/TOOLING.md). The Lean fragments in
this document express intended design directions, but they are not necessarily
declarations currently provided by `auctionlib`. Exact API changes still
require their own design and implementation review.

## Design principles

The principles address semantic mismatch, unnecessary specificity, exposed implementation details, and duplicated concepts. They apply both to foundational definitions and to the statements and organization of theorems built on them.

### P1. Prefer minimally constitutive definitions

A familiar economic or mathematical definition should encode its minimal constitutive content: The data and properties necessary and sufficient for an object to be an instance of the concept.

- Necessity: A definition must not exclude a legitimate instance because it lacks a usual regularity condition or because the definition encodes a convention that need not hold universally.
- Sufficiency: Every object admitted by the definition must meet the expected semantics of the underlying concept.

For every field or hypothesis, ask whether removing it would admit an object that no longer deserves the name. If not, the field does not belong in the definition. Then check both directions: If the declaration excludes a legitimate instance, it contains a nonconstitutive condition; if it admits an object that an economist would reject, a constitutive condition is missing.

When a term has several established meanings, state the intended scope in the docstring and distinguish the variants explicitly. Minimality is relative to that scope; it does not require one definition to accommodate every use of the term. Scope decisions should also be reflected in module organization and naming. Variants of a term with different scopes are siblings, each in its own namespace, with the scope visible in the name or namespace.

The same discipline applies to theorem statements. A theorem's name,
documentation, and advertised scope must match what its formal statement
establishes. A useful algebraic identity may be an important helper without
being the economic proposition it helps to prove, and the two should be labeled
accordingly. Every hypothesis should be load-bearing. Stronger assumptions
should enter at the first theorem or layer that needs them, often through a
specialized corollary rather than the underlying definition or general result.

#### Example

Consider a deterministic mechanism: Agents choose actions and the mechanism selects an outcome and monetary transfers. Its constitutive data can be expressed as follows:

> **Note.** The prior-free generic mechanism used in these examples is the
> project's active architectural direction. Its detailed design is recorded in
> [issue #67](https://github.com/AxiomMath/auctionlib/issues/67), with the initial
> migration implemented in
> [PR #68](https://github.com/AxiomMath/auctionlib/pull/68). The principles here
> explain the intended architecture; the exact declarations remain subject to
> review until that PR lands.

```lean
/-- A profile assigning one value of type `X i` to each agent `i`. -/
abbrev Profile {I : Type*} (X : I → Type*) := ∀ i, X i

/-- A deterministic mechanism with outcomes and monetary transfers. -/
structure Mechanism (I : Type*) (A : I → Type*) (O : Type*) where
  /-- The outcome selected at an action profile. -/
  outcome : Profile A → O
  /-- Net money received by an agent at an action profile. -/
  transfer : I → Profile A → ℝ
```

Note that the usual regularity conditions that accompany "well-behaved" instances are not present. For example, there is no measurability condition, since measurability becomes relevant only when an outcome or transfer is integrated in a probabilistic model. Efficiency, dominant-strategy incentive compatibility, and ex-post individual rationality are meaningful without a measurable space or a prior. Requiring measurable rules in this general definition would exclude deterministic mechanisms for a condition unrelated to those questions.

Now consider a single-good auction, which specializes this mechanism with outcomes that award one indivisible good. If the outcome type is an allocation vector `I → Bool` with no further condition, the definition admits mechanisms that award the good to two bidders at once. No economist would call that a single-good auction, so a constitutive condition is missing. Taking `O := Option I` restores sufficiency by making the infeasible outcomes unrepresentable, since an outcome names a recipient or none. An allocation-vector representation is also legitimate when an explicit feasibility condition restricts it to at most one recipient; this example does not require every auction to use `Option I`.

### P2. Generalize to the most useful shared level, then specialize

When several concepts follow the same rule, define that rule once at the most general useful level, then obtain the familiar concepts by supplying the relevant objects and relations. For theorems, prove the shared result in that general language using only the assumptions needed there, then derive stronger or application-specific statements as corollaries.

When deciding the level of generality, consider that a generalization should support an identifiable use beyond the case that prompted it or simplify the dependency structure by letting one proof replace several. A more general formulation being possible is not by itself a reason to introduce it.

A named abstraction is expensive: it becomes part of the interface that users
must discover and maintainers must support. Introduce one when it has a second
consumer, supports a genuinely shared theorem, or materially simplifies the
dependency structure. Until then, prefer keeping a one-use expression local.

This gives different parts of the library a common foundation, moving responsibility for ensuring that higher-level abstractions are expressions of the same underlying concept from the designer to the Lean kernel. Lean is then able to guarantee that general results apply directly to every specialization and that maps between specializations are able to transport those results. Equivalence theorems can focus on the relationship between the specializations rather than reconcile independent definitions.

This also suggests a guideline for module organization. A theorem belongs with the most general definitions the library has in which it can be stated and proved, not necessarily with the application in which it was first needed.

#### Examples

In its general form, a game-theoretic equilibrium problem comprises (1) the possible profiles, (2) who can deviate, (3) which alternative profiles are considered deviations by an actor, and (4) how that actor evaluates a profile.

P2 suggests that one should define this basic structure once: A profile is an equilibrium when no allowed deviation gives the deviator a higher value.

```lean
/-- Profiles evaluated by deviators with specified admissible deviations. -/
structure EquilibriumProblem (S : Type*) (I : Type*) where
  /-- Whether the second profile is an admissible deviation from the first. -/
  deviation : I → S → S → Prop
  /-- The deviator's payoff at a profile. -/
  value : I → S → ℝ

/-- No admissible deviation strictly improves the deviator's payoff. -/
def EquilibriumProblem.IsEquilibrium {S I : Type*}
    (P : EquilibriumProblem S I) (s : S) : Prop :=
  ∀ i s', P.deviation i s s' → P.value i s' ≤ P.value i s
```

Then different equilibrium concepts are specializations of this one underlying structure. For Nash equilibrium in a strategic game, (1) a profile is an action profile; (2) a deviator is a player; (3) an allowed deviation changes only that player’s action; and (4) the value is that player’s payoff.

For interim Bayesian Nash equilibrium in a finite Bayesian game with positive marginal probability for every type, (1) a profile is a strategy profile; (2) a deviator is a player-type pair; (3) an allowed deviation changes only that player’s action at that type; (4) the value is the corresponding interim expected payoff.

Suppose instead each concept is written directly. Nash equilibrium becomes `∀ i a', g.payoff i (update s i a') ≤ g.payoff i s` while interim equilibrium is `∀ i θ a', interim b σ i θ (updateAt σ i θ a') ≤ interim b σ i θ`. While each is fine on its own, proving that an equilibrium is a profile of best responses becomes tedious: The Nash proof unfolds the first quantifier; the interim proof cannot reuse it, because the predicates share no common form, so it is written again against the second quantifier; and so on. Every later result about equilibrium as such, from existence under continuity to the report-deviation characterization, is similarly troublesome.

Applying P2 provides a shared structure such that the deviation is a named field of the specialization. The `IsEquilibrium` predicate is defined using the specialization's `deviation` field.

### P3. Compose high-level concepts from library primitives

Compose high-level economic concepts through shared library primitives rather than by assembling the same ingredients afresh in each application. When a concept is built from shared parts, it naturally interoperates with everything else built from them and is able to use lemmas proved elsewhere in the library. A theorem about a quasilinear agent's expected payoff, for example, should be stated in terms of the library's mechanism, environment, and probability law, so that it applies to every model expressed in those terms.

Develop one integrated library rather than parallel foundations for microeconomics,
macroeconomics, and econometrics. As a strong default for future code,
project-owned declarations should share one top-level Lean namespace, with
nested namespaces for organization; no particular second-level division by
field is prescribed. Define shared economic objects once and reuse them across
applications. Specialized modules may add distinct concepts or explicit
bridges, but should not duplicate a foundation merely because an application
belongs to another field. This direction does not itself rename existing
declarations; any migration requires separate review.

Carrier types—the agents, types, actions, and outcomes—should be explicit parameters of a primitive rather than fields of it. If a mechanism and an environment each carried their own agent type as a field, combining them would require a hypothesis that the two fields are equal and every reference to an agent would be cast across that equality. As parameters, both objects mention the same `I`, and the type checker identifies them with no proof obligation.

Some carriers necessarily depend on ambient structure: a `ProbabilityMeasure α` depends on a measurable space on `α`. In that case the API should establish one canonical ambient instance and avoid accepting a competing structure on a derived carrier such as a profile space. This prevents instance-sensitive types and artificial restrictions on results that do not use the supporting structure.

The set of primitives will grow with the library. Extract a reusable component
when it has a second consumer, supports a theorem shared across applications,
or separates an optional condition from a stable underlying object. That a
component can be named or interpreted on its own is evidence of possible reuse,
but is not by itself a reason to add it to the public vocabulary.

Reuse Mathlib directly for mathematical concepts it already represents adequately. Introduce an economic primitive when it contributes economic semantics, an interface, or a distinct collection of laws, not merely a new name for an existing construct. When a mathematical concept has a different established name in economics, keep the economic name as a thin alias or notation over the Mathlib definition. An economist-facing name can be useful even when it adds no mathematical structure, but it must not require an independently maintained definition or a duplicate theorem family.

#### Example

Recall the `Mechanism` from P1. Two further primitives complete the vocabulary: An environment that records how agents value outcomes and a probability law over type profiles. All three take the same carriers as explicit parameters, which is what lets them combine.

```lean
/-- Outcome values in a quasilinear environment, allowing interdependent values. -/
structure QuasilinearEnvironment (I : Type*) (Θ : I → Type*) (O : Type*) where
  /-- An agent's value for an outcome at the true type profile. -/
  value : I → Profile Θ → O → ℝ
```

Notice that the law is Mathlib's `ProbabilityMeasure` with no wrapper since a wrapper would add no economic content. Meanwhile, the environment is a new primitive because value at the true type profile provides economic semantics.

A direct mechanism `M : Mechanism I Θ O` and an environment `env : QuasilinearEnvironment I Θ O` share `I`, `Θ`, and `O`, so an agent's payoff is defined once from both:

```lean
/-- An agent's quasilinear payoff from a mechanism's outcome and transfer. -/
def Mechanism.utility {I : Type*} {Θ : I → Type*} {O : Type*}
    (M : Mechanism I Θ O) (env : QuasilinearEnvironment I Θ O)
    (i : I) (θ a : Profile Θ) : ℝ :=
  env.value i θ (M.outcome a) + M.transfer i a
```

Interim expected utility integrates this payoff under a law `μ : ProbabilityMeasure (Profile Θ)`, using the measurable structure induced by the agents' type spaces, and Bayesian incentive compatibility is a predicate on that expectation. Each layer is defined once and takes the previous layers as arguments. The same environment and law can be paired with several mechanisms, and the same mechanism can be studied under several laws.

The alternative is a single record for a Bayesian auction with fields for values, the prior, the allocation rule, and payments. Revenue equivalence compares two mechanisms in one environment, so it needs two such records together with a hypothesis that their value and prior fields coincide, and every lemma about utility is proved against that record rather than against the mechanism. A deterministic comparison that needs no prior must either carry an unused field or introduce a second record and a second copy of every lemma.

With the shared vocabulary, a single-parameter revenue-equivalence statement binds one environment and one law, then quantifies over two mechanisms with those carriers.

### P4. Match representation to logical role

A declaration intended to be a predicate, such as `IsProperty`, must return `Prop`. If downstream definitions use a particular price, density, kernel, strategy, relation, or other selected component, that component belongs in an explicit argument or a structure in `Type`, together with the laws it must satisfy. A proposition may instead assert that such a witness exists when every conclusion is independent of which witness is chosen.

Keeping proposition and data separate makes the library much easier to use. For example, a structure exposing a selected value has sort `Type`, so it cannot directly serve as the membership condition of a `Set`, the body of an existential proposition, or the argument of negation.

For a declaration that does return `Prop`, marking it as a typeclass makes a further API commitment: Consumers may omit its proof and expect typeclass search to recover it. Use a class only when automatic recovery from the surrounding context is intended and supported by a small, predictable collection of instances. Otherwise use an ordinary predicate.

Mathlib follows both distinctions. `ContinuousMap X Y` and `ProbabilityMeasure Ω` are structures in `Type` that carry chosen maps or measures, whereas `Continuous f` and `IsProbabilityMeasure μ` state properties of already supplied objects. Among propositions, Mathlib uses classes for ambient or routinely propagated properties such as `CompactSpace X`, `SigmaFinite μ`, and `IsProbabilityMeasure μ`. It leaves `Continuous f`, `Measurable f`, `Integrable f`, and `Monotone f` as ordinary propositions, with closure theorems and specialized automation such as `fun_prop` and `measurability` rather than general typeclass search.

#### Examples

Suppose a menu assigns a quantity and a payment to each action. A chosen unit price, together with evidence that it describes every payment, is data:

```lean
/-- A selected unit price representing a menu's payments. -/
structure UnitPriceSpec {Action : Type*}
    (quantity payment : Action → ℝ) where
  /-- The price per unit of quantity. -/
  price : ℝ
  /-- Every action's payment is its quantity times the unit price. -/
  payment_eq : ∀ a, payment a = price * quantity a

/-- The menu's payments admit a constant unit price. -/
def HasUnitPrice {Action : Type*}
    (quantity payment : Action → ℝ) : Prop :=
  Nonempty (UnitPriceSpec quantity payment)
```

A consumer that computes with a particular price takes `s : UnitPriceSpec quantity payment` and uses `s.price`. A claim that some price exists uses `HasUnitPrice quantity payment`, which can occur in a set membership condition, existential proposition, or negation. Naming the data-bearing structure `IsUnitPrice` or declaring it as a class would not turn its selected price into a proposition.

Incentive compatibility illustrates the second decision. It is a property of a particular menu or mechanism, so establishing it is normally part of the mathematical argument. Its transport rules depend on the deviation domain, equilibrium notion, and conditions such as surjectivity or domination, so they do not form a small background inference system. In the design illustrated here, one should therefore define `IsIC` as an ordinary predicate and pass IC hypotheses explicitly rather than asking typeclass search to prove them.

> **Current-library note.** The proposed general affine-menu foundation follows
> the ordinary-predicate default. `SingleParameterProblem` retains its IC class
> chain, which supplies automatic implications and forward transport through
> `reduce`. Replacing classes with predicates and expressing the IC flavors as
> one optimality condition over deviation sets are separate, undecided
> migrations. Each requires its own design issue and an analysis of downstream
> call sites and API pins; P4 does not change the existing API.

### P5. Make changes of representation explicit

When one economic object is another object expressed through different inputs or at a lower level of detail, provide a means to construct the derived object from the original through an explicit, reusable transformation rather than declaring it independently. Give the transformation identity and composition laws so that successive changes of representation remain coherent.

This prevents parallel APIs for the same underlying object. It also allows theorems to be reused between concepts connected by the transformation: Preservation lemmas carry results from the original object to the derived representation, while reflection lemmas state the additional conditions under which results can be carried back. Without a shared transformation, each pair of representations requires bespoke bridge theorems, and their independently stated definitions can drift apart.

#### Example

An indirect mechanism accepts action profiles. Given a strategy that converts each new input into an action, precomposition produces the induced mechanism:

```lean
/-- Precompose a mechanism with each agent's change of action representation. -/
def Mechanism.comap {I : Type*} {A : I → Type*} {B : I → Type*} {O : Type*}
    (M : Mechanism I A O) (σ : ∀ i, B i → A i) : Mechanism I B O where
  outcome b := M.outcome (fun i => σ i (b i))
  transfer i b := M.transfer i (fun j => σ j (b j))
```

This operation has the laws `M.comap (fun _ a => a) = M` and `(M.comap σ).comap τ = M.comap (fun i c => σ i (τ i c))`. Identity and composition lemmas expose these laws to consumers.

For example, let `M` be a first-price auction whose inputs are bids and let `β` be a bid schedule mapping each agent's value to a bid. Its direct value-report representation is `M.comap β`: truthful reporting in the derived mechanism produces exactly the outcomes and transfers obtained by playing `β` in the original auction. The construction is meaningful for any bid schedule; an equilibrium hypothesis is needed when drawing incentive conclusions.

The map also records the limit of this reuse. `M.comap σ` observes `M` only on action profiles in the range of `σ`; two mechanisms that differ only off that range induce the same mechanism. Properties shown to be preserved therefore descend along `comap`, but reflecting a property back to the original mechanism requires an additional condition such as surjectivity or a theorem showing that off-range actions are dominated. The same discipline applies to other changes of representation, such as pushing a probability law forward or replacing an outcome lottery by its marginal allocation probabilities.

### P6. Distinguish total Lean operations from partial economic concepts

Lean and Mathlib deliberately make many mathematically partial operations total. This is logically harmless: Defining division by zero or assigning zero to the Bochner integral of a nonintegrable function does not allow one to prove `False` in Lean.

However, totalization carries semantic risk because a totalized term can appear to be a meaningful economic quantity. A nonintegrable payment stream can therefore receive the real value zero from the integral and be presented as an expected payment; a virtual-value formula can return a real number where its density denominator is zero; and so on. Statements about these terms may be correct Lean theorems even though their expected-payment, virtual-value, or interim-payoff interpretations are invalid in those cases.

To prevent this, low-level definitions may expose totalized operations when their names and documentation make this clear, but a public theorem asserting their economic meaning must carry or derive the appropriate conditions.

Whenever possible, formulate the economic result without the partial operation. For a cumulative distribution function `F` and a chosen density `f`, the weight `w(θ) = θ f(θ) - (1 - F(θ))` avoids the division in `φ(θ) = θ - (1 - F(θ)) / f(θ)`. The factorization `w(θ) = f(θ) φ(θ)` holds wherever the density is nonzero; an expected-revenue interpretation also requires the relevant distributional and integration hypotheses.

Likewise, ex-ante incentive constraints can compare expected utilities without selecting conditional payoffs at each individual type. An interim formulation must specify its conditional payoff object and whether its claims hold pointwise or almost everywhere. An equivalence theorem between these formulations must justify the conditioning and deviation arguments it uses.

In general, prefer formulations that do not require arbitrary choices on null events when they express the intended economic claim. When a claim requires beliefs or incentives at every type, supply the relevant belief specification explicitly and distinguish it from an almost-everywhere or ex-ante formulation.

### P7 (provisional). Provide a usable interface, not only a general definition

A reusable abstraction should provide the lemmas and constructions needed to use it without repeatedly unfolding its implementation. Generality is valuable when familiar applications can recover their natural statements through a small, predictable interface.

Providing an interface does not mean maximizing the number of public
declarations. Expose the semantic evaluation, identity, composition,
economics-relevant characterization, extensionality, and bridge lemmas that
make ordinary downstream use natural. Do not publish projection or
definitional-equality lemmas merely because they are easy to state. A theorem
proved by `rfl` may nevertheless be valuable when it records a genuine
semantic contract of a construction.

Choose `@[simp]` rules deliberately so that routine economic expressions have
a stable normal form. A lemma should not be marked `@[simp]` when it does not
advance simplification toward that form or when it creates competing rewrite
directions.

Downstream proofs should ordinarily depend on this interface rather than on
the arrangement of fields or the implementation of supporting definitions.
Test intended clients through the documented umbrella import: importing a leaf
or implementation module directly can conceal a missing export or an
unintended public dependency. Elaborator behavior, typeclass search,
simplification, and proof-checking cost are part of whether an abstraction is
usable.

This follows Mathlib's guidance to provide API lemmas rather than make consumers depend on unfolding, and to consider performance when changing definitions, instances, or simplification rules.

#### Examples

Defining BIC through truthful equilibrium should be accompanied by a theorem characterizing it through the familiar report-deviation inequalities. An auction proof should not need to unfold the induced game, the Bayesian equilibrium definition, and `EquilibriumProblem` to establish an incentive constraint.

Likewise, `Mechanism.comap` should have evaluation, identity, composition, and appropriate preservation lemmas, so downstream proofs can work with its economic behavior directly.

### P8 (provisional). Validate abstractions with representative instances and boundary cases

A foundational abstraction should be evaluated by constructing representative
instances and using it to state and prove representative results. An example
that only constructs the input to a headline theorem establishes that its
hypotheses are satisfiable, but does not validate the advertised conclusion.
Apply the theorem and expose its economic content. A definition that appears
general in isolation may still make ordinary applications difficult or conceal
unintended restrictions.

The validation burden should match the generality advertised. A major
foundation whose value lies in serving different settings should, when
practical, include both a standard application and a materially different one.
A small leaf contribution need not add two elaborate examples. Where relevant,
include boundary cases that distinguish constitutive conditions from theorem
hypotheses or expose the limits of a transformation. Cross-check an independent
formula when one is readily available. These examples should be maintained as
checked clients of the public interface.

Use small counterexamples to record important limits of implications and representation changes. Examples complement proofs: They help establish that the formal definitions and theorem statements capture the intended concepts.

#### Examples

A mechanism abstraction should be exercised by a prior-free auction result and, if its stated scope includes them, a non-auction mechanism or an asymmetric action space.

The affine-menu API should include a case demonstrating why type-dependent deviation sets require additional hypotheses for monotonicity. The `comap` API should include a case showing why a property of the induced mechanism need not hold for actions outside the map's range.

## Illustrative architectural designs

The following examples combine the principles into prospective APIs for
mechanisms, equilibrium, and single-parameter choice problems. They do not
duplicate current source documentation; the repository source remains
authoritative for exact names, fields, and statements.

### Separate mechanisms, environments, and priors

The mechanism from P1 and environment from P3 determine realized utility once a true type profile and an action profile are supplied:

```lean
/-- Realized quasilinear utility at true types and reported actions. -/
def Mechanism.utility {I : Type*} {A : I → Type*}
    {Θ : I → Type*} {O : Type*}
    (M : Mechanism I A O) (E : QuasilinearEnvironment I Θ O)
    (θ : Profile Θ) (a : Profile A) (i : I) : ℝ :=
  E.value i θ (M.outcome a) + M.transfer i a
```

The sign convention is fixed such that a positive transfer is money received by the agent, payment is its negative, and revenue is the sum of payments when that sum is defined. Keeping one signed transfer avoids independently maintained payment and transfer rules.

These objects do not require agents to be finite, values to be private, or types to follow a particular law. This allows a finite welfare theorem to request the instances needed for finite sums, a private-value specialization to require an agent's value to depend on the true type profile only through that agent's own type, and a Bayesian theorem to take a prior `μ : ProbabilityMeasure (Profile Θ)` together with the measurability and integrability conditions needed for its expectations.

Dominant-strategy incentive compatibility (DSIC), Bayesian incentive compatibility (BIC), and individual rationality are ordinary predicates on the relevant objects. A theorem about individual rationality also supplies the reservation utility being compared. Selected data such as a prior, density representative, reservation utility, or tie-breaking rule remain explicit arguments or structures in `Type`.

This design applies P1 by separating constitutive data from assumptions for particular results, P3 by making the environment and prior reusable, P4 by separating data from properties, and P6 by establishing integrability where an integral acquires an economic interpretation.

### Derive direct mechanisms and equilibrium notions

A direct mechanism specializes the action spaces to the agents' type spaces:

```lean
/-- A mechanism whose action spaces are the agents' type spaces. -/
abbrev DirectMechanism (I : Type*) (Θ : I → Type*) (O : Type*) :=
  Mechanism I Θ O
```

Given a mechanism `M` and a strategy profile `σ : ∀ i, Θ i → A i`, the transformation from P5 produces the direct mechanism `M.comap σ`. Truthful reporting is the strategy `fun _ θ => θ`. Its outcome and transfers agree with those of `σ` in `M` by construction.

An induced Bayesian game combines the mechanism, environment, prior, and admissible strategies. It can instantiate `EquilibriumProblem` by supplying strategy profiles, deviators, admissible deviations, and the corresponding expected utilities. Bayesian incentive compatibility then states that truthful reporting is an equilibrium in the chosen formulation. Characterization theorems expose the familiar report-deviation inequalities.

For a revelation argument, a report deviation in the induced direct mechanism must give an admissible deviation in the original mechanism with the same payoff. In a measurable model, this includes verifying the required measurability and integrability. These are the hypotheses of an equilibrium transport theorem, allowing a result about `σ` to imply a result about truthful reporting.

The reverse direction requires separate justification. `M.comap σ` observes only actions in the range of `σ`. Equilibrium against report deviations therefore does not by itself rule out profitable off-range actions in `M`. A reflection theorem must supply an appropriate lifting property, such as surjectivity with admissible lifts, or show that omitted actions cannot improve the payoff.

This design applies P2 by defining equilibrium once and providing familiar specializations, P4 by keeping BIC as an ordinary proposition, and P5 by giving each change of action representation an explicit construction and a stated transport contract.

### Share affine menus across bidding and screening problems

A bidder choosing a bid and a consumer choosing a contract can face the same mathematical problem: Select an action with utility affine in a scalar type. Their shared core is an affine menu:

```lean
/-- A menu whose utility is affine in a one-dimensional type. -/
structure AffineMenu (Action : Type*) where
  /-- The type coefficient associated with each action. -/
  quantity : Action → ℝ
  /-- Net money received by the agent after choosing an action. -/
  transfer : Action → ℝ

/-- Type `θ`'s utility from choosing action `a`. -/
def AffineMenu.utility {Action : Type*}
    (M : AffineMenu Action) (θ : ℝ) (a : Action) : ℝ :=
  θ * M.quantity a + M.transfer a

/-- A strategy is feasible and optimal among each type's available deviations. -/
structure AffineMenu.IsOptimalOn {Action : Type*}
    (M : AffineMenu Action)
    (T : Set ℝ)
    (D : ℝ → Set Action)
    (σ : ℝ → Action) : Prop where
  /-- Each type's selected action is available to that type. -/
  feasible : ∀ θ ∈ T, σ θ ∈ D θ
  /-- No available action gives greater utility than the selected action. -/
  optimal : ∀ θ ∈ T, ∀ a ∈ D θ,
    M.utility θ a ≤ M.utility θ (σ θ)
```

The type domain, deviation correspondence, and selected strategy are arguments because they can vary while the menu remains fixed. A single-item allocation interpretation constrains the quantity to `[0, 1]`; an arbitrary affine choice problem need not. Real-valued bidding specializes `Action` to a bid space, while screening can use a space of contracts. Both reuse theorems about the same menu and optimality predicate.

The theorem hierarchy follows the mathematical dependencies:

```text
optimality on the menu
  + cross-type availability of the selected actions
  → supporting inequalities and monotone selected quantity
  + interval type domain and regularity
  → envelope and payment identities
  → deterministic revenue equivalence
  + probability law and integrability
  → expected payment
  + chosen density
  → virtual surplus
```

Each step supplies the assumptions it uses. In particular, comparing the choices of two types requires each selected action to be available to the other type, as holds for a common feasible menu. Optimality with an arbitrary type-dependent deviation correspondence alone does not imply monotonicity. Envelope results require the appropriate interval and regularity hypotheses, and expected-payment results require integrability.

An expected-payment theorem stated under a general probability law can accommodate atoms. A density representation supplies additional structure for a virtual-surplus corollary; a quotient virtual value also needs the nonzero-density condition for its economic factorization. Precomposing the menu's quantity and transfer functions handles changes of action representation, with the same preservation and reflection discipline as P5.

This design applies P1 to keep allocation and distribution assumptions out of the affine core, P2 and P3 to share theorems and primitives across applications, P4 to keep optimality hypotheses explicit, P5 to relate action representations, and P6 to introduce density and division with their validity conditions.

## Provenance

Daniel Lyng drafted these principles in the original discussion on
[issue #60](https://github.com/AxiomMath/auctionlib/issues/60) and developed the
version imported here in [his design-principles
gist](https://gist.github.com/danlyng/1fc6bf249436782e1e00b99c3ff6ce5e).
Comments from Scott Kominers on issue #60 motivated several revisions. Later
refinements reflect the review practice recorded in
[issue #72](https://github.com/AxiomMath/auctionlib/issues/72).
