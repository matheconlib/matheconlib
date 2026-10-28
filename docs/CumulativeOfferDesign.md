# Cumulative offer processes and mechanisms: design proposal

Status: design only; no declarations or theorems below are implemented by this
document. This starts [#139](https://github.com/matheconlib/matheconlib/issues/139)
under [#136](https://github.com/matheconlib/matheconlib/issues/136), and prepares
the process-comparison work remaining in
[#138](https://github.com/matheconlib/matheconlib/issues/138).
Names and module boundaries are provisional.

## Recommended scope

Define one accumulated-offer transition relation, with explicit proposal
batches and histories. Expose sequential and simultaneous processes as named
specializations. Add source-specific views and correspondence theorems where
the papers use different state variables. Equality across schedules is a
theorem, not part of the definition.

Use weak preferences over a proposer's own contracts and the outside option,
with unrestricted receiving-side choice functions. Define admissible batches
relationally before selecting a policy. Policies may use history to select
proposers and resolve preference ties; fixed tie-breaking is a named
specialization. Reuse `ChoiceFunction`, incidence maps, and stability predicates;
bridge to `Market.ofSellerPreferences` through a strict refinement. Do not require substitutability, IRC, LAD, or feasible holdings in
the process data. These conditions belong to individual results.

The initial economic scope is unit-demand proposing sellers and accepting
buyers. A completely abstract proposal oracle would admit procedures that
do not follow proposers' preferences; it should not replace the canonical
economic definition. Extract a more general helper only if a second consumer
needs it. Many-to-many proposing behavior is a separate extension. General choice
correspondences with indifferences are tracked separately in
[#200](https://github.com/matheconlib/matheconlib/issues/200).

## Source distinctions and explicit projections

| Presentation | Source convention | Proposed interface |
| --- | --- | --- |
| Hatfield–Milgrom (2005), §V, system (14), pp. 928–929 | Simultaneous doctor choices; hospital offer sets accumulate. Held offers may be repeated. | All-eligible fresh-offer policy plus a view of the literal recurrence. |
| Hatfield–Kojima (2010), §2.3, p. 1710 | One currently unheld doctor offers at each step; the receiving hospital chooses from its accumulated offers. | Singleton-batch policy and a projection to per-hospital menus. |
| Bó–Kratz–Shimoji (2024), §3 | A nonempty subset of eligible doctors can propose together. | Motivation for the shared batch relation. |

For the Hatfield–Milgrom view, write their cumulative hospital menu as
`A(t)`, aggregate hospital choice as `C_H`, and rejection as
`R_H(A) = A ∖ C_H(A)`. Their recurrence is

```text
A(0) = ∅
D(t) = X ∖ R_H(A(t−1))
A(t) = A(t−1) ∪ C_D(D(t))
```

The fresh-offer formulation must be related to this recurrence on reachable
states by an invariant about descending proposals under the fixed strict
refinement and previously offered contracts. Repeated held offers disappear under the cumulative-set projection.
Do not claim definitional equality on arbitrary states. Their Theorem 15
compares cumulative offers with their generalized deferred acceptance under
substitutes; it is not itself a sequential-versus-batch independence theorem.

For Hatfield–Kojima, singleton steps should preserve every other buyer's menu
and holdings. Prove that projection directly. Their preference-based model
supplies receiving-side rationality properties that our raw choice interface
does not assume. The source also warns that unrestricted choices may produce
an infeasible final set. Source correspondence must state which assumptions
come from representation and which enter feasibility or stability.

These are two named instantiations/views of shared machinery, not two
independently maintained process foundations. Avoid the abbreviation “HK” in
public names: Hatfield–Kojima and Hirata–Kasuya are different references.

## Data, locality, and state

Let `X` be contracts, `S` proposers, and `B` receivers, with existing
`seller : X → S` and `buyer : X → B`. Preferences are complete, transitive weak relations on
`Option {x : X // seller x = s}`, with `none` the outside option.
Reuse the `CompletePreference` interface from #253 and the refinement API
from #206, coordinating with their landing rather than introducing a parallel
preference foundation. Keep preferences explicit and fixed during a run.
A fixed strict refinement, rather than the economic weak preference itself,
can be supplied to the existing linear-order constructor.

Separate scheduling from selection among tied best contracts. Both may depend
on history at the general policy level; neither may override strict economic
preferences. For the fixed-tie-breaking specialization, for own contracts,
the refinement ranks x above y exactly when x is strictly preferred, or when
x and y are indifferent and the fixed tie-break prioritizes x. The full
refinement includes the outside option. The baseline convention puts the
outside option ahead of contracts tied with it, so only strictly acceptable
contracts are offered. An adapter allowing such contracts must specify their
placement explicitly; a contract-only offer order cannot determine that.

Prove that proposing a weakly best remaining acceptable contract and resolving
ties by this fixed order coincides with proposing under the strict refinement.
Strict economic preferences are a specialization in which contract tie-breaking
has no effect. Document the library's comparison orientation at implementation.

The semantic state is the accumulated offer set `A : Set X`. Start at the
empty set. Define the own-buyer menu and holdings by

```text
A_b = {x ∈ A | buyer x = b}
H_b(A) = choiceB b A_b
H(A) = ⋃ b, H_b(A)
```

Holdings are derived data. Do not store a second independently mutable holding
set. In particular, retain rejected offers in A: without extra conditions a
receiver may choose a previously rejected contract again.

**Locality decision:** evaluate each buyer on its own menu. Existing market
support alone does not rule out choices depending on other buyers' contracts.
Prove agreement with the existing global-menu aggregation under `Market.Local`;
use the existing IRC-to-locality bridge where applicable. Do not silently
identify these expressions for an arbitrary `Market`.

The state and raw terminal output have type `Set X`, not a feasible-matching
subtype. Even if every buyer selects at most one contract per seller, different
buyers can simultaneously hold contracts with the same seller. Feasibility is
an obligation of the matching-valued adapter.

## Offers, steps, histories, and termination

For a proposer s, let `U_s(A)` be its strictly acceptable contracts outside A.
It is eligible when no contract of s belongs to H(A) and U_s(A) is nonempty.
An admissible offer is a greatest element of U_s(A) under its weak preference:
it is at least as good as every other remaining acceptable contract.
This relation allows all tied best contracts; it does not select one.

A valid productive batch Q is nonempty, contains only admissible offers by
eligible proposers, and contains at most one offer per proposer. The step is
`A' = A ∪ Q`. Every test uses the same pre-step state. Holdings are then
recomputed from A'. Validity and runs are relational; determinism is additional
policy data, not part of the definition of a process.

A history-dependent policy selects a valid batch at each nonterminal valid
history. Equivalently it selects a nonempty subset of eligible agents and one
admissible contract for each selected agent. Use this equivalence as an adapter,
rather than maintaining two independent process definitions. In the contract-set
representation, the participating agents are the seller image of the batch.

The history determines A, which determines holdings, availability, and
eligibility. Do not store these as independently mutable policy inputs.
A state-dependent policy factors through A: two valid histories with the same
accumulated offers receive the same batch. Provide the lift of a state policy
to a history policy and the corresponding agreement of runs.

Expose the following specializations, combining restrictions where appropriate:

| Policy | Restriction |
| --- | --- |
| History-dependent batches | Any valid batch selected from the history |
| State-dependent batches | The batch depends only on accumulated offers |
| Simultaneous | Exactly one admissible offer from every eligible agent |
| Sequential | Exactly one admissible offer overall |
| Fixed tie-breaking | Each selected agent uses its fixed strict refinement |
| Fixed contract-order sequential | Choose the highest-priority admissible contract globally |

Simultaneous and sequential restrictions alone do not resolve preference ties.
A deterministic constructor supplies the corresponding selector. General
history-dependent selection includes changing priorities among tied best
contracts; fixed tie-breaking is the standard specialization for source
correspondence and scheduling-independence results. Changing scheduling and
changing tie-breaking are different operations.

The HKW-style fixed-contract-order specialization uses one fixed order Γ on X.
Form the union of all eligible agents' weakly best remaining acceptable
contracts, and select its Γ-first member. This simultaneously resolves contract
ties and selects the proposing agent. Priority never overrides an agent's
strict preference. Its weak-preference version is an extension, not an assertion
that HKW's original model permits ties. Also provide a fixed-priority
simultaneous rule that takes each eligible agent's Γ-first admissible contract.

Use sets in the semantic relation. On infinite domains, eligibility need not
supply a greatest remaining contract, and a priority order need not attain a
first element. Policy existence therefore needs explicit attainment hypotheses;
absence of a valid batch is not automatically economic exhaustion. Finite
contracts supply the needed attainment without finiteness of either agent type.
Use #258's attainment and outside-option bridges on the actual own-contract
menus, including attainment under refinement. Do not interpret a total choice
constructor's empty fallback as voluntary nonparticipation.

Retain batch labels in a run. Its accumulated-set projection forgets order and
batch boundaries; it cannot replace the history interface needed for observable
conditions. Singleton runs should project to a list of distinct offered
contracts. Batch runs retain their partition into rounds. Flattening a batch
with an arbitrary order need not produce a valid sequential run.

First prove monotonicity of A, strict growth at every productive step, no
contract offered twice, and the relation between run length and offers.
With finite X, every productive run has at most |X| steps, and a policy valid
at every nonterminal state reaches a terminal state. No fairness assumption
is needed: finite fresh offers plus nonempty progress suffice.

Terminal means that no unheld proposer has an acceptable unoffered contract.
A total iteration may stutter at terminal states, but those repetitions must
not count as productive steps. Empty markets and universal unacceptability
terminate immediately.

An executable implementation is later work: `Fintype`, decidable equality,
computable choices, and computable preference comparisons are additional
requirements, not consequences of a noncomputable finite existence proof.

## Outcome and mechanism layers

Expose the terminal outcome relation before selecting a schedule. For a fixed
valid deterministic policy on finite contracts, construct a policy-indexed raw
outcome function. This function still returns a set of contracts.

Promote it to a matching-valued allocation rule only after proving feasibility
for every report in its stated domain. An independence theorem then permits a
canonical outcome on the fixed-refinement specialization that suppresses the
scheduling-policy parameter while retaining the preference refinement. Changing tie-breaking can change the
outcome, even for one proposer indifferent between two accepted contracts.
Independence from scheduling is not independence from tie-breaking. Keep the policy-indexed
interface available for domains without independence.

Reports vary the proposer preference profile; receiving choices and incidence
maps, scheduling rule, and tie-selection rule are fixed parameters of the
relevant mechanism (a fixed rule may still depend on its input history). Reuse the existing
mechanism infrastructure, with zero monetary transfers where appropriate.
An allocation rule alone is not a strategy-proofness theorem: report domains,
true preferences, outcome evaluation, and deviations belong to
[#140](https://github.com/matheconlib/matheconlib/issues/140).

## Theorem boundaries and dependency order

The following are proof targets, not claims that this draft establishes them.

| Layer | Scope or assumptions to expose |
| --- | --- |
| Step invariants | Choice containment, incidence support, valid fresh offers; no substitutes or IRC. |
| Finite termination | Finite contracts and valid nonempty scheduling; best offers exist. |
| Source views | Weak-preference/refinement correspondence, reachability and refined-order invariants; explicit locality bridges. |
| Sequential feasibility/stability | Audit the precise bilateral/unilateral hypotheses and IRC in the source and existing library predicates. |
| Proposer optimality | Separate theorem under its own conditions; use the existing stable-outcome comparison. |
| Sequential order independence | Hold tie-breaking fixed; state equality across the specific class of singleton scheduling policies covered by the proof. |
| Batch independence | Hold tie-breaking fixed; separate theorem quantifying over batch policies with its own sufficient conditions. |
| Ordinary DA comparison | Explicit map to the existing deferred-acceptance operator and its initialization; substitutes/IRC as required. |
| Mechanism and incentives | Feasibility for the report domain, then independence and incentive hypotheses as needed. |

With weak economic preferences, stability and incentive statements must specify
their interpretation. Stability under a strict refinement is not automatically
strong or super-stability under the weak relation; use an explicit transfer
theorem for the intended blocking notion. Proposer optimality and incentives
likewise require their own weak-domain statements and fixed exogenous
tie-breaking conventions.

Hirata–Kasuya (2014) gives an order-independence result under bilateral
substitutes and IRC; its abstract was checked, but its complete proof remains
to be audited before reproducing a theorem statement in Lean.

Bó–Kratz–Shimoji distinguish sequential observable conditions from conditions
covering batch histories (§§4–5). Thus
[#141](https://github.com/matheconlib/matheconlib/issues/141) must specify the
histories over which each condition quantifies. A sequential theorem cannot
be advertised as batch independence merely because both use the same state.
Their stronger batch results are a reference for later work, not prerequisites
for landing the raw definitions.

## Connection to completions

The merged completion reduction supplies stable existence and transfer of
completed-market stability to the original market. It does not yet identify
a cumulative-offer selection or prove completion independence.

A useful sufficient process bridge would assume equality of original and
completed buyer choices on all relevant reachable menus. This yields equality
of holdings, eligibility, and subsequent steps under a common policy. However,
completion agreement on feasible menus does not by itself supply that
hypothesis: accumulated menus can contain multiple contracts with one seller.

The actual completion comparison must therefore prove a reachable-menu lemma
using the completion definition and applicable weak-substitutes conditions,
or establish outcome equivalence by another argument. It must also align
proposal policies and locality conventions. Record this as a substantive proof
obligation for #138, not an automatic corollary of terminal feasibility.
Do not infer original-market proposer optimality solely from completed-market
optimality and one-way stability transfer.

## Existing preference API and scope boundary

The current `Choice/Induced.lean` constructors `ofBundleOrder`,
`ofSetLinearOrder`, and `ofOptionLinearOrder` require `LinearOrder`;
so do `bestOption` in `Choice/FiniteOption.lean` and the feasible-bundle
constructor in `Choice/Matching/Preferences.lean`. They do not represent ties
between distinct alternatives. Their use of weak comparisons does not remove
antisymmetry.

The raw `ChoiceFunction` structure imposes only containment. It can encode
a set of maximizing individual alternatives, but under the matching
interpretation its output is one held bundle. A family of tied optimal bundles
requires a correspondence or equivalent relational interface. Simply weakening
the order in the current existential bundle formula would union all optimal
bundles, potentially destroying feasibility and optimality.

[#200](https://github.com/matheconlib/matheconlib/issues/200) tracks weak
preference-induced choice, correspondences, selection bridges, and
utility/transfer examples, coordinated with the preferences-port issue
[#161](https://github.com/matheconlib/matheconlib/issues/161).
These general choice results are developed outside #139. The active #253,
#206, and #258 stack now supplies preference, refinement, and attainment
interfaces for the process to reuse. Coordinate integration with that stack;
do not duplicate its definitions or require the whole #200 roadmap to finish.

## Implementation sequence and acceptance checks

1. **Core and sequential process.** Tentative module
   `Matching/Contracts/CumulativeOffer/Basic.lean`: own-menu holdings,
   weak preferences, eligibility, relational admissible offers and valid batches,
   labeled runs and terminal outcomes. Add history policies, state-policy lifts,
   and sequential, simultaneous, fixed-tie-breaking, and fixed-order adapters.
   `Termination.lean`: finite progress bounds and policy execution.
   Deliver a usable singleton policy and small concrete examples.
2. **Source specializations.** Tentative `Presentations.lean`: simultaneous
   policy, per-buyer projection, literal Hatfield–Milgrom view, and proved
   correspondence. Keep source assumptions explicit in docstrings.
3. **Economic results.** Separate feasibility, stability, optimality and
   independence results, with a source-to-hypothesis table updated as proofs
   land. Split files only where dependencies and size justify it.
4. **Mechanism adapter and completion comparison.** Expose a policy-indexed
   matching-valued mechanism once feasibility holds on its report domain;
   completion independence is not a prerequisite for this adapter. Complete the
   separate #138 comparison. Coordinate history interfaces with #141 and report
   interfaces with #140.

Initial regression examples should exercise empty contracts, all-unacceptable
contracts, a rejected proposer making a second offer, two contracts between
the same proposer and receiver, tied acceptable contracts, a tie with the
outside option, refinement correspondence, re-selection of an earlier rejected contract,
and infeasible raw holdings under unrestricted choices. Exercise state-policy
lifts, history-dependent scheduling, history-dependent tie selection, and the
fixed-order adapter. Include an example where sequential and simultaneous
outcomes differ under unrestricted choices. A small regular market
should run under both singleton and simultaneous policies. Include a public
umbrella-import client when Lean files are added.

For the first implementation, correctness means that the definitions and
termination proofs land without silently imposing economic regularity.
Later acceptance requires named source correspondence proofs and separately
scoped economic guarantees. A design document does not close #139 or #138.

## Agreed generality and remaining review

- Use weak proposer preferences and arbitrary receiving choices. Define valid
  batches relationally, with history-dependent policies selecting agents and
  resolving ties. Fixed tie-breaking and strict refinements are specializations.
- Provide state-dependent, simultaneous, sequential, and fixed-contract-order
  specializations of the same process; prove their validity and run embeddings.
- Finite termination applies to all valid productive runs, including policies
  with history-dependent tie selection. Scheduling independence and classical
  source correspondence retain their separate fixed-refinement hypotheses.
- Review the outside-option convention and keep general choice with
  indifferences in #200.
- Approve own-menu receiver evaluation and explicit locality transport.
- Approve batch-labeled runs with sequential and simultaneous specializations,
  while prioritizing sequential proofs.
- Review the proposed reachable-state correspondence for the literal
  Hatfield–Milgrom recurrence before fixing the public API.
- Decide which independence theorem belongs in the first economic-results
  milestone; keep batch observable conditions out of the initial definition PR.

## References and audit status

- Hatfield, J. W., and P. R. Milgrom (2005), “Matching with Contracts,”
  *American Economic Review* 95(4), 913–935.
  [Published PDF](https://web.stanford.edu/~milgrom/publishedarticles/Matching%20with%20Contracts-AER.pdf).
  Checked §V, system (14), and Theorem 15.
- Hatfield, J. W., and F. Kojima (2010), “Substitutes and Stability for Matching
  with Contracts,” *Journal of Economic Theory* 145, 1704–1723.
  [Published-paper PDF](https://kylewoodward.com/blog-data/pdfs/references/hatfield%2Bkojima-journal-of-economic-theory-2010A.pdf).
  Checked the model and §2.3 process definition; theorem hypotheses require
  declaration-by-declaration audit during implementation.
- Hirata, D., and Y. Kasuya (2014), “Cumulative offer process is
  order-independent,” *Economics Letters* 124(1), 37–40.
  [Publisher page](https://www.sciencedirect.com/science/article/pii/S0165176514001360).
  Abstract checked; full proof audit pending.
- Bó, I., S. Kratz, and M. Shimoji (2024), “Generalized cumulative offer
  processes,” *Review of Economic Design*.
  [DOI](https://doi.org/10.1007/s10058-024-00350-4);
  [author PDF](https://inaciobo.com/files/BoKratzShimoji2024.pdf).
  Checked §§3–5 for batch semantics and the scope of observable conditions.
- Hatfield, J. W., S. D. Kominers, and A. Westkamp (2021), “Stability,
  Strategy-Proofness, and Cumulative Offer Mechanisms,” *Review of Economic
  Studies* 88(3), 1457–1502.
  [DOI](https://doi.org/10.1093/restud/rdaa052).
  Follow-up source for #140–141; this draft does not claim a completed
  theorem-level audit of its observable conditions.
