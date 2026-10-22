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

Use strict preferences over a proposer's own contracts and the outside option,
and unrestricted receiving-side choice functions. Reuse the existing
`Market.ofSellerPreferences`, `ChoiceFunction`, incidence maps, and stability
predicates. Do not require substitutability, IRC, LAD, or feasible holdings in
the process data. These conditions belong to individual results.

The initial economic scope is unit-demand proposing sellers and accepting
buyers. A completely abstract proposal oracle would admit procedures that
do not follow proposers' preferences; it should not replace the canonical
economic definition. Extract a more general helper only if a second consumer
needs it. Ties and many-to-many proposing behavior are separate extensions.

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
states by an invariant about descending proposals and previously offered
contracts. Repeated held offers disappear under the cumulative-set projection.
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
`seller : X → S` and `buyer : X → B`. Preferences use the existing strict
ordering of `Option {x : X // seller x = s}`, with `none` the outside
option. Document the library's ordering orientation at the implementation site.

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

For a proposer s, let `U_s(A)` be its acceptable contracts outside A.
It is eligible when no contract of s belongs to H(A) and U_s(A) is nonempty.
A valid offer is its unique best member of U_s(A).

A productive batch Q is nonempty, contains only valid offers by eligible
proposers, and contains at most one offer per proposer. The step is
`A' = A ∪ Q`. All eligibility and best-offer tests in a batch use the same
pre-step state. Recompute holdings from A'.

Use sets in the semantic relation. Availability of a best remaining contract
must be explicit on infinite domains; nonempty does not imply a greatest
element. Finite contracts supply this fact without finiteness of either agent
type. Do not interpret a total choice constructor's empty fallback on a
non-maximizing infinite menu as economic exhaustion.

Provide policies selecting:

- One eligible proposer (sequential).
- Every eligible proposer (simultaneous).
- Any nonempty subset of eligible proposers (general batches).

A policy may depend on the prior history. A fixed priority order is a convenient
instance, not the definition of a process. Require the chosen batch to be valid
whenever the state is nonterminal.

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
canonical outcome that suppresses the policy parameter. Keep the policy-indexed
interface available for domains without independence.

Reports vary the proposer preference profile; receiving choices and incidence
maps are fixed parameters of the relevant mechanism. Reuse the existing
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
| Source views | Reachability and strict-preference invariants; explicit locality bridges. |
| Sequential feasibility/stability | Audit the precise bilateral/unilateral hypotheses and IRC in the source and existing library predicates. |
| Proposer optimality | Separate theorem under its own conditions; use the existing stable-outcome comparison. |
| Sequential order independence | State equality across the specific class of singleton policies covered by the proof. |
| Batch independence | Separate theorem quantifying over batch policies, with its own sufficient conditions. |
| Ordinary DA comparison | Explicit map to the existing deferred-acceptance operator and its initialization; substitutes/IRC as required. |
| Mechanism and incentives | Feasibility for the report domain, then independence and incentive hypotheses as needed. |

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

## Implementation sequence and acceptance checks

1. **Core and sequential process.** Tentative module
   `Matching/Contracts/CumulativeOffer/Basic.lean`: own-menu holdings,
   eligibility, valid batches, labeled runs and terminal outcomes.
   `Termination.lean`: finite progress bounds and policy execution.
   Deliver a usable singleton policy and small concrete examples.
2. **Source specializations.** Tentative `Presentations.lean`: simultaneous
   policy, per-buyer projection, literal Hatfield–Milgrom view, and proved
   correspondence. Keep source assumptions explicit in docstrings.
3. **Economic results.** Separate feasibility, stability, optimality and
   independence results, with a source-to-hypothesis table updated as proofs
   land. Split files only where dependencies and size justify it.
4. **Completion comparison and mechanism adapter.** Complete the relevant
   #138 bridge, then expose a matching-valued mechanism. Coordinate history
   interfaces with #141 and report interfaces with #140.

Initial regression examples should exercise empty contracts, all-unacceptable
contracts, a rejected proposer making a second offer, two contracts between
the same proposer and receiver, re-selection of an earlier rejected contract,
and infeasible raw holdings under unrestricted choices. A small regular market
should run under both singleton and simultaneous policies. Include a public
umbrella-import client when Lean files are added.

For the first implementation, correctness means that the definitions and
termination proofs land without silently imposing economic regularity.
Later acceptance requires named source correspondence proofs and separately
scoped economic guarantees. A design document does not close #139 or #138.

## Decisions for review

- Approve strict proposer preferences with arbitrary receiving choices as the
  economic core, using the existing preference constructor.
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
