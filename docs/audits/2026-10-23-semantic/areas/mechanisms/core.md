> Historical concept assessment at the audited revision. The [publication and proof-scope record](../../README.md) and [repair/migration table](../../MIGRATION.md) distinguish confirmed findings from candidates and current repairs.

# Mechanism core and auction specification: semantic audit

Source revision: `1d9f8cc233cdaeee0364b51befb84feea657a4da`. All source was read without modification. This covers every module in `MathEconLib/Mechanism/`, including the two major annotated definitions absent from the initial inventory: `utilityGame` and `inducedBayesianGame`.

Verdict: no substantive false positive or false negative found under the documented scope. Deterministic mechanisms, quasilinear valuations with money received positive, unrestricted interdependent values, zero outside utility, and the explicit strict-highest/tie-discard allocation rule are meaningful restrictions and conventions.

## Declaration-to-concept map

All locations below are relative to `MathEconLib/Mechanism/`. “Equivalent” means both implications follow by unfolding, subject to the scope stated in the row; it does not claim a representation theorem for a more general economic model.

| Source location and declaration | Intended mathematical/economic concept | Both-direction assessment |
| --- | --- | --- |
| `Core/Profile.lean:33`, `Profile` | Agent-indexed dependent product of individual inputs | Equivalent: a dependent function is precisely one input of type `X i` for each agent. Empty index sets give the singleton empty profile. |
| `Core/Mechanism.lean:54`, `Mechanism` | Deterministic outcome rule plus agent-indexed monetary transfers | Equivalent for unrestricted deterministic mechanisms on the specified product action space. Feasibility belongs to the outcome type or separate predicates; random outcomes may be encoded in `O`, but the structure does not itself supply a probability kernel. |
| `Core/Mechanism.lean:65`, `DirectMechanism` | Direct revelation mechanism with report space equal to type space | Equivalent; directness is the report domain, while truthfulness is separately imposed. An arbitrary direct mechanism need not be IC. |
| `Core/Mechanism.lean:71`, `payment` | Amount charged to agent | Equivalent: `payment=-transfer`; a positive transfer is a receipt, so its payment is negative. |
| `Core/Mechanism.lean:78`, `revenue` | Designer's net monetary receipts from finitely many agents | Equivalent: `-sum transfer=sum payment`. It excludes production costs and any external source of income. |
| `Core/Environment.lean:60`, `QuasilinearEnvironment` | Outcome valuation at the full true type profile, with quasilinear money utility | Equivalent for an unrestricted valuation table `value i theta o`; no private-values, sign, or distributional restriction is hidden in the structure. |
| `Core/Environment.lean:70`, `IsPrivateValues` | Own-type dependence of each agent's outcome valuation | Equivalent: equality of own type forces equality of the entire outcome valuation function. Conversely an own-type valuation plainly has this invariance. If other type spaces are empty, the property is vacuous on unrealizable profiles, as is the economic comparison. |
| `Core/Environment.lean:74`, `ofPrivate` | Environment obtained from own-type valuation functions | Exact embedding: `value i theta o=v i (theta i) o`. Any own-type valuation specification maps here with the same values. |
| `Core/Environment.lean:94`, `utility` | Quasilinear utility evaluated at true types for actions actually played | Equivalent: true valuation of `M.outcome a` plus monetary receipt. Reports affect the outcome and transfer, not the fixed true type argument. |
| `Core/Environment.lean:110`, `totalValue` | Utilitarian social value excluding transfers | Equivalent for finitely many agents. Seller costs/value require inclusion in the environment if they are intended to enter welfare. |
| `Core/Environment.lean:117`, `welfareExcl` | Sum of all other agents' valuations | Equivalent: the erased finite set removes precisely agent `i`; no transfer is included. |
| `Core/SolutionConcepts.lean:63`, `IsDSIC` | Truthful reporting weakly dominant for every true profile | Equivalent: for fixed `i,theta`, every report profile `r` is compared with its update to truthful own report. This quantifies over every alternative own report and every opponent-report profile. Values may be interdependent because the full `theta` is fixed across the comparison. |
| `Core/SolutionConcepts.lean:70`, `IsExPostIR` | Ex-post individual rationality at truthful play with outside utility zero | Equivalent: every agent and every true profile has nonnegative truthful utility. IR under arbitrary opponents' reports would be a stronger property and is not asserted. |
| `Core/SolutionConcepts.lean:75`, `IsEfficient` | Truthful outcome maximizes utilitarian value over the whole outcome type | Equivalent: `IsMaxOn` over `Set.univ` expands to comparison with every `o:O`. The outcome type is the feasible universe. |
| `Core/SolutionConcepts.lean:88`, `IsBudgetBalanced` | Strong budget balance, pointwise in action profiles | Equivalent for finitely many agents: total monetary receipts of agents vanish, hence designer revenue is zero. |
| `Core/SolutionConcepts.lean:91`, `IsNoDeficit` | Weak budget balance/no net payout, pointwise in action profiles | Equivalent: total agent receipts are nonpositive, hence designer revenue nonnegative. |
| `Core/Comap.lean:44`, `comap` | Mechanism induced by componentwise report/action maps | Exact pullback: both outcome and transfer evaluate the same translated action profile. Every such induced mechanism has precisely these rules. |
| `Core/Strategic.lean:58`, `utilityGame` | Strategic game induced by fixing the full true type profile | Exact construction: all action-profile payoffs equal mechanism utilities at that fixed profile. This definition is annotated on its declaration line and was missed by the initial inventory pattern. |
| `Core/Bayesian.lean:59`, `inducedBayesianGame` | Type-dependent Bayesian game form induced by mechanism utilities | Exact construction of the payoff table; belief/prior data belong to the Bayesian-game layer rather than this game-form constructor. Fixed-type restriction equals `utilityGame`. Also absent from the initial inventory pattern because of annotation. |
| `Auctions/Allocation.lean:53`, `IsUnitIntervalAllocation` | Individual allocation probability/share bounds | Equivalent to coordinatewise membership in `[0,1]` at every mechanism output. It explicitly does not claim aggregate single-item feasibility. |
| `Auctions/Allocation.lean:61`, `UsesStrictHighestBidAllocation` | Award one unit to a strictly highest bidder, discard ties | Equivalent: indicator is one exactly when every other bid is strictly smaller and zero otherwise. It is not advertised as welfare efficiency or arbitrary tie breaking. |
| `Auctions/AllPurchase/Spec.lean:60`, `AllPurchaseSpec` | Positive posted unit price, continuous strictly decreasing resale schedule, net expenditure and strict-highest prize rules | Exact bundled specification of these rules. Both directions hold by supplying/unpacking `price`, `phi`, and their properties. Purchases and resale values are explicitly allowed to be negative (`:25-26`); comparison with a nonnegative-purchase market requires an additional domain restriction. |
| `Auctions/AllPurchase/Spec.lean:81`, `IsAllPurchase` | Existence of parameters satisfying the preceding all-purchase specification | Equivalent by `Nonempty`: no extra price/schedule restrictions are introduced or dropped. This is a library-specific rule specification, not a completeness claim for every resale market. |

## Independent algebra and quantifier checks

For DSIC, put `r=(x_i,r_-i)`. The defining inequality is exactly

`value_i(theta,outcome(x_i,r_-i))+transfer_i(x_i,r_-i) <= value_i(theta,outcome(theta_i,r_-i))+transfer_i(theta_i,r_-i)`.

Every choice of alternative report `x_i` and opponents' reports `r_-i` produces such an `r`; every `r` supplies such a choice. Thus neither a deviation nor an opponents' profile is lost. In particular the true opponents' types and their reports need not agree. A mechanism that is only truthful against truthful opponents would not in general pass this universal quantifier.

Money signs were checked independently with a one-agent transaction: receipt `transfer=3` gives utility `value+3`, payment `-3`, and revenue `-3`; receipt `transfer=-3` gives utility `value-3`, payment `3`, and revenue `3`. This matches no-deficit's `sum transfer<=0` and strong balance's equality. `comap` applies exactly the same action transformation to outcomes and transfers, so it cannot change these signs.

Private-values invariance compares valuations at a fixed outcome, not equilibrium outcomes. The `welfareExcl_update` result correctly changes another agent's type while holding this outcome fixed. Efficiency excludes transfers consistently with total monetary transfers cancelling when the designer is included in utilitarian monetary welfare.

## Rejected defect candidates and explicit separating instances

These are useful scope checks, not findings against the stated concepts. Each numerical calculation was independently recomputed by the area lead after the first source-reading pass.

1. **Coordinate bounds do not ensure single-item feasibility.** Two agents, any one action profile, and allocations `(1,1)` satisfy `IsUnitIntervalAllocation` but allocate two units. This is a real separation from single-item feasibility, but the source explicitly states no aggregate capacity constraint (`Auctions/Allocation.lean:21-25,50-55`). A single-item feasibility predicate would additionally require `sum_i alloc_i<=1`; changing the current definition would change its documented concept.
2. **Ties discard the prize.** Two bids `(0,0)` make each strict comparison `0<0` false, so both allocations are zero. The usual randomized or deterministic tie-breaking highest-bid auction allocates the object in this case, and therefore fails this particular predicate. This is an explicit convention at `Auctions/Allocation.lean:22-25,57-63`, not a false negative for the promised strict rule. A separately named weak-highest/tie-breaking predicate could represent those other auctions.
3. **All-purchase allows negative purchases.** One bidder, price `1`, scarcity schedule `phi(B)=-B`, outcome allocation always `1`, and `transfer(b)=-((1+b)*b)` satisfies the stated specification for every real bid. The bidder wins vacuously and `phi` is continuous/strictly decreasing. At `b=-1`, gross expenditure is `-1`, resale proceeds are `(-1)*phi(-1)=-1`, and net payment is `0`; at `b=1` net payment is `2`. Negative purchases are economically unsuitable for a physical purchase-only market, but are explicitly admitted by this specification (`Spec.lean:25-26`). Restrict reports to nonnegative reals or introduce a feasible-action domain to obtain that additional market interpretation.
4. **Highest bid is not efficiency.** For values `(0,1)` and bids `(2,1)`, bidder 1 receives the object although bidder 2 values it more. The allocation predicate is explicitly a bid rule, not a welfare condition (`Allocation.lean:24-25,60`). The separate `IsEfficient` definition supplies the correct welfare concept.

## Four passes and verification limits

1. Constructive map: read all nine modules, identify payoff/transfer conventions and every declaration family above.
2. Hostile pass: test reports versus true types; omitted deviations; signed money; tie handling; individual versus aggregate feasibility; empty/singleton agents; nonnegative purchase interpretation; private-values quantifiers.
3. Reverse direction: expand each predicate and constructor; verify the DSIC product-quantifier equivalence and the budget signs algebraically. Inspect strategic/Bayesian bridges to ensure type and action arguments are not exchanged.
4. Reconciliation: independent verifier reviews the core; area notes and inventory are reconciled by the area lead. No project build or Lean kernel verification is claimed here. The derivations above are exact, not numerical approximations or bounded searches.

Primary terminology cross-check: [Hartline, Mechanism Design and Approximation, chapter 2](https://jasonhartline.com/MDnA/MDnA-ch2.pdf), definitions 2.2.1 and 2.4.1, confirms the dominant-action quantification and `v*x-payment` convention; sections 2.4-2.5 distinguish interim reduced forms from complete game equilibrium. The all-purchase rules were assessed against their explicit local specification; a matching externally published general definition was not located and is not asserted.
