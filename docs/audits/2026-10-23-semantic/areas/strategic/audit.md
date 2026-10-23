> Historical concept assessment at the audited revision. The [publication and proof-scope record](../../README.md) and [repair/migration table](../../MIGRATION.md) distinguish confirmed findings from candidates and current repairs.

# Strategic games, equilibrium, outcomes, mixed strategies, and existence

Source revision: `1d9f8cc233cdaeee0364b51befb84feea657a4da`.

Verdict: no independently verified substantive conceptual defect identified in this area. One expected-utility semantic-domain documentation caveat is recorded below; it is not treated as an incorrect theorem or an equilibrium counterexample on the admitted finite-expectation domain.

## Scope and verification

All six source files were read in full: `GameTheory/Equilibrium/Problem.lean` (179 lines), `Strategic/Basic.lean` (339), `Strategic/Outcome.lean` (214), `Strategic/Mixed.lean` (257), `Strategic/Mixed/Finite.lean` (218), and `Strategic/Existence.lean` (656): 1,863 source lines. All 50 current `area = strategic` inventory entries are mapped in [coverage.json](coverage.json). The review also covers the dominance order instances, regularity classes, and the attributed outcome-mixing definitions.

Four passes were completed:

1. Extracted the definitions, intended concepts, dependencies, declared assumptions, and module-level conventions from every source file.
2. Checked both directions against the concepts below. For predicates, the main method was direct quantifier expansion. For constructions, it was comparison with the defining mathematical formula and the stated domain.
3. Tried adversarial cases: empty/singleton action and player spaces, duplicate actions and payoff ties, incomparable vector payoffs, non-surjective action maps, nested lotteries, nonintegrable utilities, arbitrary versus integrable mixed deviations, and irrelevant extension values outside feasible sets.
4. An independent reader re-audited dominance and equilibrium refinements and separately implemented coalition and unilateral predicates; another reader independently checked the expected-utility candidate against pinned mathlib. The parent area auditor read the independent checker and results. These independent reviews agreed with the conclusions below.

Reproducible finite evidence: run `python3 docs/audits/2026-10-23-semantic/areas/strategic/verification/dominance.py`. The saved [results](verification/dominance-results.json) report exit-success assertions for all 256 two-player, two-action games with binary payoffs, 1,024 game/profile cases, 1,024 game/player/action cases, and six boundary scenarios. This establishes only those encoded finite cases; the general arguments below do not rely on finite exhaustion.

No library source was changed. Existing Lean tests were inspected as source, not represented as freshly compiled proofs. LeanProbe readiness was queried successfully, but no Lean witness or whole-project build success is claimed by this area auditor. The initial checkout lacked a complete built dependency environment.

Source paths below are relative to `MathEconLib/`; a colon gives the exact declaration or relevant equation line. Helpers are grouped under their mathematical purpose.

## EP

**Declarations:** `GameTheory/Equilibrium/Problem.lean:52` (`EquilibriumProblem`), `:68` (`IsEquilibrium`).

**Intended concept:** a state with no admissible deviation whose reward exceeds the incumbent reward, formulated as incumbent weakly dominating every directly admissible reward. The inputs are states, deviators, a supplied deviation relation, and a value function.

**Both directions:** the predicate is literally `∀ i s', deviation i s s' → value i s' ≤ value i s`. Thus every formal equilibrium satisfies every required inequality, and any state satisfying these inequalities is a formal equilibrium. Under `LinearOrder V`, this is equivalent to absence of strict improvement; `isEquilibrium_iff_not_lt` correctly requests that assumption at `:89–91`.

For a partial order, absence of a strict improvement need not imply the inequality. The file explicitly states this at `:13–16` and `:63–67`. It also expressly says that only the supplied one-step relation is checked (`:18–22`, `:64–67`). A non-transitive relation is not silently closed. These are documented generalizations, not defects. No extraneous feasibility assumptions are smuggled into `EquilibriumProblem`: the deviation relation is responsible for them.

## MOR

**Declarations:** `GameTheory/Equilibrium/Problem.lean:96` (`GameMorphism`), `:121` (`id`), `:128` (`comp`).

**Intended concept:** the library's expressly chosen reward-preserving, deviation-lifting map, sufficient to push equilibria forward. There is no unique canonical economic notion of a game morphism being silently presumed.

**Both directions:** the fields specify exactly a state map, target-to-source deviator map, lifting of every target deviation from an image state, and equality of corresponding rewards (`:99–108`). Conversely any functions with those properties construct this structure. For transport, a target deviation lifts to a source deviation; source equilibrium bounds its reward, and the equality field transfers that bound. The identity uses the same deviation witness. Composition lifts through the second map and then the first; its deviator map reverses in the necessary order (`:129–136`). It does not claim that every map preserving the equilibrium set must satisfy these stronger local contracts.

## COMOR

**Declarations:** `GameTheory/Equilibrium/Problem.lean:140` (`GameComorphism`), `:164` (`id`), `:171` (`comp`).

**Intended concept:** a reward-preserving map sending source deviations to target deviations, sufficient to pull equilibria back.

**Both directions:** the fields are exactly deviation mapping and reward equality. Pullback (`:157–161`) sends a source deviation to a target deviation, applies the target equilibrium inequality, and translates rewards. Composition forwards the deviation first through the first map and then through the second (`:172–175`); both state and deviator map orders are correct. As with `GameMorphism`, this is an explicitly stated structural contract rather than a claim to characterize every possible equilibrium-preserving function.

## GAME

**Declarations:** `GameTheory/Strategic/Basic.lean:66` (`StrategicGame`), `:76` (`comapActions`).

**Intended concept:** a normal-form payoff game on a dependent product of individual action spaces; action translation pulls the payoff function back pointwise.

**Both directions:** any payoff assignment `i ↦ (a ↦ u_i(a))` constructs the structure, and its sole field is exactly such an assignment. `comapActions` evaluates `u_i((κ_j(b_j))_j)` (`:78`), so it is the ordinary game induced by independently relabeling/restricting/duplicating individual actions. The identity and composition formulas are pointwise correct (`:80–87`).

The data structure admits empty action spaces and infinite player types. These are deliberate constitutive-data generality; the equilibrium-existence results separately require nonempty actions and finite players. If an action space is empty, no action profile exists, so there is no spurious equilibrium object. No failure of a theorem for an ordinary nonempty game was found.

## NASH

**Declarations:** `GameTheory/Strategic/Basic.lean:90` (`nashProblem`), `:96` (`comapActionsComorphism`), `:107` (`IsNash`).

**Intended concept:** pure Nash equilibrium: every player's incumbent action is a best response to the fixed opponents' actions.

**Both directions:** `nashProblem.deviation` admits precisely `update a i s`. Such an update changes only coordinate `i`; conversely every profile agreeing with `a` outside `i` is `update a i (a' i)`. Therefore `IsNash` is exactly `∀ i s, u_i(s,a_{−i}) ≤ u_i(a)` (`isNash_iff`, `:118–127`). Self-deviations add only reflexivity under ordinary ordered payoffs. The `LinearOrder` no-strict-improvement characterization at `:154–157` is valid; the documented partial-order variant intentionally also rules out incomparable deviations.

Action translation commutes with updating a coordinate (`:101–104`), so its comorphism and Nash pullback direction are correct. Nash equivalence for action equivalences uses surjectivity via the inverse (`:131–145`). **Rejected converse candidate:** one player has original actions `{0,1}` with `u(a)=a`, while the translated game has only action `0`. Its sole profile is Nash after restriction but is not Nash in the original game. The source correctly states only the opposite pullback implication for arbitrary maps (`:110–115`), so this does not refute any claimed equivalence.

## DOM

**Declarations and defining instances:** `GameTheory/Strategic/Basic.lean:164` (`Strategy`), `:172–174` (dominance `LE`), `:201` (`IsDominant`), `:211` (dominance preorder), `:230` (`IsStrictOrderDominant`), `:248` (`IsStrictlyDominant`).

**Intended concepts:** pure actions ordered by payoff weakly increasing against every opponents' profile; a dominant action is a top of that preorder. Strict-order dominance means weak improvement everywhere and strict improvement somewhere against each distinct alternative. Strict dominance means strict improvement everywhere against each distinct alternative.

**Both directions:** the two profiles in `LE` are required to agree outside the player and have their own coordinates equal to the two compared actions. This is equivalent to the pointwise payoff comparison `u_i(s,a_{−i}) ≤ u_i(s',a_{−i})`; the update characterizations at `:183–197` expose both directions. Hence `IsTop s` is precisely weak optimality of `s` against every opponents' profile. Under `Preorder V`, `s' < s` means `s' ≤ s` and not `s ≤ s'`; combined with the first inequality, failure of the reverse is exactly strict payoff improvement at some profile (`:220–225`). `IsStrictOrderDominant` quantifies this condition over each distinct alternative; the profile witnessing strict improvement may depend on that alternative, correctly. `IsStrictlyDominant` directly requires the strict payoff inequality at every profile (`:250–251`).

Some texts reserve “weak dominance” for weak everywhere plus strict somewhere, while others use it for this preorder. The source defines its convention explicitly and gives the two different predicates separate names. Hajek's [game theory text, Remark 1.9](https://hajek.ece.illinois.edu/Papers/GameTheoryDec2017.pdf) acknowledges the competing terminology. This is not a conceptual error.

**Adversarial checks:** (i) two distinct actions with identical payoff are both dominant but neither strictly dominant nor strict-order dominant; (ii) `u_0(a_0,a_1)=a_0 a_1` on binary actions gives action `1` strict-order dominance with a tie at opponent action `0`, so it is not strictly dominant; (iii) if an opponent has no actions, all pointwise comparisons are vacuous and strict dominance can hold, while the strict preorder between distinct alternatives does not. The source's bridge `IsStrictlyDominant.isStrictOrderDominant` explicitly requires a nonempty full profile space (`:265–273`). The existing `MathEconLibTest/GameTheory/Strategic.lean:106–159` and the independent checker both distinguish these cases. No bridge theorem conflates the concepts.

## REFINE

**Declarations:** `GameTheory/Strategic/Basic.lean:283` (`IsStrictNash`), `:313` (`IsStrongNash`).

**Strict Nash, both directions:** `∀ i s ≠ a_i, u_i(s,a_{−i}) < u_i(a)` is precisely a unique-best-response condition at the incumbent opponents' actions. The exclusion of unchanged actions is essential and present. Every strict unilateral change has a distinct action and conversely. The theorem implying Nash asks for `Preorder V`, ensuring compatibility of `<` and `≤` (`:295–301`).

**Strong Nash, both directions for linearly ordered payoffs:** formal strong Nash requires every distinct profile `a'` to leave some actual changer `i` with `u_i(a') ≤ u_i(a)`. Let `D={i | a_i≠a'_i}`. If the formal property fails, `D` is nonempty and every member strictly benefits, so coalition `D` can implement the profitable deviation. Conversely, suppose a nonempty coalition `C` can deviate with outsiders fixed and all its members strictly benefit. A strictly profitable deviation changes the profile; its nonempty actual changer set `D` is a subset of `C`. Every `i∈D` strictly benefits, contradicting the formal witness requirement. Thus allowing coalition members who keep their own actions does not change the concept. This is a general quantifier argument, independent of the finite computation. It agrees with the profitable-coalition definition in [Harks–Klimm–Möhring, Definition 1](https://arxiv.org/pdf/0909.0347).

For an arbitrary player set this excludes all coalitions; there is no implicit restriction to finite coalitions. For ordinary finite games that distinction disappears. The partial-order strengthening is explicitly stated at `:309–312`; the strict-improvement equivalence correctly requires `LinearOrder V` (`:319–322`).

**Rejected partial-order defect:** a one-player binary-action game with payoffs `(0,1)` and `(1,0)` under the componentwise order has no strict profitable deviation but neither action satisfies the library's Nash/strong Nash inequalities, because the payoffs are incomparable. This is exactly the documented convention, not an undisclosed false negative. A different Pareto-maximality concept would require a separately named predicate.

## OUTCOME

**Declarations:** `GameTheory/Strategic/Outcome.lean:48` (`OutcomeGame`), `:53` (`PayoffStructure`), `:60` (`StrategicGame.ofOutcome`), `:80`, `:117` (measurability classes), `:122` (boundedness), `:163`, `:190` (continuity classes), `:90` (`mixed`), `:96` (`mixedFlattened`).

**Intended concepts and both directions:** an outcome game is exactly a deterministic map from action profiles to outcomes, and a payoff structure is exactly a separate utility map for each player. Their composite is `u_i(o(a))` (`:62`). Regularity classes directly require measurability/continuity of the named maps and boundedness of each player's range. “Bounded” is playerwise, not a common bound uniform across potentially infinitely many players; this matches its explicit docstring.

`mixed` computes the pushforward of the independent product law through the measurable outcome map (`:92`). For any measurable outcome event `B`, its probability is the product-law probability of `{a | o(a)∈B}`, which characterizes the induced distribution. It does not purport to represent correlated actions. If outcomes themselves are laws, `mixed` intentionally gives a law of laws; `mixedFlattened` applies `ProbabilityMeasure.join`, producing the mixture `B ↦ ∫ o(a)(B) d(⊗_j σ_j)(a)` (`:99–100`). The source explicitly distinguishes these two constructions (`:85–89`). No extra or missing randomization stage was found.

The measurable and continuous instances impose the stated action/outcome measurable and topological assumptions. In particular continuity-to-measurability and continuity of product-law mixing are not asserted on arbitrary incompatible measurable structures (`:169–183`).

## EXPECTED

**Declaration:** `GameTheory/Strategic/Outcome.lean:134–136` (`PayoffStructure.expected`).

**Intended concept:** utility of an outcome lottery, represented by the Bochner expectation in a complete real normed space.

**Both directions on the semantic domain:** for a lottery `μ` for which `P.payoff i` is integrable, its Bochner expected utility is exactly the integral used by the definition, so both directions are equality by construction. Real bounded measurable utilities are integrable under all outcome laws; compact continuous real utilities also give the usual expectation under the stated measurable-space assumptions. The later measurability and continuity instances impose corresponding sufficient conditions (`:139–142`, `:204–208`).

**Caveat C-STR-1, not an elevated substantive finding:** the constructor itself requires neither integrability nor measurability. Unlike `Mixed.lean:95–102`, its local documentation calls the result expected utility without saying that nonintegrable utilities produce zero. Thus its raw total domain is larger than the domain of finite expected utility. This is an API/documentation issue worth clarifying under `DESIGN.md:223–229`, not a refutation of an economic theorem on admitted utilities.

**Explicit witness:** one player; outcomes `ℝ` with their usual Borel structure; `μ = volume.restrict (Ioc 0 1)`; `P.payoff () x = x⁻¹`. The interval has measure one. On `(0,1]` the utility is nonnegative, and for every `0<ε<1`, its truncated integral is `∫_[ε,1] dx/x = −log ε`. These values tend to `+∞` as `ε→0+`; hence `u` is not integrable and its extended nonnegative expectation is `+∞`. The formal totalized payoff is `0`. This is not a finite-expectation lottery and is therefore outside the ordinary real-valued expected-utility domain.

**Independent verification:** the independent reviewer inspected the [pinned mathlib Bochner implementation](https://raw.githubusercontent.com/leanprover-community/mathlib4/8f9d9cff6bd728b17a24e163c9402775d9e6a365/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean), where the definition explicitly returns zero outside `Integrable` and `integral_undef` states this. The repository separately contains the exact reciprocal nonintegrability derivation in `MathEconLibTest/GameTheory/Integrability.lean:90–105`; those source proofs were read, not freshly compiled by this auditor. The analytic argument above independently establishes the example's mathematical side.

**Proposed clarification:** document `expected` as the totalized Bochner integral, with expected-utility interpretation conditional on `∀ i, Integrable (P.payoff i) μ`. A reusable predicate/restricted lottery domain could expose this condition; bounded measurable real utilities are a sufficient stronger restriction. No source edit is proposed as part of this audit. The current boundedness result (`:143–150`) remains a correct norm bound even when a nonmeasurable utility integral is totalized to zero; it does not assert a new probability-theoretic expectation theorem in those cases.

## MIX-REP

**Declarations:** `GameTheory/Strategic/Mixed.lean:56` (`outcomeGame`), `:60` (`payoffStructure`), `:64` (`Bounded`), `:79` (`MixedStrategy`), `:83` (`Measurable`), `:243` (`Continuous`).

**Intended concepts and both directions:** the strategic game's profile is used as an outcome, with identity outcome map and its original payoffs as utilities. Thus recomposition recovers the same payoff assignment. A mixed profile is exactly one probability law per individual action space, so it describes independent randomization once the product law is used. Every such collection is admitted; a correlated joint distribution is intentionally a different object. Boundedness, measurability, and continuity ask exactly for the corresponding condition on each strategic payoff function, with no hidden uniform-player bound. The identity outcome map automatically has the required regularity.

## RAW-MIX

**Declaration:** `GameTheory/Strategic/Mixed.lean:99–102` (`mixedExtension`).

**Intended concept:** the independent mixed extension as a raw, totalized Bochner-integral payoff game.

**Both directions:** on integrable payoffs it is precisely `E_{⊗_j σ_j}[u_i]`. The independent product includes every player once; a unilateral law replacement preserves all opponents' laws. Conversely every profile of independent action laws gives exactly that integral. The function remains defined when a payoff is nonintegrable, but the file explicitly labels it zero there (`:13–19`, `:95–98`). It does not equate raw Nash of this extension with the economic `IsMixedNash` without the extra hypotheses checked next. `mixedExtension_eq_ofOutcome` (`:105–111`) is an identity with pushforward through the identity profile outcome map; it is valid as a raw identity even without an economic interpretation of a nonintegrable integral.

## MIX-NE

**Declarations:** `GameTheory/Strategic/Mixed.lean:114` (`MixedPayoffsIntegrable`), `:142` (`mixedNashProblem`), `:167` (`IsMixedNash`).

**Intended concept:** independent mixed Nash equilibrium with integrable incumbent payoffs, comparing unilateral deviations whose deviator payoff is integrable. This admissibility convention is explicit, including the distinction from raw integral Nash (`:136–146`, `:165–173`).

**Both directions:** incumbent integrability is exactly `∀ i, Integrable u_i (⊗_j σ_j)`. A deviation consists of a replacement of one player's law and integrability of that player's payoff under the resulting product. The structure then demands every such deviation's integral be weakly below the incumbent integral. Conversely those integrability and inequality conditions construct `IsMixedNash`; `isMixedNash_iff` exposes exactly them (`:177–189`). It does not require other players' payoffs to be integrable after somebody else's deviation, which is unnecessary for evaluating that deviator's incentive.

The raw-equilibrium problem alone lacks incumbent integrability by design and is not named `IsMixedNash`. The equality with raw Nash requires integrability of every unilateral payoff (`:200–213`), including the unchanged action law, or uses bounded measurable payoff hypotheses in a second-countable value space to derive it (`:217–234`). The assumptions justify Bochner measurability and bounded integrability; no converse silently loses the incumbent condition.

**Rejected candidates:** on `(0,1]` uniform mixing, the one-player action payoff `u(a)=−|a⁻¹|` has totalized integral zero, can satisfy raw Nash, and loses raw Nash after adding one to all pure utilities. This pathology is explicitly documented and its incumbent fails `IsMixedNash` by integrability. Conversely `u(a)=−|a⁻¹|−1` at pure action zero is an economic mixed equilibrium against all integrable deviations, but raw Nash compares a nonintegrable uniform law totalized to zero and rejects it. That is the announced admissible-deviation convention, not a false negative of its stated predicate. The existing exact constructions appear in `MathEconLibTest/GameTheory/Integrability.lean:118–270`. No claim was found that also compares deviations with positive infinite or undefined expectations.

## FINITE-MIX

**Declarations:** `GameTheory/Strategic/Mixed/Finite.lean:58` (`FiniteMixedStrategy`), `:65` (`finiteExpectedPayoff`), `:79` (`finiteMixedExtension`), `:84` (`IsFiniteMixedNash`), `:101` (`toSimplex`), `:105` (`toProbability`).

**Intended concepts and both directions:** a mixed action is a finite probability weight vector (`FinDist`); profiles are independent weight vectors; their payoff is `Σ_a (∏_j σ_j(a_j)) • u_i(a)`. `FinDist.productD` and `FinDist.expect` expand to precisely this formula (`:68`, `:72–76`; dependency definitions `Probability/FinDist/Simplex.lean:44–52` and `Expect.lean:55–56`). Every finite independent distribution supplies such vectors, and any such vectors determine the independent product law. The finite extension simply makes these expected payoffs the strategic payoff field. Its Nash predicate therefore gives every unilateral distribution comparison, exactly the mixed Nash condition, with no integrability issue from finite sums.

For real utilities one may equivalently compare all pure-action deviations: expectation is affine in the deviating player's weights, so a weighted average of pure deviation payoffs cannot exceed an incumbent that bounds each pure deviation. Conversely a pure action is an allowed point-mass distribution. This confirms the formal use of all finite-distribution deviations adds no extra restriction to ordinary finite mixed Nash.

`toSimplex` and `toProbability` apply the finite-discrete probability/simplex equivalence coordinatewise. Both inverse identities are proved at `:109–118`, and they commute with unilateral updates at `:123–141`. The measure bridge expressly requires discrete measurable finite actions (`:98`, `:143`). Finite payoff integrability is supplied at `:49–53`; the expected-payoff bridge uses atom mass products (`:146–161`). Thus `isFiniteMixedNash_iff_isMixedNash` (`:173–180`) neither discards deviations nor introduces a measurable-space mismatch. The arbitrary-outcome bridge includes measurable outcome/payoff maps (`:185–204`), and its equilibrium equivalence is a payoff-preserving action equivalence (`:208–214`). No false positive or false negative was found.

## EXIST

**Declarations:** `GameTheory/Strategic/Existence.lean:69` (`decode`), `:76` (`encode`), `:93` (`bestResponseCorr`), `:458` (`toWeakDualContinuousMap_homeomorph`).

**Intended concepts and both directions:** `encode` and `decode` are the coordinatewise homeomorphism between action profiles and the product of representing feasible sets. Every encoded profile lies in those sets (`:82–87`), and decoding applies the inverse homeomorphism to each coordinate (`:72–73`). Thus neither representation discards or fabricates feasible actions. `bestResponseCorr` consists exactly of feasible represented profiles whose coordinate `i` maximizes `u_i(s,a_{−i})` against the incumbent opponents from `x`, for every player (`:100–104`). Holding opponents at `x`, rather than at the selected response profile, is the correct best-response correspondence. The product characterization at `:231–255` confirms both directions. A fixed point makes these incumbent best-response inequalities the Nash inequalities (`:405–420`). The weak-dual homeomorphism is expressly onto the range of the probability-measure embedding (`:458–461`), not onto the entire weak dual.

**Existence helper audit:** compact feasible sets follow from their action-space homeomorphisms (`:50–66`); maxima require a nonempty compact action space, continuity, and a linear order (`:128–140`). The closed/compact/convex best-response arguments keep the incumbent opponents fixed. Quasiconcavity is requested only on the representing feasible set, so the arbitrary default values of `Subtype.val.extend` outside it are irrelevant (`:169–208`; dependency `ForMathlib/Quasiconvex.lean:31–46`). No accidental zero/`Inhabited V` requirement or constraint on outside values is introduced. The closed-graph-to-upper-hemicontinuity lemma explicitly confines the range to a compact product in Hausdorff coordinate spaces (`:365–382`), rather than making the invalid unrestricted claim that any closed graph is upper hemicontinuous.

The pure existence theorems impose finite players, nonempty compact convex feasible action sets in locally convex real spaces, continuous payoffs, closed payoff order, and quasiconcavity (`:430–453`, `:602–613`). These are sufficient assumptions for the Kakutani/Glicksberg/Fan argument; a partial-order maximality theorem is not asserted. The theorem's hypotheses are sufficient conditions, not claimed necessary conditions for Nash existence.

For mixed existence, continuous real payoffs on compact finite-player action profiles are bounded and integrable under every product probability law. This is explicitly used in the Fubini/weak-dual derivation (`:482–497`) and in converting raw Nash to `IsMixedNash` (`:616–627`). Finite action payoffs are integrable by finiteness (`:631–640`). The final finite-simplex existence theorem transfers through an actual inverse equivalence, without measurable-structure obligations on its public interface (`:644–650`). The arbitrary-outcome compact theorem separately assumes `P.expected.Continuous` (`:562–568`); this is stronger than needed in some cases but is not advertised as a characterization. All these domains exclude the nonintegrable-totalization counterexample above. No substantive conceptual defect was identified.

## Conclusions and limits

No finding in this area meets the threshold for a substantive concept mismatch on its documented domain. The expected-utility caveat has an explicit witness, correction, and independent analytic/source verification; it should remain a caveat unless a downstream theorem actually gives an invalid economic interpretation outside integrability. The unusual partial-order, empty-space, strict-preorder-dominance, raw-integral, and admissible-mixed-deviation cases were checked and reflect explicit source conventions.

This is a semantic audit of the current source and mathematical contracts. It does not certify all imported analytic theorems independently, and it does not claim a fresh successful Lean build. The finite checker supplies reproducible bounded evidence, while the equivalence arguments above explain the general semantic conclusions.
