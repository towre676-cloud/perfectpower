# Implementation freedom, exact transport, and optimal finite diagnosis

## The enhancement

This extension develops the mathematical architecture recovered from the user's SOE program into new PerfectPower interfaces. The canonical historical SOE archives were not available in this workspace. Consequently the implementation is an enhancement built from the recovered program context, rather than a claim that the old compiler or hardware system has been restored. The useful connections are semantic implementation fibres, delayed target commitment, semiring transport, future-state discovery, and exact changes of representation. Each becomes an executable interface with an explicit finite or algebraic scope.

Six commands expose the work: `soe-family`, `soe-transport`, `soe-states`, `soe-equivalence`, `soe-chart`, and `soe-plan`. The runtime uses only the Python standard library. It builds on PerfectPower's existing exact populations, the PSG rational polynomial interpreter, and the affine generalized-Pell bridge. The new interfaces do not claim Lean refinement, industrial speedup, universal compiler correctness, or discovery of an unknown physical device's state. Their purpose is to make concrete pieces of that larger ambition reusable without overstating what a supplied model establishes.

The enhancement changes the unit of work. Instead of producing a single implementation and then trying to remember why it was acceptable, it retains a family of original implementations, the observations that identify their semantics, the restrictions that establish legality, and the target valuation used to choose among them. Instead of treating identical present outputs as identical states, it asks whether every permitted future action preserves that identification. Instead of ranking experiments by a heuristic score, it can solve an exact finite decision problem for minimum worst-case measurement cost.

## Semantic fibres retain original identities

Let I be a finite carrier of implementations and let π:I→S be an exact semantic map. For a required semantic value s, the admissible family is the intersection of π⁻¹(s) with the legal subset L. A target cost function is applied to that intersection. This order matters: an inexpensive implementation with the wrong behavior does not compete with an expensive implementation having the required behavior, and a semantically correct but illegal implementation is excluded before optimization.

`ImplementationFamily` accepts named original objects with exact coordinates and nonnegative rational weights. Semantic outputs are rational polynomials evaluated at those coordinates. Different object IDs remain different implementations even when their coordinates or semantic outputs coincide. The result returns every accepted original ID, its coordinates, semantic values, weight, and costs. Projection never silently substitutes a semantic label for an original object's identity.

The query interface admits polynomial equality and inequality restrictions, a specified semantic value, and up to eight polynomial objectives. A single objective returns its minimum together with every tied minimizer through the Pareto set. Several objectives return all nondominated implementations under componentwise minimization. Equal cost vectors do not dominate each other strictly, so distinct tied objects remain present. Zero-weight objects also retain their identities: weighted mass and object count answer different questions.

Completeness is relative to the supplied carrier. If a caller supplies twelve candidate machine layouts, the interface decides the exact query over those twelve layouts. It does not prove that no thirteenth layout exists. This limitation is visible in the result scope. The existing `ExactPopulation` adapter supplies a stronger source when a supported backend already represents a complete bounded arithmetic family, but materialization remains limited to 4,096 original objects. An empty source family is a valid result, not an error disguised as an absent optimum.

## Connected original-coordinate arithmetic

The worked arithmetic example starts with the original equation (2x+1)²−2y²=−1 and the cutoff |y|≤1000. The existing affine norm bridge constructs twenty original integer points, retaining the nonunimodular inverse-coordinate restriction. The new semantic family uses the polynomial (2x+1)²−2y² as its semantic output, so every admitted source point belongs to the same semantic fibre with value −1.

A legal restriction y≥0 retains ten original points. The target objective x²+y² has exact minimum one. The calculation passes through the original integer coordinates throughout; it does not minimize over canonical Pell coordinates and then assume every canonical minimizer can be realized in x,y. This is the connection between implementation freedom and arithmetic families: many original objects can share a required invariant while still differing in legal status, target cost, or future behavior.

The earlier PSG work established why reconstruction must retain exceptional branches and integer image conditions. This extension reuses that discipline at the family level. Coordinate elimination is useful only when an answer can be recovered in the original space. Semantic projection is useful only when the original implementations and their multiplicities remain recoverable from the fibre ledger.

## Three semirings answer three different transport questions

A finite transport is a sparse relation between two declared, ordered carriers of original IDs. Composition combines intermediate contributions. The interface provides three distinct algebras because changing the meaning of addition or multiplication changes the question being answered.

In the natural-count semiring, entries are nonnegative integers. Addition combines alternative paths and multiplication combines successive path multiplicities. The coefficient of a composed source-to-target edge is the number of represented two-stage paths, with declared multiplicity. Two distinct intermediate paths arriving at one target must be counted twice; merely recording reachability would lose information.

In the nonnegative rational-mass semiring, entries and input masses are exact rational numbers. Composition sums products. A row-stochastic transport preserves total mass because every source row sums to one. The interface reports every row sum, including missing source rows, and accepts the preservation claim only when all of them equal one. A transport can be meaningful without preserving mass, but the two situations receive different results.

In the min-plus semiring, addition chooses the smaller cost and multiplication adds successive costs. The additive zero is unreachable, represented internally by an absent value; a reachable zero-cost edge is a different object and remains present. Composition finds cheapest paths through the declared stages. Negative rational edge costs are permitted because this operation concerns a fixed finite path composition, not an unrestricted shortest-path closure with potentially negative cycles.

The receipt corpus checks 360 compositions against independent enumeration of their original two-edge paths. A separate dense checker replays the composed coefficient identity from caller-supplied arrows without trusting sparse composition. Its own work budget is explicit. Associativity tests cover all three algebras. Carrier order and semiring must agree before two transports compose; these checks establish declared carrier compatibility, not a scientific interpretation of arbitrary labels.

## Forward mass and backward questions

The same rational-mass relation carries source weights forward and target questions backward. If K is its matrix, w is a source weight vector, and q is a nonnegative target valuation, the identity ⟨wK,q⟩=⟨w,Kq⟩ follows by rearranging a finite sum. This makes projection useful for repeated queries: one can aggregate a population once, or pull a target question back to original objects, while obtaining the same weighted answer.

The implementation tests this pairing identity exactly. It also retains the exceptional multiplicity of signed arithmetic orbits. For the seven parameters −3 through 3 projected by n↦n², the zero fibre has one original parameter and each positive square fibre has two. Uniform sampling over semantic labels would not be uniform sampling over original parameters. Count transport and rational-mass transport make that distinction explicit rather than burying it in a choice of representative.

## Future equivalence includes action legality

For a finite deterministic partial transition model, an action can either lead to a successor state or be disabled. An observation is an exact JSON label. States are future-equivalent when their observations agree and every finite action word has the same observation and enabled-action behavior from both states. Present-output equality is necessary but insufficient.

The quotient begins with states grouped by present observation. It repeatedly refines each block by the enabled status and destination block of every action. Refinement stops after a finite number of block splits. At the fixed point, the projection commutes with every enabled transition, and disabled actions remain disabled. Induction on action-word length then establishes preservation of every finite future observation/legality trace.

The result is the coarsest quotient preserving those observations and partial actions. A replay checker verifies the original-carrier partition, the projection, observation agreement, and every action commuting square. Minimality is established by a distinguishing experiment for each pair of quotient representatives: states that can be distinguished by an action word cannot be merged in any valid observation-and-legality quotient.

The state model is supplied. Hidden physical state, noisy measurements, stochastic transitions, and uncertainty about the transition function remain separate problems. The quotient does not learn those facts from a few observations. This boundary is particularly important when applying a finite exact result to SOE target-state discovery: an exact quotient of an inaccurate device model is still a quotient of that model.

## Shortest experiments and different model sizes

A reverse graph on unordered state pairs computes shortest distinguishing words. Pairs with different current observations are already distinguished by the empty word. Pairs with different action legality have one-action witnesses. Every jointly executable action propagates a witness backward from its successor pair. The resulting algorithm computes pair distinctions together, instead of launching a separate forward search for every pair.

The corpus exhausts all 324 two-state partial deterministic models with two named actions and binary observations. Independent enumeration checks every action word through length four, compares the resulting equivalence relation, and verifies the shortest witness lengths. Additional three-state randomized tests compare against all words through length nine. These are finite exhaustive and regression results; they are not a proof of the Python interpreter in a proof assistant.

Cross-model comparison forms a disjoint union of two models and applies the same quotient. Initial states in the same quotient block have identical behavior under every finite action word in the supplied models. Otherwise the result contains a shortest counterexample, including action-legality disagreements. Missing actions are treated as disabled. A worked example compares a four-state duplicated toggle model with a two-state toggle model and recovers a common two-state quotient. Changing one transition immediately yields a one-action counterexample.

This is a useful form of compiler-model equivalence: two representations need not have the same number of internal states or the same internal names. What must agree is the protected observable behavior and the allowed future interaction. It remains finite behavioral equivalence, not arbitrary program equivalence on all possible inputs.

## Exact adaptive diagnosis improves the experiment schedule

A probe is a named action word with positive rational cost. Each probe resets to the same unknown original state, executes its word, and reports the complete observation/legality trace. Observation events and disabled-action events use distinct tagged representations, so user-supplied JSON observations cannot impersonate legality events. Present observation is free. A diagnosis policy chooses subsequent probes according to the observed outcomes and stops when the remaining belief set belongs to one future-equivalence class.

The planner memoizes finite belief sets. For a proposed first probe, its outcomes partition the current belief. The worst-case remaining cost is the probe cost plus the maximum optimum over its outcome branches. Minimizing this value across the declared probe menu gives the exact finite-menu optimum. Probes that fail to split the belief are discarded: with positive cost and the reset assumption, repeating such a probe cannot improve identification.

The worked six-state model has four initially indistinguishable states and two visibly distinct terminal states. Three probes are available, each costing one. One probe separates the four hidden states into two pairs; the other probes distinguish the respective pairs. An adaptive policy asks the first probe and then chooses the relevant second probe. Its worst-case cost is two. Every fixed two-probe schedule leaves at least one pair ambiguous, while a fixed three-probe schedule distinguishes all four. The improvement is demonstrated on this declared model: two adaptive probes versus three fixed probes, not an empirical speedup for a real device.

If the menu cannot identify the future class, the result supplies two future-distinct states with identical traces for every offered probe. That proves menu insufficiency. It does not prove that no better probe could be invented. The planner's minimum is likewise over the supplied menu, under resettable-probe and additive-cost assumptions. Non-resettable experiments require a different belief-state transition problem and are left open.

## Reversible nonlinear charts transport derivatives

The chart interface accepts rational polynomial coordinate maps φ and ψ and checks both identities ψ∘φ=id and φ∘ψ=id. It then checks semantic preservation S=T∘φ. These are global polynomial identities, not sampled equalities. The derivative transport follows the chain rule: DS=(DT∘φ)Dφ. Every displayed derivative coefficient is checked by the exact rational polynomial interpreter.

The nonlinear example φ(x,y)=(x+y²,y) has inverse ψ(x,y)=(x−y²,y). Both coordinate maps have integer coefficients, so the identities establish an integer lattice bijection as well as a rational polynomial automorphism. Semantic outputs and their Jacobians can therefore move between these charts while retaining their original meaning.

The affine map φ(x)=2x+1 has a rational polynomial inverse (x−1)/2, but that inverse is not integral. The chart is rationally reversible and does not establish a bijection of the integer lattice. The result reports that distinction explicitly. This prevents a rational gauge freedom from being mistaken for an unrestricted legal implementation transformation.

## Reproduction and remaining mathematical work

Run `make soe-bridge` to execute the focused tests and regenerate deterministic receipts. Each console command accepts a JSON specification file and optionally writes a JSON result with `--out`. The `receipts/soe_bridge/cli_*.json` files provide directly runnable examples for all six routes. The installed-wheel check exercises each route outside the source checkout, alongside the preceding PSG routes and existing packaged-runtime checks.

The main remaining extensions are symbolic or infinite implementation families without materialization, stochastic controlled-state equivalence, discovery from uncertain transition evidence, non-resettable optimal diagnosis, richer hardware legality and cost models, and formal refinement of the new executable algorithms. Pareto comparisons, sparse composition, dense replay, and belief search have explicit budgets and stop when those limits are exceeded. Exceeding a work budget produces neither an approximate optimum nor an unsupported impossibility claim.

The resulting machinery connects arithmetic and implementation design through preserved families. Original objects can be constrained, valued, aggregated, transported, compared by future behavior, and diagnosed with an optimal finite policy. The value lies in composing these operations while retaining the exact question each one answers.
