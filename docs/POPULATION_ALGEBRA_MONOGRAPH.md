**Population algebra: changing the rules while keeping the objects**

**Why this addition matters**

Imagine a room containing every design allowed by a particular set of choices. A first question asks which designs can lift a heavy load. A second asks which designs fit in a small space. A useful program should answer both questions and explain how their answers relate. Which designs pass both rules? Which pass only the first? Which become available when either rule is acceptable? If a design has address twelve in one collection and address seven in another, how do we recognize that it is still the same design?

PerfectPower already supplies exact finite populations for supported mathematical definitions. A population has a count, an ordering, a way to select an object by address, and a way to recover an address from an original object. The new PopulationComparison layer makes relationships between two restrictions into reusable objects. It connects the existing population machinery to explicit set operations, a persistent catalogue, command-line queries, a local service, a formal theorem module, and an interactive demonstration. The important result is a consistent path from a declared mathematical collection to questions about changing requirements.

This account describes the actual implementation and its limits. The word exact refers to integer arithmetic and the supported backend semantics. The word finite refers to the declared population, even when its count is enormous. The generic Lean results establish mathematical laws about partitions and supplied bijections. They do not certify the execution of the Python predicate compiler. Keeping those meanings clear makes the system easier to use and the remaining proof work easier to locate.

**Start with one shared universe**

Every comparison declares a universe and two predicates, called left and right. A predicate is a rule that each original object either satisfies or fails. The universe is a finite ExactPopulation definition. For integer domains, it contains a polynomial field schema and a supported Boolean combination of polynomial or modular conditions. For supported curve populations, it contains the defining equation and conditions expressed in the original integer coordinates. Coefficients follow the repository convention: constant coefficient first, followed by coefficients of increasing powers.

Both predicates are interpreted within that universe. This choice is essential. Suppose the universe contains the integers from zero through one hundred. The complement of the even integers means the odd integers inside that interval. It does not mean every odd integer anywhere. Likewise, a curve comparison with a declared height bound never silently removes that bound when forming a union or complement. Each derived population combines the original universe restriction with its additional Boolean rule.

The specification therefore has exactly three top-level keys: universe, left, and right. The implementation validates the universe and both sides eagerly. It compiles the remaining parts when they are first requested and caches them inside the comparison object. This reuse avoids repeatedly reconstructing a derived population during pages or address transport. Unsupported definitions and exceeded budgets fail explicitly. The interface does not return a partial set and describe it as complete.

**Four boxes explain every object**

Two yes-or-no rules divide the shared room into four boxes. The first contains objects satisfying both predicates. The second contains objects satisfying left and failing right. The third contains objects failing left and satisfying right. The fourth contains objects failing both. Their public names are both, left_only, right_only, and neither. Every object in the universe belongs to exactly one of these four parts.

The remaining public parts build directly on this division. Left contains both and left_only. Right contains both and right_only. Union contains the first three boxes. Symmetric_difference contains left_only and right_only: the objects admitted by exactly one rule. Universe is available as a part too. A comparison therefore exposes nine named collections with one shared original-object interpretation.

The summary computes the four counts and checks their sum against the universe count. It also checks the two side decompositions. Its union and symmetric-difference counts follow from those checked parts. Direct queries can compile and count those derived populations themselves; tests compare these direct counts with the summary. A failed identity raises an error. These runtime identities are valuable consistency checks, while the separate Lean module establishes their mathematical counterparts for abstract finite filters.

**An object is more than its address**

A rank is an object's position in one ordered collection. It is not the object's permanent identity. If a restriction removes earlier objects, the surviving object can receive a smaller rank. If a restriction removes that object itself, it has no address in the restricted collection. Copying an address between collections would confuse those two cases and could select an entirely different object.

For domain populations, original identity is the integer parameter together with the declared family and field schema. Two parameters may produce identical displayed values. For example, the square field maps negative two and positive two to the same value, four. They remain distinct original objects. A comparison cannot merge them simply because a displayed field happens to agree.

For curve populations, original identity is the integer point, its x and y coordinates, together with the defining family. A chart number or chart parameter is useful for generation but is not the shared identity. The origin can have special chart ownership; restricting a branch can change where subsequent addresses begin. Address transport therefore uses the original point instead of assuming that chart positions match.

The implementation exposes a family_id and an object_id computed with SHA-256 over versioned, deterministically serialized definitions. The family definition omits the universe predicate, so changing only a finite bound retains the same family identity. The object definition uses that family identifier and the original parameter or point. Consequently, a surviving original point retains its object_id across comparisons of the same normalized family. These identifiers are content identifiers with ordinary hash assumptions, not a theorem deciding whether arbitrary equations describe isomorphic curves.

**Moving between collections**

Transport starts by selecting the source rank in the named source part. It extracts the original parameter or integer point, asks the target population to locate that original object, and selects the corresponding target record. If the target excludes the object, transport returns null. If the target includes it, the returned record preserves its object_id while carrying the target population's record and recovered addresses.

A decorated comparison record reports the comparison identifier, family identifier, original-object identifier, four-way membership category, original backend record, and an address for each of the nine parts. A missing address is null rather than an invented negative rank. An address of zero remains a genuine address. This distinction matters in Python, JSON, and browser code because zero must not be mistaken for absence.

Classify accepts a complete backend record from a declared source part. Before recovering shared identity, it calls that source population's rank validation. A record from another population, a changed original value, or a forged population identifier is rejected. The method does not treat an untrusted displayed rank as evidence that the record is valid. Public specification and record copies can be edited by callers without changing the comparison's internal definition.

**An enormous example with small formulas**

The arithmetic exhibit uses the equation 2x² = 3y³. Its supported complete integer family consists of the origin and the points with x equal to positive or negative 18t³ and y equal to 6t², for positive integer t. Restricting y to at most 6T² gives one origin and T points on each signed branch. The total count is 2T + 1. The existing backend orders the origin first, then the positive branch, then the negative branch, with increasing t within each nonzero branch.

Choose T = 10⁴⁰. Let left require nonnegative x. Let right require y at most six hundred, which is equivalent here to t at most ten, with the origin included. Both then has eleven points. Left_only has T minus ten. Right_only has ten. Neither has T minus ten. Left has T plus one, right has twenty-one, union has T plus eleven, and symmetric_difference has T. The sum of the four boxes is exactly 2T + 1.

The first right_only point is negative eighteen, six. Its right_only address is zero. Its address in right is eleven. Its address in the universe is T plus one. It has no left address. Transporting it from right_only to universe changes its address and backend population record while preserving its original-object identifier. Transporting it to left returns null. These are concrete answers about the same mathematical point, not a positional join between unrelated rows.

The count exceeds what anyone could list in a file. The query nevertheless uses finite chart descriptions, polynomial restrictions, and exact inverse addresses. This demonstrates why a complete structured family can be useful without materializing its entire population. It does not imply that every integer equation admits such a description or that every supported operation has constant running time. More complicated predicates can require more compilation work and are subject to existing budgets.

**Using the Python interface**

PopulationComparison is available from perfectpower.population_algebra. Construct it with the shared universe and two predicates. Summary returns the specification, counts, identifiers, ordering description, identity interpretation, and stated completeness scope. Count accepts a part name, defaulting to universe. Select takes a part and zero-based rank. Locate accepts an original parameter for a domain or x and y for a curve, returning a decorated universe record or null.

Page accepts a part, starting rank, and bounded size. Sample accepts a part, sample size, seed, and optional replacement flag, using the existing exact population sampler. Optimize accepts a part and the backend's domain polynomial or curve expression objective; it returns the existing backend optimization result. It does not wrap optimizer output as a decorated comparison record. Evidence includes the summary and the exact backend evidence for all nine parts, with an explicit statement that generic Lean laws do not verify the compiler.

The existing row, node, modular-period, work, and integer-bit budgets are inherited through restrictions. An output page is bounded even when the mathematical collection is huge. Counts do not become approximate simply because the population is too large to materialize. Reproducible sampling concerns the declared exact population and sampler; it does not create a new physical probability model for a fictional machine or an application scenario.

**Commands and persistent queries**

The population-compare command reads a JSON specification from a file. With no action it prints the summary. Its rank, locate, page, sample, and transport actions expose the same implementation. Part selects the collection for rank, page, or sample operations. Transport takes a JSON triple containing source part, source rank, and target part. The checked huge-curve specification lives in receipts/population_algebra/huge-curve-spec.json.

The persistent catalogue registers kind population_comparison. Its versioned definitions, content addresses, aliases, and bounded compilation cache work as they do for other catalogue objects. Reopening the database reconstructs a comparison from its saved definition. Generic service calls expose summary, count, select, locate, classify, transport, page, sample, optimize, and evidence through the existing allowlist. The service never evaluates arbitrary Python code from a request.

The local HTTP console includes registration, partition-summary, and transport examples. Its response view displays the raw JSON text, retaining all decimal digits rather than turning enormous integers into approximate browser numbers. The service still binds to the loopback interface, checks host and origin, and handles requests serially. This release adds a local route to the walkthrough; it does not change the service into a public multi-user deployment.

**A walkthrough grounded in the engine**

The repository now contains the room of possibilities as a self-contained offline HTML artifact and editable source. Its machine workshop has 288 fictional designs, animated searching, visible constraint boundaries, saved scenes, captured requirements, and a component workbench. Scores and costs are invented teaching quantities. They are not predictions about a physical lifting machine. The mathematical hall uses real population exports and exact browser integer arithmetic for its explicit chart formula.

The new comparison notebook displays two exported backend datasets: the enormous family and the seventeen pictured points at T = 8. It shows exact four-way counts, selected original points, original-object identifiers, and addresses in all nine collections. A visitor can follow an exported point into the family exhibit or download the comparison evidence. Integer quantities in the notebook remain decimal strings; displayed arithmetic checks use BigInt.

When opened through the repository's local service at /atlas, the notebook can replay its saved registration request and ask Python for the summary. That request is preserved as JSON text so a huge bound is never rounded by a browser serialization step. The resulting response is displayed unchanged. Opening the standalone HTML remains fully offline and displays the exported evidence; local-engine replay is disabled there. The two modes have clear meanings and exercise the same declared definitions.

**What Lean establishes**

PerfectPower.PopulationPartitions proves fourteen generic theorems. The finite-filter results establish that the four membership classes cover the universe and exclude one another, give the two side cardinality identities and complementary-side identity, give the four-way total, and give union and symmetric-difference counts. They quantify over an arbitrary finite universe and decidable predicates, without depending on the illustrative equation.

The address results assume bijective maps from a common object type to address types. Transport decodes one address to the original object and encodes that object in the second address system. The theorems prove original-object preservation, round trips, composition through an intermediate address system, and injectivity. Two further results prove that a supplied predicate implication embeds one restricted object type into another while preserving its value and remaining injective.

The axiom audit records only the standard Lean dependencies propext, Classical.choice, and Quot.sound where required; the two restricted-subtype results use no axioms. There are no admitted proofs in this module. These results are foundations for future semantic links. Their bijections and predicate interpretations are explicit premises. Connecting the Python compiler, its supported curve solver, and its generated addresses to those premises remains separate formal work.

**Evidence, reproduction, and remaining work**

The comparison tests independently enumerate small integer universes, randomized polynomial and modular predicates, a bounded signed curve, and a nonlinear finite curve table. They also check empty and equal sides, duplicate projections, record validation, stable identities across bounds, huge closed-form counts, address round trips, budgets, catalogue persistence, command-line output, and HTTP preservation of large integer digits. Browser checks cover the imported counts and point identities, mobile layout, downloads, offline behavior, and live local-engine replay. Existing population and application regressions remain part of the focused validation.

Make population-algebra runs the population tests and regenerates the arithmetic receipt. Make population-algebra-lean builds the new module and runs its axiom audit. The walkthrough README describes ingestion, pinned renderer installation, rebuilding, and browser checks. Source hashes identify the exact executed Python and Lean files. An ingestion record's source_commit names its checkout base; when files were modified before ingestion, the source hashes and explicit dirty-worktree flag carry that distinction. Neither an old commit label nor an uncommitted receipt is silently represented as a clean published source tree.

On the tested hosted runtime, Lean's numeric process path was unavailable while its self path worked. An optional runner adapts only the current process's executable lookup. It requires an installed toolchain and does not replace the kernel or download caches. Ordinary installations can use standard Lake commands. The compatibility detail belongs to reproduction instructions, not to the visitor's conceptual tour.

The former 457-curve Mordell frontier remains computationally closed with the previously documented bases and integral-point lists. This addition does not prove the remaining global saturation bound, external rank-upper-bound justification, or completeness of elliptic-logarithm and LLL enumeration inside Lean. Its purpose is to make another useful piece of the framework explicit: collections can change while original objects remain recognizable, set relations can be queried without listing every object, and each level of evidence has a stated boundary. That gives applications a reliable contract and future formal work a precise target.
