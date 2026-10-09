**PerfectPower 0.6.1: checked original equations and a reproducible runtime**

**The problem this release addresses**

PerfectPower has accumulated exact arithmetic engines, complete solution registries, reusable Lean results, algebraic-curve calculations and applications. That breadth creates a practical problem: a user can receive a mathematically complete answer from Python while the recognition, dispatch and execution steps that produced it remain outside the formal proof boundary. Installing the package also previously omitted assets that several public operations needed. A reliable theorem library and a reliable delivered computation are related achievements, but one does not automatically supply the other.

This release responds to the 25-finding review with a concrete bounded proof route, packaged runtime assets, an isolated HTTP execution process, explicit industrial strategy selection, current status contracts and additional release checks. It preserves the existing mathematical and computational closures. It does not claim to finish general Baker bounds, Sturm variation, number-ring orbit bounds, arbitrary smooth metrics, all marked periods, or observed particle-physics predictions. The machine-readable current frontier accounts for every finding and names the boundary of each delivered repair.

**The new original-equation route**

The public operation is `checked-box`. Its input is an integer polynomial represented by ascending coefficients, an exponent, an integer interval for x, and optionally an integer interval for y. Coefficients and endpoints have strict integer types; Boolean values are rejected. The delivered API supports degree at most 32 and exponents from 2 through 16. These are implementation budgets. The underlying Lean completeness result is parametrized by an arbitrary coefficient list and exponent.

For explicit bounds, the theorem describes exactly those original integer pairs in the rectangle that satisfy y raised to the chosen exponent equals the original Horner polynomial. The result retains negative coordinates, negative roots, zero and both signs for even exponents. Reversed intervals describe an empty domain. No affine normalization, external curve list, supplied analytic premise or inferred global height bound appears between the original equation and the checked answer.

Python proposes a list of pairs. Lean independently evaluates the finite domain and checks that its filtered list equals the proposed literal list. A general theorem connects membership in that evaluated list to the original bounds and equation. Consequently, an omitted point, invented point or wrong coefficient makes the checked literal equality fail. The producer is useful for proposing the result, but its enumeration is not a premise of the theorem.

**Completeness for all integer roots**

When y bounds are omitted, the operation proves more than a rectangle search. It evaluates the original polynomial over the finite x interval and proposes a natural upper bound M for the absolute values. Lean checks the finite value-bound statement. Python also proposes a root cap c, and Lean checks the strict inequality M < (c+1)^d.

The generic proof is elementary and independent of Mathlib. If y^d equals a value v, then the natural absolute value of y raised to d equals the natural absolute value of v. If the absolute value of y were at least c+1, monotonicity of natural powers would force its d-th power to be at least (c+1)^d. This contradicts the checked value bound and strict cap inequality. Every possible integer root therefore lies between -c and c.

Combining that cap theorem with the literal rectangle equality produces a theorem quantified over every integer y. Only x remains bounded. For the example y²=x³-2 with -2≤x≤5, the complete answer is (3,-5) and (3,5). The generated theorem establishes that no other integer y occurs at any x in the interval. It says nothing about x outside that interval. That distinction is retained in the packet and acceptance receipt.

**Counts, addresses and optimization**

The evaluated list is ordered by increasing x and then increasing y. A checked count states its exact length. A requested selection rank produces a checked optional-list lookup equality. A reverse-rank check establishes that the selected original pair does not occur in the preceding prefix. These are statements about this evaluated original-equation list, rather than assumed abstract address bijections.

An optional integer polynomial objective in x produces the minimum over the complete finite answer. The packet retains every tied original point. Lean checks that every answer has objective at least the proposed minimum and that filtering the answer at equality returns exactly the proposed tied-minimizer list. Additional original-source theorems connect those facts to the original bounds and equation. An empty answer has no fabricated minimum.

This provides a concrete proof-producing route for bounded optimization. It does not certify the repository's entire generic optimizer, unbounded tail analysis or every population compiler. Nor does a finite-x answer settle a global Diophantine equation. The work budget is enforced before a large finite search is attempted; exceeding it produces an explicit failure rather than an incomplete list labelled complete.

**Acceptance is a separate operation**

Emission is labelled `emitted`. The checker reconstructs the expected packet from its specification and rejects any discrepancy in the proposed points, count, selections, minimum, source hash, Lean text or status. It compiles the reconstructed source, not arbitrary source supplied in a packet. It requires Lean 4.20.0 and a successful compilation of both the small generic foundation and the query instance.

Acceptance binds the normalized specification, emitted source and generic library by SHA-256. Printed axiom dependencies may contain only the standard dependencies propext, Classical.choice and Quot.sound. An unavailable toolchain, compilation failure, admitted proof, nonstandard audited axiom or timeout yields an unaccepted result. The CLI exits unsuccessfully when `--check` cannot obtain acceptance.

The foundation imports Std. The new route therefore avoids downloading or building Mathlib and avoids the repository's memory-heavy generated slab reductions. Seven retained query fixtures cover a nonempty Mordell example, negative odd powers, empty fibres, zero fibres, reversed bounds, quartic values and an explicit signed rectangle. The fixtures include rank and tied-minimum proofs. The checker still executes in Python, and input interpretation is not itself formally verified. `execution_verified=false` remains accurate even when the reconstructed theorem is kernel checked.

**A package that carries its runtime**

The wheel now includes a curated collection of certificates, data, mathematical source statements, core registry receipts, Dresden source tables, the native tuning source, current contracts and the offline atlas. A build hook copies those assets into the package and records their hashes. Resource lookup distinguishes a source checkout from an installed wheel without depending on the current working directory.

The installed-wheel test checks every asset hash and exercises a complete compiler result, the new bounded query producer, the health endpoint, the atlas endpoint and process-isolated catalogue dispatch. It runs with installed imports outside the source tree. The source distribution includes the inputs needed to reproduce the runtime wheel. The full research receipts, historical logs and heavyweight builds remain in the complete repository archive; they are not all duplicated in the runtime package.

Named dependency extras expose analytic, interval, industrial and combined research installations. A portability workflow builds and exercises installed wheels on Windows, Linux and macOS with Python 3.10 and 3.12. A separate research job installs the research extra for the focused service and arithmetic checks. These are delivered CI jobs, not a claim that every hosted platform run has already completed in this workspace.

**HTTP deadlines and process recovery**

The loopback service now uses bounded HTTP client threads and one persistent catalogue process. Catalogue queries remain serial, preserving the cache and database access model. Health and atlas requests do not wait for that process. An absolute timer limits header and body delivery, preventing an active trickle of bytes from holding a request indefinitely. The client limit bounds concurrent request handlers.

A query deadline includes queue waiting and worker response waiting. On worker timeout, the dispatcher terminates the worker and starts a fresh one for a subsequent request. The persisted database survives process replacement. The implementation does not promise a transactional rollback: a timed-out mutation may already have committed. The timeout response explicitly tells clients to inspect persisted state before retrying a mutation. Worker shutdown and process recovery are exercised by tests.

Existing error types and messages remain part of the protocol. The independent concurrent HTTP workload initially detected a formatting difference introduced by process transport; preserving the original error name and message corrected that regression. The existing population HTTP suite and concurrent replay checks pass with the isolated worker. Socket disconnects are handled without producing misleading arithmetic responses.

**Industrial evidence remains honest**

The strategy API exposes baseline replay, bounded transport batching and an explicitly experimental portfolio. The default transport path preserves the original assertions and query barriers. The portfolio cannot activate without a separate explicit opt-in. Both modes remain answer-only replay; model, proof and unsat-core forwarding are outside the interface.

The independent portfolio replication remains a negative result: 540 solved queries versus 571 for the original strategy, with approximately 48.6 percent greater summed wall time and no SAT/UNSAT conflicts. The separate transport work has a reported 4.73 percent replay improvement on its declared prefix cohort. This release does not rebrand that front-end improvement as stronger arithmetic solving, a universal speedup or a production adoption result.

**Current status and remaining mathematics**

The current-frontier JSON accounts for all 25 findings exactly once. Six have implemented infrastructure repairs, one has an explicit mitigation and seven have a new bounded proof route. Eleven remain research obligations. The bounded extensions also retain their broader unbounded obligations. The release manifest requires source paths and regression checks for each new capability; release verification includes focused arithmetic and service tests, installed-wheel reproduction and explicit kernel checks.

The original 457-curve Mordell frontier remains computationally closed. Its curve-specific global rank, saturation and integral-coordinate proofs remain open in Lean. General Sturm correctness, Matveev, effective number-ring completion, global smooth/mesh identification, arbitrary certified periods and all-level Weil formalization remain separate mathematical tasks. The latest wall, dyadic-reduction and Kummer Stokes closures are preserved. Incoming commits through 5778ed8 add certified Stokes data without closed forms, repeated eigenvalues and ramified scalar reductions within their stated framework, and a completed wall-network scan. Arbitrary irregular systems beyond that framework, wild genus-two conductors at 2, interval bounces and physical flavor selection retain their declared limits.

Two historical regression assumptions also receive corrections. The elliptic frontier test now checks the current 457 matching witnesses and zero remaining external-list rows while retaining the distinction from formal closure. The wall receipt test compares numerical stability of precision-dependent certified bounds at controlled precision; independently rounded upper and lower bounds are not necessarily overlapping enclosures of one exact scalar. It retains the independently computed positive-gap requirement.

The release's principal advance is a small, executable bridge from an original bounded equation to a checked complete answer with usable counts, addresses and minima. The packaging and service work make that bridge accessible beyond a research checkout. The current contracts keep unresolved global mathematics visible rather than turning implementation breadth into a claim of universal completion.
