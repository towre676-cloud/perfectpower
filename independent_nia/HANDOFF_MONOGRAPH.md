# Exact arithmetic certificates in real verification workflows

## The immediate result

The blocked Zenodo host does not prevent independent workload acquisition. This handoff contains 69 upstream QF_NIA files obtained through GitHub, with exact blob hashes and preserved source bytes. It includes industrial ELSTER test-generation submissions, independently maintained cvc5 regressions, and a mathematical sample retrieved from STAUB. Their provenance and purpose remain distinct. We did not download the Zenodo benchmark archive, reproduce a competition corpus, or run a solver performance study.

The useful scientific finding is restrained. The conservative recognizer parses every bundled file but sees no direct univariate square/cube atoms in the 19 industrial files. It sees four orientations of three equations across three cvc5 files. One candidate is part of an intentional option-parsing error test, one accompanies an integer exponentiation extension, and the remaining example has small finite variable domains. None is an end-to-end checked replacement. This corpus establishes an independent testbed and exposes a coverage gap; it does not establish industrial demand for the current certificate fragment.

That distinction matters to the project's commercial ambition. A mathematically powerful method has monetary utility when its supported structure occurs in expensive obligations that a real customer repeatedly solves, and when the replacement fits the customer's trust and tooling requirements. Counting equations with a QF_NIA declaration does not measure that overlap.

## What was acquired

| Source and role | Included files | Query commands | Main interpretation limit |
|---|---:|---:|---|
| SMT-LIB ELSTER incremental industrial submission | 19 of 181 | 12,801 | Smallest-file stratified sample; no direct power matches |
| cvc5 QF_NIA regression subset | 49 of 292 scanned SMT2 files | 58 | Regression harness conditions, intentional errors, and extensions |
| STAUB three-cubes motivating sample | 1 | 1 | Crafted mathematical case outside the current direct univariate target |

The ELSTER selector chooses one smallest file per available combination of type, query variant, and form. Ties are broken by upstream path. This creates a manageable offline sample with visible source diversity. It introduces size bias and keeps many siblings from one generator; it does not justify a claim about the distribution of customer verification obligations. The complete directory index makes the missing files visible and permits expansion without selecting favorable cases after inspecting performance.

The cvc5 selector inspects all 292 SMT2 files under the three `regress[012]/nl` directories at one pinned commit and includes all 49 with an explicit QF_NIA declaration. Twenty-nine included files contain integer bitwise or exponentiation extensions detected by the structural profiler. Two have harness directives expecting failure. These remain useful negative and interoperability cases, but they need separate outcome labels. An error-handling regression can be a soundness test for an adapter and still be unsuitable for a performance claim.

The sum-of-three-cubes example asserts

\[
x^3+y^3+z^3=855,\qquad x,y,z\in\mathbb Z.
\]

Its source metadata says SAT. That metadata is not a certificate. The equation has three integer unknowns and is not automatically an instance of a two-variable univariate perfect-power equation. Its presence helps test honest rejection of an attractive unsupported problem.

## The replacement theorem that actually matters

Let a supported atom be

\[
A(n,m):\quad m^d=F(n),\qquad F\in\mathbb Z[n],\quad d\ge2.
\]

An exact solution list is useful only when a checked theorem states completeness on the domain that the source query uses. If a finite list \(L\) is complete on a domain \(D\), the relevant statement is

\[
\forall n,m\in\mathbb Z,\quad
D(n,m)\Longrightarrow
\left(A(n,m)\iff
\bigvee_{(a,b)\in L}(n=a\land m=b)\right).
\]

Under assumptions that establish \(D\), this permits a formula replacement in a larger conjunction. If the finite list is empty, the conclusion is impossibility on that domain. If the theorem only proves that the solution set is finite, no such empty-list conclusion follows. If the list records nonnegative magnitudes for an even power, both signed witnesses must be reconstructed before substitution into an unrestricted integer query.

For a verification goal \(G\) under hypotheses \(\Gamma\), the usual logical target is

\[
\Gamma\models G
\quad\Longleftrightarrow\quad
\Gamma\land\neg G\text{ is UNSAT}.
\]

A witness satisfying the original formula is evidence of SAT when its arithmetic and other constraints are checked. UNSAT requires an argument covering every possible witness. A successful bounded search, an unsuccessful bounded search, a finiteness theorem, an enumeration algorithm, and a kernel-checked completeness theorem are different deliverables. Preserve that distinction in the adapter's types and result records.

The present compiler uses a positive input argument. Thus a theorem for \(n\ge1\) cannot be applied to an unconstrained SMT Int symbol. An adapter can establish positivity from live assumptions, or perform a checked partition:

\[
\mathbb Z=\{n>0\}\;\dot\cup\;\{0\}\;\dot\cup\;\{n<0\}.
\]

The negative branch can use \(n=-t\), \(t\ge1\), with polynomial \(F(-t)\). If \(F(n)=\sum_i a_i n^i\), its transported coefficients are \((-1)^i a_i\). The zero branch reduces to the exact constant equation \(m^d=F(0)\). Each branch needs its own checked transport and relevant completeness argument. The partition is a sound design route, not an implemented source-language certificate in this package.

## Why normalization is a proof obligation

Recognition should normalize integer polynomials exactly. Coefficients must not pass through floating point. An affine cube

\[
F(n)=(rn+s)^3+k
\]

has coefficients

\[
a_3=r^3,\qquad a_2=3r^2s,\qquad
a_1=3rs^2,\qquad a_0=s^3+k.
\]

All four equalities must hold exactly before transferring a square equation to a solved Mordell model. The transformed variable \(t=rn+s\) carries its image constraints. A theorem enumerating points on \(m^2=t^3+k\) must be followed by the exact filter \(r\mid(t-s)\), the transported input domain, and witness reconstruction. Dropping an image filter can add spurious solutions; dropping a legitimate witness or domain branch can make an UNSAT claim unsound.

The included parser does something much narrower. It recognizes supported polynomial atoms only when directly asserted or inside a positive conjunction. It does not expand let-bindings, normalize arbitrary Boolean contexts, infer domains, replay the incremental assertion stack, or produce a proof term. Its sparse polynomial arithmetic has explicit degree and term caps. It is a triage tool, and its four candidate occurrences must remain labeled as such.

Future normalization can legitimately recover hidden matches under let-bindings or definitions, but every rewrite used in a checked substitution needs an explicit semantics-preserving justification. A detector should return the source term, normalized polynomial, free symbols, sort information, assumptions, and query identity. A certificate attached only to a coefficient vector, without binding it to the actual source query, is inadequate for deployment.

## Infinite families can also help, with a different contract

An exact infinite parametrization can compress a supported relation. For example, over integers,

\[
x^2=y^3
\quad\Longleftrightarrow\quad
\exists t\in\mathbb Z_{\ge0},\ \exists\varepsilon\in\{-1,1\},
\quad y=t^2\land x=\varepsilon t^3.
\]

Zero is included and the two signs coincide there. A formal completeness proof can use divisibility of prime exponents. This mathematical relation illustrates a possible elimination route, but the substitution introduces a parameter and might leave nonlinear arithmetic of comparable difficulty. It is useful only when the residual constraints become simpler and the consumer accepts the checked transformation.

In the bundled `disj-eval` regression, x is restricted to \(\{5,7,9,27,10\}\) and y to \(\{0,1,9,8\}\). Direct exact evaluation of those twenty pairs leaves \((27,9)\). That tiny example does not demonstrate a need for an advanced certificate engine. It is useful as a transparent integration exercise for preserving finite domains and checking the original formula.

Pell-orbit descriptions and filtered infinite families need equally precise interfaces. Finding a witness through an orbit gives a candidate SAT witness, which can be checked against the source formula. Failing to find one in the first few orbit steps gives no general UNSAT conclusion. A filtered family can have uncertain infinitude even when its generator is exact. The existing plan status must survive all the way into the adapter's answer rather than being flattened to a Boolean solved flag.

## The trust boundary for AdaCore-related use

The plausible AdaCore-related application is specialized discharge of mathematical integer obligations arising within a verification workflow. It remains a hypothesis to validate with actual customer or tool-generated obligations. This sample consists primarily of tax-form constraints and solver regressions; it is not a GNATprove/SPARK corpus and provides no evidence that AdaCore would pay for this fragment.

There are several possible product contracts. A first product can produce a Lean-checked arithmetic audit beside the original solver obligation. A stronger product can emit certificates accepted by a defined downstream checker. A more ambitious integration can provide a justified translation through Why3 or another verification layer. Those contracts have different engineering costs. A Lean kernel accepting a theorem does not automatically make that theorem an accepted proof in an AdaCore workflow.

The source semantics matter. A mathematical Int equation, bounded machine arithmetic, modular arithmetic, floating point, and language-specific division are not interchangeable. Any adapter handling a source-program expression must establish that its integer model and range assumptions describe the original operation. For SMT `div` and `mod`, negative arguments and zero denominators need particular care; do not translate through a host-language operator merely because the printed names resemble one another. Unsupported semantics should trigger fallback rather than an arithmetic theorem about a different formula.

The practical customer value is reproducible reduction in proof latency or manual intervention under an acceptable trust model. Exact certificates can also reduce repeated work by caching a checked result whose normalized statement and assumptions remain unchanged. Cache reuse needs a stable statement identity and checker/version binding. A theorem about a nearby polynomial is not a valid cache hit.

## A measurable economic model

Let \(N\) be annual obligation instances, \(p\) the fraction genuinely eligible for a checked replacement, \(t_s\) the mean baseline solver time on those instances, \(t_c\) the checking time, \(t_r\) residual solving time, and \(t_f\) routing overhead on all instances. Let \(K\) be the number of distinct eligible statements, and \(t_g\) the certificate-generation cost per distinct statement. A simplified annual compute-time saving is

\[
\Delta T=Np(t_s-t_c-t_r)-Nt_f-Kt_g.
\]

This is a planning equation, not a measured result. It shows why fast rejection of unsupported inputs and reuse of checked certificates matter. It also shows why an engine with impressive mathematics but negligible eligible coverage can have negative net benefit.

If a statement is reused \(R\) times, a simple per-instance specialized cost is

\[
t_{\mathrm{special}}=t_f+t_c+t_r+\frac{t_g}{R}.
\]

The specialized route improves compute time only when this is below the relevant baseline on that statement. Generation can be expensive and still be worthwhile for highly reused statements; a costly one-off certificate may not be.

A customer-specific monetary model can then combine measured compute and engineering effects:

\[
V=\frac{\Delta T}{3600}c_h+H_ec_e-C_{\mathrm{integration}}-C_{\mathrm{operation}}.
\]

Here \(c_h\) is the customer's marginal compute cost per hour, \(H_e\) the observed engineering hours saved, and \(c_e\) that customer's chosen value per engineering hour. No price assumptions are supplied. Avoid counting time saved twice, treating available machine time as billable savings without evidence, or claiming risk reduction from an unvalidated workflow. A purchaser can value shorter development cycles even when direct compute cost is small, but that effect needs its own evidence.

| Evidence stage | Measure | Decision enabled |
|---|---|---|
| Source acquisition | Hashes, licensing, cohort boundaries | Is the workload real and reproducible? |
| Fragment coverage | Eligible live queries over all relevant queries | Does this buyer actually generate supported structure? |
| Correctness bridge | Checked source binding, domains, theorem and consumer | Can the replacement be trusted in this workflow? |
| Performance | Generation, checking, routing, residual and baseline times | Does specialization reduce total work? |
| Reuse and maintenance | Distinct statements, cache hits, integration effort | Is recurring value sufficient for a paid product? |

The immediate high-value experiment is a real verification corpus with expensive supported arithmetic obligations and repeated statements. The mathematical roadmap should follow that corpus. Adding a large theorem family with no observed customer overlap can be intellectually valuable while leaving the commercial experiment unresolved.

## Evaluation design that survives scrutiny

Record the original source SHA, exact solver version, invocation, timeout policy, hardware, and project revision. Keep original files unchanged. Match incremental queries to the live assertion stack and assumptions; a file can contain thousands of related checks. Use a consistent comparison policy for complete query streams and clearly label partial timeouts. Report unsupported inputs, solver errors, UNKNOWN answers, and intentional harness failures separately.

Measure certificate generation and checking separately, then include routing and residual solver cost in the end-to-end comparison. Count cache hits and distinct checked statements. An acceleration measured after precomputing certificates is a reuse experiment; show the amortization assumption. A cold run is a different experiment.

Use held-out source families or projects. Randomly splitting siblings from the same generator risks learning the template rather than demonstrating general usefulness. The bundled ELSTER sample is intentionally small and size-biased; expand it or obtain customer workloads before a general performance claim. The complete index prevents quiet omission of unfavorable siblings.

The supplied baseline runner launches an installed solver directly without a shell. It preserves the source input and records statuses, exit outcome, runtime, stderr, and harness directives. It does not reproduce cvc5's harness automatically, check proof objects, or time each incremental query interactively. An interactive query-level benchmark harness is a separate implementation task. Solver status output is a claim to be interpreted under the selected configuration, not a new trusted certificate.

## What Claude should deliver next

The accompanying work order asks Claude to reproduce integrity and structural inspection, establish raw baselines where solver tools are available, and implement a fail-closed integration in a separate PerfectPower working branch. It directs attention to domain transport, even-power witnesses, incremental assumptions, certificate/source binding, and meaningful negative tests. It preserves existing distinctions among complete finite results, structured families, filtered families, finiteness-only classifications, and unavailable enumeration.

There is no requirement to manufacture a positive coverage result. If this corpus does not expose a valuable supported obligation, the right deliverable is an explicit coverage diagnosis and a targeted request for a real workload that would test the next fragment. If a certified substitution does occur, the deliverable must include its checked evidence, unchanged source identity, measured baseline, total specialized cost, and downstream trust contract.

The package itself has completed byte-exact acquisition and structural inspection. It has not run Z3, cvc5, Lean, Mathlib, or the PerfectPower solver on these obligations. All such claims remain pending. Its value is that Claude can start from concrete independent inputs and a precise experiment rather than another blocked download or an assumed commercial result.
