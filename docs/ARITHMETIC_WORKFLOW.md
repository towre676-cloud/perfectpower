# PerfectPower in a real software verification workflow

## What this round establishes

PerfectPower now has a concrete, independently authored software workload on which a proposed extension measurably helps. The program is an integer-square-root implementation from the Why3 examples, rather than a Diophantine equation constructed to fit PerfectPower. Why3 1.6.0 generated the obligations from the unmodified program. The measured extension adds guarded unsigned bitvector facts proved in Lean 4.20. It preserves the original assertions, uses exact machine-word semantics, and gives a source-bound certificate for every added fact.

The latest full batch contains 134 native-bitvector obligations for 16-, 32- and 64-bit Von Neumann square root. Under a three-second Z3 limit, the baseline proves 128 and the selective adapter proves 130. The measured total falls from 26.7394 seconds to 19.7118 seconds, a 26.3 percent reduction. Preparation is included in the adapter total. These are measurements on one shared machine and one pinned workload, not a forecast of industrial throughput.

The strongest repeated result is the 64-bit terminal bound. The baseline times out in all five seeds tested; the adapted task proves in all five, with a median of approximately 18.6 milliseconds including preparation. The 64-bit subtraction-assignment obligation proves in three of five baseline runs and in five of five adapted runs, with an adapted median of approximately 27.4 milliseconds. A 32-bit terminal obligation improves in three of five runs under the default selective policy. Four other hard obligations remain unsolved in every repeated run under that policy. The raw receipts include unsuccessful attempts and regressions.

This is an extension to the coverage of PerfectPower, not a demonstration that its existing Mordell/Pell adapter already helped these programs. Running that existing adapter against the 32 ordinary square-root obligations and the 134 native-bitvector obligations gives zero replacements across all 166 tasks. The ordinary 32 obligations are already easy for Z3 and provide a negative performance control. Their existence is useful: a benchmark should distinguish an actual need for arithmetic assistance from an example that simply contains a square.

This round was prepared against commit `63787ac`. In this repository the modules are integrated as `PerfectPower/BVWorkflow.lean`, `PerfectPower/ArithmeticWorkflow.lean` and the generated `PerfectPower/Generated/WorkflowInstances.lean` (307 instances) and `WorkflowContexts.lean` (4 complete ground contexts). They are imported by the root module, listed in the axiom audit and linted, and the Python adapter is `python/perfectpower/unsigned_adapter.py`. The fixtures, scripts and receipts are in `why3_isqrt/`. The paired benchmark was re-run in this repository with the same Z3: 128 → 130 solved and 28.50 → 21.18 seconds on the full batch, and 3 → 13 of 35 runs on the hard set (`why3_isqrt/README.md`); `docs/RELEASE_CHECK.md` records which checks the release ran.

## The independently authored programs

The main example is `examples/isqrt_von_neumann.mlw` from the independently authored Why3 tree at commit `ea0810ea51a237280dcd800490b5dcebb6bc3d9e`. The program credits Claude Marché and Sylvain Dailler. The official Toccata gallery describes the same algorithmic family at https://toccata.gitlabpages.inria.fr/toccata/gallery/isqrt_von_neumann.en.html. The exact pinned source in the archive is the experimental authority; a current gallery page can differ in its toolchain or proof results.

The ordinary control is `examples/isqrt.mlw` from the same tree. Its loop invariants already express the square relation effectively, and all 32 exported obligations solve quickly without this extension. A micro-C square-root example and a counterexample benchmark are also retained as leads. They are not added to the primary timing population.

AdaCore's independently authored SPARK regression files are retained at commit `627d89b487155aa5f925a96e4492931047ca0f8b`. The Von Neumann test lives in `testsuite/gnatprove/tests/QA31-008__von_neumann_sqrt`; a separate counterexample square-root test includes an intentionally nonconforming variant. Those files make the industrial connection concrete: there is actual SPARK arithmetic verification work in this neighborhood. Their saved warnings were inspected, but GNATprove was not run and no AdaCore warning is claimed to be fixed by this experiment. AdaCore's manual-proof documentation, https://docs.adacore.com/spark2014-docs/html/ug/en/source/manual_proof.html, explains the role of external proof support in that workflow.

A second independent mathematical source is Mark Dickinson's CPython integer-square-root proof, from `mdickinson/snippets` at commit `41ce2d256fef06fb32f24fe7014cfa95173ac5e0`. The handoff includes the source proof and its license. This round adapts its scaled-Newton statement to the repository's older Lean 4.20 toolchain and proves the exact division statement. That is useful proof infrastructure; it is not a performance result for CPython and does not prove the compiled Python interpreter correct.

Every supplied upstream file is pinned, attributed, and hashed in the manifest. The raw tasks contain their original Why3 path comments. Regenerating a task at a different path can change its byte hash even when its mathematical formula is unchanged. Certificates bind the actual delivered bytes, so re-exporting requires re-derivation rather than blindly reusing an old receipt.

## The exact machine arithmetic that removes search

A word of width $w$ belongs to

$$
\mathrm{BV}_w=\mathbb Z/2^w\mathbb Z,
\qquad
\mathrm{val}_w:\mathrm{BV}_w\longrightarrow\lbrace 0,\ldots,2^w-1\rbrace.
$$

The adapter uses unsigned order, written $\le_u$. Word subtraction wraps modulo $2^w$. Consequently the naive integer inequality $n-b\le n$ is false for an arbitrary word subtraction: for an eight-bit word, $0-1=255$. The guard is part of the theorem and must come from the active original context.

The proved rule is

$$
b\le_u n\quad\Longrightarrow\quad
 \mathrm{val}_w(n-b)=\mathrm{val}_w(n)-\mathrm{val}_w(b)
 \quad\Longrightarrow\quad n-b\le_u n.
$$

Transitivity gives the reusable specialization

$$
b\le_u n\ \land\ n\le_u x\ \Longrightarrow\ n-b\le_u x.
$$

`PerfectPower.BVWorkflow.sub_le_self` uses Lean's exact `BitVec.toNat_sub_of_le` theorem to transport the guarded subtraction to natural subtraction. `sub_le_bound` applies unsigned transitivity. A Boolean version, `ule_sub_bound`, matches SMT-LIB's unsigned predicate. The theorem is valid for every width, including the degenerate zero-width type. No analytic premise, curve census, norm representative, or external number-theory theorem appears.

The assignment obligation is equally explicit:

$$
a=n-b,\quad b\le_u n,\quad n\le_u x
 \quad\Longrightarrow\quad a\le_u x.
$$

That is the loop-preservation condition in the three width variants of the original Why3 example. It is a trivial mathematical consequence once the guard is known. In the complete original 64-bit solver context, however, Z3 also sees nonlinear products, shifts, disjunctions, and quantified arithmetic lemmas. The point of the accelerator is to supply the useful consequence directly so the solver need not rediscover it inside that context.

The terminal bound has another short proof. The original context contains a final shift exponent $m=0$, the residual relation $x-\mathrm{num}=\mathrm{sqr}(r_g)$, the unsigned invariant $\mathrm{num}\le_u x$, and the readout

$$
r=r_g\,(1\ll m).
$$

At $m=0$, the readout is exactly $r=r_g$. Therefore

$$
\mathrm{sqr}(r)=\mathrm{sqr}(r_g)=x-\mathrm{num}\le_u x.
$$

`terminal_square_bound` proves this even for an arbitrary function `sqr`. The task parser also expands the actual source definition `sqr r = r*r`, and the generated complete-context theorem proves that normalized ground implication. The proof neither estimates a square root nor enumerates words.

These four translated complete ground contexts are checked in Lean: the 16-, 32- and 64-bit subtraction assignments and the 64-bit terminal bound. Every original ground premise is retained in their statements. Quantified premises are omitted, making the implication stronger. The generated proofs use only the relevant guard, readout, residual and assignment equalities. Thus the central examples have direct mathematical proofs of their full normalized ground implications, in addition to successful SMT replay with added facts.

## Why adding a theorem preserves the task

Let $C$ be the conjunction of the original active assertions, and suppose a checked instance gives $C\Rightarrow L$. Then

$$
C\iff C\land L.
$$

This equivalence preserves both satisfiability and unsatisfiability. The implementation adds the ground fact $L$ immediately before the original single `check-sat`. It leaves the original declarations, definitions and assertions intact. It does not replace a machine multiplication with integer multiplication or assume that a shift cannot overflow.

Each certificate records the exact task SHA-256, the word width, the subtraction operands, the target upper bound, the original assertion carrying the subtraction, and the assertion indexes supplying the guard and optional upper bound. Checking a certificate re-derives the permitted instances from the original parsed task. Any proposed step must equal one of those permitted instances. Changing the source, width, operand, fact, or assertion index invalidates the corresponding certificate.

The source boundary is deliberately conservative. There must be exactly one query. Only an explicit whitelist of declaration, definition, metadata, assertion and final-query commands is accepted. Push/pop, reset, multiple queries and assertions after the query are rejected. Strings and quoted symbols are scanned correctly, so a comment-looking semicolon inside a symbol cannot erase a guard and a query-looking string cannot create a query. Signed inequalities are not reinterpreted as unsigned inequalities. A theorem cannot borrow a premise from a later scope or future assertion.

This is a checked arithmetic rule with a Python semantic import boundary, not a fully verified SMT parser. Z3's parser normalizes the source into an AST; the generator translates supported bitvector operations and ground propositions to Lean. The translator and the connection between source bytes and the parsed mathematical statement still require review or formalization. Source hashing prevents accidental receipt reuse, but a hash alone does not prove that a translation is correct. A customer should be told exactly where this boundary lies.

The remaining proof consumer also matters. The measured solver continues to be Z3. The complete-context Lean theorems give independent evidence for four implications, while the other accelerated tasks use the generic checked rule and standard SMT proof discharge. There is no claim that all 130 successful solver answers have complete Lean proofs of their entire verification conditions.

## Selectivity and the measurements

The default policy applies the rule only when the final goal is an unsigned upper-bound goal and a derived fact shares its upper-bound term. This is a syntax-based rule over the formula, not a list of favorable task names. It selects nine of the 134 original native-bitvector tasks. All selected facts still have to pass the same arithmetic certificate check. The policy influences performance, never mathematical validity.

The exploratory all-facts policy is also supplied. In an earlier full-batch run, it proves 129 of 134 tasks and takes 25.82 seconds including preparation, compared with 26.70 seconds for the corresponding baseline. Some easy tasks become slower, and one 64-bit obligation rises from roughly 0.47 seconds to roughly 2.18 seconds. Valid lemmas can still damage solver heuristics. The experiment keeps this receipt so a later developer cannot mistake indiscriminate fact injection for a sound performance strategy.

The final default-policy full-batch run proves 130 of 134 tasks, compared with 128 of 134 for its paired baseline. Its totals are 19.71 and 26.74 seconds respectively. The two new completions are a 32-bit terminal-bound obligation and the 64-bit terminal-bound obligation. A 64-bit subtraction obligation already fits the three-second limit in seed zero but becomes much faster. Completion counts and timings should be reported together: a timeout becoming a proof is often more valuable than shaving milliseconds off an easy proof.

The hard-case population was selected by an earlier complete one-second baseline, which left seven obligations unproved. Every one of those seven is replayed with seeds 0, 1, 2, 3 and 4 at the three-second limit. The default-policy baseline proves 3 of 35 task/seed runs; the adapted arm proves 13 of 35. The totals are approximately 102.98 and 68.99 seconds. These repeated results are reported separately from the full 134-task run, so the reader can see both the whole-population result and the sensitivity of difficult cases.

The benchmark alternates arm order by seed, runs each solver as a separate process, sets Z3's time limit, and enforces an external watchdog. The adapter totals include parsing, matching, certificate derivation and checking. They do not include the one-time Lean proof-library build, pip installation, or a new Python process startup for each task. The wrapper's startup cost belongs in a future host-session measurement. The handoff explicitly records that exclusion; its approximately 18-millisecond hot-path result is not a cold installation time.

The core bitvector theorem, all 307 generated arithmetic instances, and four complete ground contexts compile with Lean 4.20. Their axiom lists contain only standard Lean axioms; they contain no `sorryAx` or project-specific mathematical premise. The Mathlib-dependent integer module also compiles and prints standard axiom lists. Nineteen Python regressions cover forged certificates, changing source bytes, missing guards, signed comparisons, scope changes, quoted strings, a controlled buggy post-state, and independent arithmetic oracles.

One negative control changes the real terminal readout to $r=r_g+1$, and uses the concrete state

$$
x=\mathrm{num}=r_g=m=\mathrm{bits}=\mathrm{bits}_g=0,\qquad r=1.
$$

The ground slice of that mutated source is satisfiable before and after injection, as it should be: $r^2=1\nleq 0=x$. A valid subtraction lemma must not conceal that bug. The complete quantified mutated task times out in both solver arms; no satisfiability claim is made for that harder quantified file. Both the full mutated source and its clearly labeled ground slice are included.

## The supplementary integer-square-root proofs

Machine arithmetic should remain machine arithmetic. Separately, mathematical-integer divisions in an algorithm can be proved by exact quotient bounds rather than by solver search. The integer module establishes a Newton upper-bound lemma using a polynomial identity.

For integers $x,y,q,z$, assume $y,q,z\ge0$, $x<qy+y$, and $q+y\le2z+1$. Then

$$
\begin{aligned}
4\big((z+1)^2-x-1\big)
={}&(2z+1-q-y)(2z+3+q+y)\\
&+(q+1-y)^2+4(qy+y-x-1).
\end{aligned}
$$

Every term on the right is nonnegative, so $x<(z+1)^2$. The constant one is intentional: over integers, a strict inequality supplies one unit of slack. This identity exposes the certificate that a nonlinear solver would otherwise have to discover.

For the scaled Newton step, let $m,a>0$, $4m^4\le n$, and

$$
(a-1)^2<\left\lfloor\frac{n}{4m^2}\right\rfloor<(a+1)^2.
$$

Define

$$
q=\left\lfloor\frac{n}{4ma}\right\rfloor,
 \qquad b=ma+q.
$$

The theorem `scaled_newton_exact` proves

$$
b>0,\qquad(b-1)^2<n<(b+1)^2.
$$

Positive divisors make Lean's Euclidean division coincide with ordinary floor division. The proof derives the quotient inequalities rather than assuming them externally. In particular,

$$
4m^2(a-1)^2<n<4m^2(a+1)^2,
 \qquad4maq\le n<4ma(q+1).
$$

The scale bound and upper enclosure force $m\le a$. Put

$$
c=4ma,
 \quad v=c(ma+q-1),
 \quad w=4m^2a^2+n-4m^2.
$$

The lower-bound certificate is

$$
16m^2a^2n-w^2
=\big(n-4m^2(a-1)^2\big)
 \big(4m^2(a+1)^2-n\big)>0.
$$

The floor bound and $m\le a$ give $0\le v\le w$, hence $v^2\le w^2$. Therefore

$$
c^2\big(n-(ma+q-1)^2\big)
 =16m^2a^2n-v^2>0,
$$

which forces the strict lower enclosure. The upper enclosure follows from

$$
(ma+q+1)^2-4ma(q+1)=(ma-q-1)^2\ge0.
$$

These proofs compile in the repository's exact Lean/Mathlib version. Independent Python checks compare eligible approximants against `math.isqrt` and test the polynomial identities on unrelated integer values. Those checks are regression oracles, not replacements for the Lean proof. No automatic CPython or GNATprove accelerator is claimed for this theorem yet.

## What AdaCore or Galois could value

In basic terms, the useful component is an arithmetic expert that can hand a verification tool a small exact fact it was struggling to find. The customer keeps its program and its verification workflow. The extra component notices a supported arithmetic shape, checks the required preconditions, supplies a theorem instance, and leaves the rest of the proof to the existing tool.

For AdaCore, the concrete lead is SPARK arithmetic verification: an actual upstream regression already uses Von Neumann integer square root, and GNATprove's proof infrastructure is related to Why3. The result here shows a nearby independently authored Why3 workload benefiting from exactly typed unsigned arithmetic support. An engineering conversation can begin with the pinned program, raw obligations, proof statements, measurements and negative controls, instead of with a general claim that advanced number theory must be commercially useful.

For Galois, the relevant capability is similarly modular proof support for arithmetic primitives in a verification pipeline. A credible integration should export explicit theorem statements, preserve bit widths and signedness, bind them to the live obligations, and expose the remaining proof assumptions. This experiment demonstrates those design choices in one bounded setting. It does not demonstrate integration with SAW, Cryptol, or a Galois customer project. That is a further consumer exercise, not a claim to place in a sales description.

The arithmetic lemma itself is elementary and can be written by a competent verification engineer. Its mathematics is not the commercial moat. The potential value is reusable recognition, reliable semantic guards, independently checked proof instances, source-bound receipts, and measured reduction of repeated proof work across a changing codebase. A company would compare the cost of maintaining that component with the cost of writing and maintaining local proof hints itself.

A useful value model separates solver seconds from engineer effort:

$$
V\approx C_{\rm eng}H_{\rm avoided}
 +C_{\rm compute}T_{\rm saved}
 +C_{\rm delay}D_{\rm avoided}
 -C_{\rm integration}-C_{\rm maintenance}.
$$

This round measures one contribution to $T_{\rm saved}$, and demonstrates additional obligations closed. It does not measure $H_{\rm avoided}$, $D_{\rm avoided}$, or a customer's willingness to pay. The larger opportunity is often avoiding a manual proof detour or a fragile annotation after a source change, but that opportunity must be measured on a real team's workflow.

The existing complete-solution-set machinery remains valuable for its supported Diophantine families. This experiment shows that reaching ordinary verification software requires broader supported shapes. A typed arithmetic-certificate layer can include both complete finite solution sets and guarded inequalities. They need different semantic contracts: an integer enumeration gives an exact equivalence over all integers, while a word inequality requires explicit machine-width and guard information. Combining their implementation should never erase that distinction.

## The next substantial work

**Native Why3 proof sessions: done, and the result is neutral** (`why3_isqrt/native_session.py`, `why3_isqrt/sessions/`, `receipts/why3_session.json`).

Setup:
- The program is Why3's own `examples/isqrt_von_neumann.mlw`, unmodified in the baseline arm.
- The rule arm adds one lemma per module, `ule b n -> ule n x -> ule (sub n b) x` (`BVWorkflow.sub_le_bound`). Why3 must prove the lemma itself in the session; nothing is admitted.
- Both arms run the same automatic script: `split_vc`, then Z3 5.1.0 at 3 s on every leaf, with no manual step.
- Why3 1.6.0's shell cannot add a file non-interactively, so the sessions are built with Why3's own tools. A skeleton session names the top-level goals, and `why3 replay -f` expands `split_vc` and computes the shapes. A Z3 attempt is then attached to every leaf, and `why3 replay -f` runs them and records the results.
- `make why3-session` replays both committed sessions with `why3 replay` (no `-f`). Both replay with exit code 0.

Results:

| arm | goals | proved | prover time |
|---|---:|---:|---:|
| baseline | 132 | 125 | 22.15 s |
| rule (lemma for every goal) | 133 (incl. the lemma) | 125 | 19.97 s |

The global lemma discharges **no new goal** and loses one (`isqrt32'vc.41`), while total prover time falls by about 10%. The seven baseline failures are `isqrt32'vc.29, .40, .42` and `isqrt64'vc.26, .29, .40, .43`. This agrees with the SMT experiment: injecting the rule everywhere is not a sound performance strategy, and the 128 → 130 gain there came from the selective policy.

The next native step is that policy: keep the lemma only in the selected goals (Why3's `remove` transformation on the others), and measure again. The scheduler problem recorded earlier was environment-specific: here the scheduler runs.

After that, run the pinned SPARK regression through GNATprove and count matches honestly. A zero-match result is still useful information: it says that the relevant GNATprove encoding needs a different bridge. Maintain explicit widths, signedness and overflow hypotheses. Do not claim that the Why3 measurements automatically transfer to Ada's checked arithmetic or to GNATprove's exact encoding.

The residual genuine hard obligations concern shifts, square identities and word range invariants. They are better next proof problems for this software workflow than another curve chosen solely because its number-theory pipeline is ready. A guarded multiplication theorem must prove that the required product does not wrap; a shift theorem must carry its range restriction; an inequality transport must distinguish signed and unsigned order. Add each rule with a satisfiable control, a forged-certificate test, and a full-population timing replay.

The key trust improvement is certifying the source-to-theorem import. The existing four complete ground contexts are a useful starting point because they expose exactly which program assumptions are necessary. A verified bitvector AST interpretation and a checked context-to-lemma application would let the kernel validate the relationship rather than leaving it to Python review. A smaller alternative is an explicit host proof obligation that checks each imported theorem specialization in the host's own semantics. Either route must be demonstrated before asserting an end-to-end kernel guarantee for arbitrary incoming SMT tasks.

Finally, keep the commercial evaluation independent. Run another independently authored arithmetic component, and then a customer-approved workload if available. Report the denominator, timeouts, unsupported formulas, preprocessing overhead, cold proof-library cost, manual proof edits, and behavior after a controlled source change. The right next claim is specific: a reviewed integration closes certain original obligations and reduces measured proof effort. That is enough to substantiate a technical pilot, without inventing an industrial deployment or a purchase commitment.

## Reproduction and handoff

`START_HERE.md` gives exact commands. `receipts/summary.json` gives the populations, completion counts, budgets, timing exclusions and repeated hard-case results. The paired raw receipts retain every task and seed. `MANIFEST.json` binds the delivered files. `verify_handoff.py` checks the hashes, re-derives the arithmetic instances, runs the regression oracles, and optionally reruns the core Lean proofs. The Mathlib-dependent module is checked separately against the supplied source snapshot.

The archive contains the source snapshot, proposed overlay, standalone experiment, pinned independent sources and their licenses, raw tasks, negative controls, proof generators and receipts. It excludes runtime binaries and dependency caches to remain below 30 MB. No remote branch was altered. Claude Code can reproduce this result, merge the proposed modules into a dedicated branch, complete the host semantic bridge, and run the repository's full release checks before publishing a release.
