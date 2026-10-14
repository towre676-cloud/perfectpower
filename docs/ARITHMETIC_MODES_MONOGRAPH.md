# Arithmetic height channels and exact Pauli interference

Research expansion, October 14, 2026. This volume extends the retained height/Pauli monograph rather than replacing it. All old source and receipts remain in the complete snapshot. The present contribution is an exact finite channel calculus, a symbolic compiler for arithmetic height walls, a height filtration of spin interference, and a Lean account of the underlying language and group algebra. The earlier 620-second oscillator experiment is a separate retained experiment; the new benchmark runs lasted 17.24 and 13.56 seconds. We do not describe those short runs as ten minutes of fresh computation.

## A larger mathematical object

Let each labeled mode j have an integer prime p_j, a direction epsilon_j in {−1,+1}, a finite quota k_j, and a Pauli axis a_j in {0,1,2,3}. From a positive reduced rational x_0, a partial word with usage vector c has value x(c)=x_0 product_j p_j^(epsilon_j c_j). Its multiplicative rational height is H(x)=max(numerator(x),denominator(x)); equivalently its logarithmic height is log H. The implementation uses the multiplicative height, exact fractions, and integer comparisons. Labels are distinct even when their arithmetic effects agree. The finite population consists of words that exhaust every quota, keep every prefix below an optional height ceiling, satisfy optional integrality, and follow an optional finite controller with accepting terminal states.

The sufficient state is (c,q), where q is the controller state. Every edge increases one usage coordinate, so the graph is acyclic even if the arithmetic value repeats. The controller can prevent consecutive uses of the same mode or impose an arbitrary finite transition grammar. This admits repeated primes, inverse moves, rational intermediates, more than two axes, and language restrictions. It is substantially broader than the two-prime shortest-path model. It remains a finite, quota-conditioned population.

For each state s, define N(s)=1 at accepted terminal states, 0 at rejected terminals, and sum_j N(next(s,j)) otherwise, omitting undefined moves. The root gives the exact population. Lexicographic rank and unrank descend the graph using these suffix counts. A prefix query returns the exact number of completions, and a uniformly chosen integer in [0,N(root)) gives a uniform word. This is population sampling, not enumeration of exponentially many words. The Python engine supports up to eight labels, horizon 512 and explicit graph budgets; the browser intentionally uses smaller limits, up to six labels, horizon 48 and 50,000 states. Large counts are decimal strings at JSON boundaries.

## The noncommutative lift

Attach U_j=sigma_(a_j), with sigma_0=I. For the chronological word w=(j_1,...,j_L), our convention is U(w)=U_(j_L)...U_(j_1). These products lie in the sixteen-element Pauli group {i^r sigma_a}. Store an exact population for each of these sixteen elements, then subtract opposing phases to obtain four Gaussian-integer coefficients A_a. The unnormalized ordered channel is A=sum_w U(w)=sum_a A_a sigma_a. Its normalized coherence statistic is C=sum_a |A_a|²/N² for N>0, and zero by convention for an empty population. This equals one half of the squared Frobenius norm of A/N. It is a finite equal-weight word statistic; no continuous-time transition probability is being asserted.

Counting paths and adding their Pauli products are different observations of the same language. Positive path populations retain every word. The spin channel can cancel them exactly. A transfer matrix can carry any finite observation algebra; the present implementation specializes this principle to the Pauli group, turn-count polynomials, and height maxima. Turn coefficients count the number of words having exactly t changes of mode. The polynomial at 1 recovers N, and its derivative divided by N gives the exact mean number of turns. Augmenting the dynamic state by previous mode and turn count gives this result without enumerating words.

A suitable layered clock can represent geodesic fixed-quota words as a leading coefficient of a Hermitian finite evolution. A general controller-conditioned or looping language needs its own clock and acceptance construction. The program does not silently identify every word population with a matrix element of a physical Hamiltonian. Bounded arithmetic labels, spectral analogies, and exact Pauli algebra do not imply a connection with zeta zeros or a proof of the Riemann hypothesis.

## The signed height-wall recurrence

For p<q and depth d, shortest integer paths from p^d to q^d under ceiling q^d correspond after reversal to grid words with u p-increments and v q-increments satisfying p^u≤q^v. The ordinary recurrence is C(u,v)=C(u−1,v)+C(u,v−1) at admissible cells. The signed recurrence is S(u,v)=(-1)^v S(u−1,v)+S(u,v−1), with the same boundary gate and root value 1. Each p-step picks up the parity of preceding q-steps; this is the anticommutation sign. Lean proves that this recurrence equals the signed sum over the finite word enumeration for all integer parameters and grid sizes.

At depth two, for every 1<p<q, Lean proves the following exact wall law:

| Arithmetic condition | C(2,2) | S(2,2) |
| --- | --- | --- |
| p<q<p² | 2 | 0 |
| q≥p² | 3 | 1 |

This is a parameterized theorem, not a numerical fit. Primality is unnecessary for this finite wall identity. Its operator interpretation still uses the chosen mode labels and Pauli axes. The first row supplies exact destructive interference despite two valid routes. At p=2,q=3, depth three has seven routes and signed coefficient −1, so the next depth restores a nonzero channel. These small identities are also checked as kernel literals.

## Height filtration and restoration

A forward dynamic sweep can track the maximum height encountered so far together with a Pauli group element. Accumulating terminal bins gives the complete step function of population and amplitude at every relevant ceiling. It computes all ceilings in one sweep; a separate minmax dynamic program finds the least peak height needed by any accepted word. An unrestricted graph is required to obtain the full filtration, while a capped graph yields its restricted filtration. Explicit augmented-state budgets protect against blowup.

For the p=2,q=3 depth-three route population, the retained exact filtration is:

| Ceiling H | Routes N | Absolute net Pauli coefficient | C |
| --- | ---: | ---: | --- |
| 27 | 7 | 1 | 1/49 |
| 36 | 9 | 1 | 1/81 |
| 54 | 14 | 0 | 0 |
| 72 | 16 | 0 | 0 |
| 108 | 19 | 1 | 1/361 |
| 216 | 20 | 0 | 0 |

Thus the height ceiling is not merely a monotone transport resource. It controls which phases enter the sum. The positive population is monotone, but its signed channel vanishes, reappears, and vanishes again. At depth two the corresponding thresholds are H=9,12,18,36, with populations 2,3,5,6 and net scalar amplitudes 0,1,1,2. These tables are exactly recomputed in Python and browser BigInt arithmetic. The public Interference Microscope animates sampled paths, displays phase populations and the threshold curve, and exports the exact packet. This is a reproducible finite finding; novelty relative to all published literature has not been established.

## Compile the arithmetic walls before choosing the bases

At fixed d, every gate u log p≤v log q depends only on lambda=log q/log p. For lambda≥1, the only changes occur at rational walls u/v with 1≤v≤u≤d. Sort and deduplicate these fractions and compute C and S once for every chamber, using u*denominator≤v*numerator. The wall belongs to the chamber on its right because the arithmetic constraint is inclusive. No approximate logarithms are used. A query (p,q) locates its chamber by exact comparisons q^denominator≥p^numerator. The compiled tables apply to ordered integer bases, including multiplicatively dependent boundary cases; they are not restricted to primes.

This is arithmetic reuse across magnitudes. It removes repeated recurrence work from a batch of prime-pair queries, but requires setup. The retained benchmark used d=64, 1,260 chambers, and 2,000 ordered prime-pair queries from primes below 500. All count and signed outputs agree with independent direct recurrence calls. Compilation took 0.921657 seconds, lookups 0.017095 seconds, and the direct query bank 1.009139 seconds. Warm lookup was 59.03 times faster; including setup, the compiled workload took 0.938752 seconds, only about 1.075 times faster overall. The measured break-even point is 1,859 queries. There is no arbitrary-workload speedup claim.

The full sweep across d=1,...,64 covered 27,833 rational chambers. Every odd d through 63 had a strictly negative signed coefficient in every chamber. We retain this as the conjecture S_lambda(d,d)<0 for odd d and lambda≥1. Even depths admit zero and positive values, so a naive depth-independent sign statement is false. Checking every chamber covers every admissibility pattern at the tested horizons; it does not prove the statement for unbounded d. A promising next proof target is a sign-reversing involution that leaves an odd-depth residual family. Until such a construction is supplied, the conjecture stays separate from the Lean theorem ledger.

## Scale and representation

The following measurements use the retained benchmark modes, heights and controller specifications in the executable script. Each row includes 300 rank/unrank round trips. The total is 3,000 verified round trips. Graph construction uses exact integer fractions; times are wall-clock measurements on this environment, not baseline comparisons.

| Modes | Quota each | Horizon | Reachable states | Exact population | Build seconds | 300 round trips, seconds |
| --- | ---: | ---: | ---: | --- | ---: | ---: |
| 4 | 4 | 16 | 499 | 22683584 | 0.0033 | 0.0025 |
| 4 | 8 | 32 | 5,389 | 34887682703496543 | 0.0444 | 0.0067 |
| 4 | 12 | 48 | 23,706 | 81818119823237912503695147 | 0.2358 | 0.0170 |
| 4 | 16 | 64 | 69,708 | 228572523000990365447886038458960471 | 0.8846 | 0.0309 |
| 4 | 24 | 96 | 327,868 | 2298271696502377238389627195577824586619042008577455719 | 5.4865 | 0.0659 |
| 6 | 3 | 18 | 3,459 | 50410998900 | 0.0340 | 0.0044 |
| 6 | 4 | 24 | 13,403 | 1177052908611030 | 0.1693 | 0.0091 |
| 6 | 5 | 30 | 40,424 | 31940096099201562524 | 0.6115 | 0.0152 |
| 6 | 6 | 36 | 102,656 | 954814713786659798930046 | 2.1812 | 0.0286 |
| 6 | 7 | 42 | 229,920 | 30532377474725377248428311308 | 5.9485 | 0.0537 |

Spin histograms were computed only for graphs below 90,000 states in this benchmark; larger rows retain exact counts and rank tests without a claimed spin computation. For four modes of quota sixteen, the positive and negative scalar phase populations are 114286261500495856656643345648435294 and 114286261500494508791242692810525177. Their exact difference is 1347865400652837910117. Tiny relative coherence is not numerical underflow: every subtraction is integer arithmetic. The separate signed bank contains 256 pair-depth cases; 128 are nonzero odd-depth cases and four are exact cancellations. The receipts call the former “revivals”; that is a count of odd nonzero cases, not a claim of 128 distinct height restoration events.

## Formal scope and evidence

The new Lean module proves signed enumeration, finite partial-state language semantics, counting equality, accepted-word length, enumeration soundness and completeness, absence of duplicate words under a distinct alphabet, edge-preserving language monotonicity, state-map transport of languages, counts and weighted observations, and the exact Pauli group representation. Associativity, identities, matrix multiplication compatibility and anticommutation are checked by kernel reduction over the finite group. The square-wall theorem is parameterized in p and q. The audit also generates signed recurrence literals and four finite arithmetic graph fixtures, including rational and controller examples. Each fixture checks outgoing arithmetic gates, reduced rational height, quota increments and controller states, then proves the finite census value.

The generic Lean state semantics do not yet prove refinement of the entire Python graph compiler. Literal fixtures bridge only their explicit graphs. The new audit checks 25 theorem declarations and 32 literal theorems, adding 57 to the retained 56-check ledger. The current kernel receipt gives the authoritative theorem counts, axiom lists and source hashes. Standard Lean logical foundations may occur; no sorry, new axiom declarations or native_decide are used. The previous height/Pauli kernel ledger remains separately retained. Python tests independently enumerate small languages and compare count, rank, prefix counts, Pauli products, turns, filtration, rational reduction, controller transitions, budgets and exact chamber boundaries. Browser tests compare 61 Python/BigInt cases and all 4,096 group associativity cases. Browser layout was not exercised by automation in this environment.

## Reproduce and extend

Run PYTHONPATH=python python -m perfectpower.arithmetic_modes examples/arithmetic_modes/four.json --turns --rank 0 --minimum-height --filtration. Run python python/benchmark_arithmetic_modes.py and python python/benchmark_slope_atlas.py for fresh measurements. Run python scripts/check_arithmetic_modes_kernel.py with Lean 4.20.0 on PATH, node scripts/check_arithmetic_modes.cjs, and the arithmetic Python test suite. Make targets provide the same entry points. Receipts retain exact decimal populations and phases; the source code fixes mode specifications and the workload. The complete ZIP pins an explicit Git engine snapshot and verifies every original source byte. Public feed refresh is separate from upgrading installed Android or Windows executables.

The next mathematical push should seek a proof or counterexample for the odd-depth sign conjecture, a generic arithmetic adapter refinement in Lean, and an analytic treatment of the signed channel near rational walls. A complementary engineering push can add interval-certified spectral calculations for a specifically defined layered Hamiltonian and compare them to the channel coefficients. Each task has a checkable target. None requires interpreting forced Pauli symmetry as an unexplained zeta phenomenon.
