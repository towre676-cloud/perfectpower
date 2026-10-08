# Open Content Assembly

This is a catalogue of the "open" and "not proved" sections found at the end of the first-party PDFs. Every item has been checked against the repository history through `eb1fb27` on main and against this branch. Fifty-seven PDFs were scanned with `pdftotext`. Items already closed are listed only so they are not picked up again.

## Feasibility tiers

| Tier | Meaning in this container |
|---|---|
| **P** | Doable now with exact Python (Fraction/SymPy) or floating-point NumPy/SciPy. |
| **A** | Doable now with certified interval arithmetic (python-flint/Arb). |
| **L** | Needs Lean/Mathlib. These are blocked here because the network policy denies the elan and Mathlib cache hosts. |
| **X** | Needs external data or tools that are blocked or absent (ATLAS, Magma, ECPP, Why3/SPARK). |
| **M** | Needs a physics model choice before any computation means anything. |
| **O** | Owned by another session's active lane. Coordinate before touching it. |

Sizes: S is under a day, M is a few sessions, L is research-scale.

## Already closed (do not re-open)

| Item | Source | Closed by |
|---|---|---|
| CRT products of residue atlases | RESIDUE_ATLAS_CRT | main |
| Smooth residue patch | BOUNDED_RESIDUE_PATCH | main |
| Integer-valued domains (base) | INTEGER_VALUED_POLYNOMIAL | main |
| Fixed divisors, local power-free | FIXED_DIVISOR, POWER_FREE_LOCAL | main |
| Rational division by 5 and 7, composed 2·3·5·7 | ELLIPTIC_COMPOSED_DIVISION | this branch (`elliptic_prime_division*`) |
| Weil commutants through level 64; on-paper all-level formula c(N)=τ(N) odd, (2a−1)τ(m) dyadic | WEIL_* | main |
| Repeated saturation (bounded form) | ELLIPTIC_SUBGROUPS | main |
| Frye / Lander–Parkin attribution | perfectpower | main |
| Mordell frontier ledger (457 = 323 empty + 134 with points) | NONFLAVOR_FRONTIER | main |
| Wall thermal nucleation, continuum stability, scattering, shape radiation, network A and C_ann, lattice GW ε_gw | Flavor_Cosmology_and_Tree_Decay | this branch |
| Genus-2 certified periods (real branch points) | CURVE_STRUCTURE | this branch |
| Shared-factor (noncoprime) atlas intersections, factored source covers, kernel-proved intersections (was R3) | RESIDUE_ATLAS_CRT | main `016aa30`, `f40fd39` |
| Wall Goldstone/gauge channel operators: exact quadratic radial decoupling, Goldstone–vector derivative mixing retained, nonzero cubic Ward overlaps (was F2) | Flavor_Fixed_Gauge_and_Goldstone_Ward | main `4bcfe69` |
| Diagonal Valentiner F-flat vacuum census: 108 roots, stable nonunitary competitor (part of V3) | Valentiner_SUSY_Vacua | main `6c57c0b` |

## Open items by lane

### 1. Arithmetic: elliptic and Diophantine

| # | Open item | Source | Tier | Size | Deliverable |
|---|---|---|---|---|---|
| A1 | Subgroup preimages for p=5,7, with reduced Smith/Hermite presentations of the generated subgroup | ELLIPTIC_SUBGROUPS | P | M | `elliptic_subgroup_preimage` module, replay verifier and receipt, reusing `elliptic_prime_division` |
| A2 | p-saturation at 5 and 7 (bounded) | ELLIPTIC_SUBGROUPS | P | M | Extend the saturation packet to ℓ∈{5,7}, using the prime-division certificates as witnesses |
| A3 | Maximal orders, nonmonic norm transport, Skolem-style extraction | ELLIPTIC_BRIDGES / NATIVE_BRIDGES | P | M | Exact order-basis certificates checked by a discriminant index |
| A4 | Brainpool-384 prime certificate (p−1 leaves a 349-bit composite cofactor, so Pocklington stalls) | Executable_Applications | P/X | L | An ECPP certificate (Atkin–Morain with a small-discriminant CM search) plus an exact verifier |
| A5 | 2-descent rank upper bound for frontier curves | NONFLAVOR_FRONTIER | P | L | A complete 2-Selmer computation for small-height curves, which removes part of the 323 empty cases |
| A6 | Mordell 457 frontier closure | NONFLAVOR_FRONTIER | X/L | L | Needs rank, Sha and saturation (Magma/Sage), then a Lean import |
| A7 | 2n⁴−1=m² (Ljunggren), Bilu–Tichy instances, global k-free density | CURVE_RESEARCH / FIXED_DIVISOR | L | L | Literature theorems; formalization only |
| A8 | k=94 source closure; Matveev premises; Lean reductions of Thms 3.1, 4.1 and the geometric half of 4.4; kernel-checked nonrigid genus-one family | perfectpower / ELLIPTIC_DIVISION_LEAN | L | M–L | Lean |
| A9 | Efficient native Sturm in the kernel | NATIVE_HALVES_REFINEMENT | L | M | Lean |

### 2. Residue atlases and integer-valued charts

| # | Open item | Source | Tier | Size | Deliverable |
|---|---|---|---|---|---|
| R1 | Transport power equations through integer-valued charts; Hensel/CRT partial domains | INTEGER_VALUED_POLYNOMIAL | P | M | A chart-transport module with exact replay |
| R2 | Bounded-residue chart switching with a branching lift | BOUNDED_RESIDUE_PATCH | P | M | A switching certificate with a lift tree |
| R4 | Unordered weighted determinant identity | RESIDUE_DETERMINANT | P | S | A symbolic proof (SymPy) plus a randomized exact test |

### 3. Weil lane

| # | Open item | Source | Tier | Size | Deliverable |
|---|---|---|---|---|---|
| W1 | Lean: old-level isometry, dyadic trace, orbit bounds, field normalization; formalize c(N) | WEIL_CRT / WEIL_DIMENSION / WEIL_SPECTRAL | L | M | Lean |
| W2 | Exact replay of c(N) beyond level 64 (e.g. to 1024) as a Python cross-check of the paper proof | WEIL_DIMENSION | P | S | Receipt |

### 4. Curves

| # | Open item | Source | Tier | Size | Deliverable |
|---|---|---|---|---|---|
| C1 | Genus-2 periods with complex branch points; automatic marking for general sextics | CURVE_STRUCTURE / ALGEBRAIC_CURVE_EXTENSIONS | A | M | Extend `genus2_certified_periods` with certified complex paths and a canonical symplectic basis |
| C2 | Positive-resonance Legendre chart; singular endpoints | CURVE_FAMILIES | A | M | Arb connection matrices with certified endpoint asymptotics |
| C3 | The 36 unresolved metric boxes of 144 | CONNECTED_CLOSURES | A | M | Refined Arb subdivision that decides each box or certifies it as undecidable at depth d |
| C4 | Rigorous interval continuation of family connections | CURVE_FAMILIES | A | M | Arb Taylor-model continuation |
| C5 | Singular Richelot targets; stable reduction with several collisions | ALGEBRAIC_CURVE_EXTENSIONS | P | M | Exact degenerate-Richelot formulas with cluster-picture tests |
| C6 | Higher-genus correspondences, quotient towers, Puiseux/Frobenius/differential Galois, rational Betti constraints | CURVE_RESEARCH / LITERATURE_CURVE_EXECUTION | P/L | L | Research |

### 5. Infrastructure

| # | Open item | Source | Tier | Size | Deliverable |
|---|---|---|---|---|---|
| I1 | Dresden browser/GPU validation | DRESDEN_NUMERICAL | P | S–M | Headless-Chromium run of the WebGPU/WebGL kernels against the reference outputs, if the kernels run on a software adapter |
| I2 | JSON parser and compiler refinement proofs | DECISION_POLICIES | L | M | Lean |
| I3 | Why3/SPARK | Executable_Applications | X | none | Demote to "not pursued" (the review agrees) |
| I4 | Industrial replication; HTTP concurrency | Executable_Applications | P | M | A load test of the reference server with a replay-equality check |

### 6. Walls (this branch's lane)

| # | Open item | Source | Tier | Size | Deliverable |
|---|---|---|---|---|---|
| F1 | Interval validation of the five profile signs | Flavor_Analytic_Radial_Profile / Polynomial_Wall_Fredholm_Hierarchy | A | M | Arb validated ODE enclosure of the kink profiles, giving certified signs |
| F3 | Zero-temperature Coleman–Weinberg and two-loop thermal corrections to nucleation | Flavor_Cosmology_and_Tree_Decay | P/M | M | A CW-corrected bounce and ΔS_3/T bracket on `wall_nucleation` |
| F4 | Annihilation-phase GW (bias-driven collapse) | Flavor_Cosmology_and_Tree_Decay | P | M | Biased-potential lattice runs and an ε_gw during collapse |
| F5 | Larger GW boxes (N≥384) to resolve the peak and IR slope | same | P | L (compute) | Larger runs, which need more cores or memory than this container has |
| F6 | Kibble–Zurek real-time formation | same | P/M | M | Quench simulation giving the initial A, compared with the PRS scaling |
| F7 | Higher-order / infinite-domain radiation-node coefficients; coupled g≠0 hierarchy | Gaussian_Coupled_Radiation_Nodes / Retuned_Wall_Radiation_Nodes | O | M | Another session's lane |

### 7. Flavor (other sessions' lane)

| # | Open item | Source | Tier | Size |
|---|---|---|---|---|
| V1 | Exact tensor proof of the 52-operator loop table | Flavor_Exact_Tensors_Running_and_Vacuum_Selection | P (SymPy) | M |
| V2 | Missing scalar-potential calculation (B5 audit) that can be tested exactly | B5_Protected_Flavor_Monograph | P | M |
| V3 | Golden-frame selection, global vacuum | Valentiner_Joint_Potential / Nonet | M/O | L |
| V4 | Finite EFT matching, two-loop phase | Flavor_Finite_Spectral_Matching | O | L |
| V5 | Explicit 3.M22 matrix representation | M22_Triplet_Transport | X (ATLAS blocked) | M |

## Opened by the 2026-10-07 releases

| # | New open item | Opened by | Tier | Size | Deliverable |
|---|---|---|---|---|---|
| N1 | On-shell wall-mode decay widths into Goldstone pairs and (at reduced g) WW/ZZ, with distorted-wave external states and energy conservation | `4bcfe69` (overlaps are vertices, not widths) | P | M | Combine the cubic Ward vertices with the Jost continuum states of `wall_jost_scattering`: a Fermi golden-rule width and a lifetime |
| N2 | Gauge thermal bath and vector functional determinant on the wall | `4bcfe69` | P/M | M | A thermal vector-mass correction to the bounce and wall tension, feeding F3 |
| N3 | Nonlinear lifetime of the 154.225 GeV localized candidate | `4bcfe69` | P | M | Real-time 1+1D evolution of the excited wall, extracting a decay rate to compare with N1 |
| N4 | A frame-selecting interaction that beats the stable nonunitary F-flat competitor (a common soft mass picks the wrong branch) | `6c57c0b` | P/O | M | A scan of symmetry-allowed soft and D-term invariants, giving exact branch energies |
| N5 | Perturbative analysis of the massless diagonal branch; global classification of perturbed vacua beyond the diagonal | `6c57c0b` | P/O | M | Exact second-order shifts, then a nondiagonal numerical census |
| N6 | Interpreter refinement for normalized factor traversal and offsets (atlas compiler to kernel) | `f40fd39` | L | M | Lean |

## What we can do: execution plan

Batches are ordered by value per effort among the items that run here.

1. **Elliptic subgroup closure (A1, A2).** This builds directly on the 5/7 division certificates already on this branch. It gives complete preimage and saturation at every prime ≤7.
2. **Certified curves (C1, C3, C2).** This extends the Arb period engine to complex branch points and closes the 36 metric boxes.
3. **Wall certification and physics (F1, N1, N3, F3, N2, F4).** This covers the Arb profile signs; wall-mode decay widths and nonlinear lifetime, built on the new gauge-channel vertices and this branch's Jost states; CW/two-loop and vector-bath nucleation corrections; and annihilation-phase GW.
4. **Residue and chart machinery (R1, R2, R4).** These are exact certificates with replay verifiers, in the style of the existing residue atlases.
5. **Cross-checks and validation (W2, I1, V1).** These are a large-level c(N) replay, headless-Chromium Dresden validation, and the SymPy proof of the 52-operator table (coordinate with the flavor lane).
6. **Large items.** These are A4 (ECPP for Brainpool-384) and A5 (2-Selmer bounds on the frontier), and they are scheduled after batches 1–5.

The Lean-blocked items (A7–A9, W1, I2, N6) need the environment's network access to allow `release.lean-lang.org`, `github.com` release downloads for elan, `lakecache.blob.core.windows.net` and `mathlib4.lean-cache.cloud`. ATLAS (`brauer.maths.qmul.ac.uk`) unblocks V5.

## Second update (main through `89bde64`)

Closed by main:

| Item | Closed by |
|---|---|
| R1 integer-valued chart transport and Hensel/CRT partial domains | `d7b9968`, `89bde64` |
| R2 bounded-residue chart switching across horizontal, vertical and singular branches | `d7b9968`, `89bde64` |
| R4 unordered weighted determinant and Gram identity, with positivity | `d7b9968`, `89bde64` |
| N1 on-shell distorted-wave pair widths (Goldstone 3.83e-8 GeV; WW/ZZ TE at g=0.4); (M−2m)^3 threshold law | `0546f58` |
| N2, partly: UV-finite thermal relative determinant of the TE vector polarizations | `0546f58` |
| N4 frame selection: determinant A-term window 6.558<t<9.524, and a Gram-quartic completion with a global unitary frame class | `065c0d5` |
| N5, partly: 130,681 certified vacua (130,572 off-diagonal); the massless orbit is flat to degree 12 | `065c0d5` |

Newly opened:

| # | Item | Opened by | Tier |
|---|---|---|---|
| N7 | Interval certificate of the positive Higgs barrier, which the threshold law and the thermal monotonicity now both rely on (merges with F1) | `0546f58` | A |
| N8 | Remaining physical vector polarizations (TM/longitudinal), plus off-shell, fermion and loop channels: the full electroweak lifetime | `0546f58` | P/M |
| N9 | Temperature-dependent wall, vertices and screening masses; Landau and scattering damping | `0546f58` | P/M |
| N10 | Feed the vector thermal free energy per area into the tension and the nucleation bounce (joins F3) | `0546f58` | P |
| N11 | Typed factor-traversal and chart-family address interpreter: one leaf per CRT tuple, safe pruning, rank/select inverses (extends N6) | `d7b9968`, `89bde64` | L |
| N12 | General Lean identification of K_S with canonical minor products | `d7b9968` | L |
| N13 | Global solution set of the Pell-type example (x^2+7)/2=y^2 via the fundamental unit, not only the box | `d7b9968` | P |
| N14 | The massless orbit at degree ≥12: all-order flatness, a continuous component, or an isolated minimum | `065c0d5` | P/O |
| N15 | Completeness of the unperturbed vacuum set beyond the 130,681 lower bound | `065c0d5` | P/O |
| N16 | Radiative stability of the radial calibration; a consistent gauge or dynamical-tensor UV completion | `065c0d5` | M/O |
| N17 | Quark-source frame, golden CKM relation and physical CP selection from the selected frame | `065c0d5` | M/O |

## Third update (main through `bb015b4`)

Closed by main:

| Item | Closed by |
|---|---|
| A1 subgroup preimages at 5 and 7, with Hermite/Smith presentations and actual free indices | `2c62fb8`, `4e61ecc` |
| A2 bounded saturation at 5 and 7, including joint 2·3·5·7 closure | `2c62fb8`, `4e61ecc` |
| F1/N7 whole-line wall existence, five profile signs and the positive Higgs barrier (Arb computer-assisted certificate) | `d84b568` |
| N16, partly: one-loop supertrace of the selected frame and the radial calibration counterterm | `f57b2b8` |
| N14, partly: multivariate effective W vanishes through degree 12 (first possible F-energy at degree 24); exact all-orders determinant criterion | `bb015b4` |
| Selected-frame census: exactly 1,080 global vacua (via Harui's theorem) | `f57b2b8` |

Newly opened:

| # | Item | Opened by | Tier |
|---|---|---|---|
| N18 | Complete torsion-aware relation lattices and actual indices modulo torsion (the current index operation needs a trivial p-kernel and free witnesses) | `4e61ecc` | P |
| N19 | Rational division and saturation at primes beyond 7 (11, 13, …) | `2c62fb8` | P |
| N20 | Automatic termination of saturation, via height-pairing index bounds | `2c62fb8` | P |
| N21 | Lean interpretation of the prime-fibre packets against the group-coset theorem | `4e61ecc` | L |
| N22 | Upgrade the remaining wall results (continuum stability gap, pair widths, thermal shifts) from numerical controls to Arb enclosures on the certified profile | `d84b568`, `0546f58` | A |
| N23 | Computational reproof of the 1,080-element automorphism group of the sextic, independent of Harui's classification | `f57b2b8` | P |
| N24 | All-orders resolution of the massless orbit from the determinant criterion: a moduli space or an obstruction at degree ≥24 | `bb015b4` | P/O |
| N25 | Global vacuum ordering beyond the local one-loop continuation; two-loop accuracy; gauge, quark and Higgs determinants in the supertrace | `f57b2b8` | M/O |

## Fourth update (main through `0e34a9a`)

Closed by main:

| Item | Closed by |
|---|---|
| A4 Brainpool-384 primality: 15-stage ECPP, 384 → 45 bits, independent check | `2fdc37d` |
| A5 two-descent upper bounds for the whole Mordell frontier; 76 rank gaps closed by quartic point lifts | `2fdc37d`, `54f81af` |
| A3, partly: cubic power-order unit bases, nonmonic source lattices, signed exponent extraction | `d0fdfb3` |
| W2 Weil dimensions checked through level 128 | `d0fdfb3` |
| R13 Pell-7: every solution of x²+7=2y² on two unit orbits | `ce43361` |
| N18 torsion-aware subgroup indices and complete relation lattices | `ce43361` |
| N19, partly: bounded division, preimages and saturation at 11 and 13 | `0e34a9a` |
| N23 direct 1,080-element stabilizer recompute (360 projectivities, no classification premise) | `4ec6504` |
| N14/N15 an exact all-orders F-flat curve in each null direction; the unperturbed census is infinite | `8d2707b`, `4ec6504` |
| F6 Kibble–Zurek formation: 2D Model-A quench ensembles | `0087ca7` |
| N9, partly: thermal wall continuation, bulk phase classification, localized Higgs ordering window (8.63 MeV) | `e3140a2` |
| V1 52-operator loop table (audited as already closed) | `8d2707b` |

Newly opened:

| # | Item | Opened by | Tier |
|---|---|---|---|
| N26 | Explicit points on the 92 witness-deficient frontier curves, certified independent against the retained upper bounds | `0e34a9a` | P |
| N27 | k=−9257: a second independent point or a sharper upper bound; reconcile 12 historical census ranks with the backend bounds | `0e34a9a` | P |
| N28 | Saturate the witness subgroups into complete bases, then rerun the affected integral-point lists | `2fdc37d` | P |
| N29 | Attach torsion-aware index packets to every saturation stage; automatic coordinate extraction | `ce43361` | P |
| N30 | General norm representatives and an effective exponent-orbit bound (current runtime searches up to |e|≤64), plus arbitrary power orders | `d0fdfb3` | P |
| N31 | Division beyond 13 | `0e34a9a` | P |
| N32 | Mixed-direction Valentiner germ: one 3D smooth component, or three separate curves? | `4ec6504` | P/O |
| N33 | KZ follow-ups: 3D networks with expansion, three-field evolution through the Higgs transition, bath matching, continuum critical calibration | `0087ca7` | P/M |
| N34 | Thermal wall follow-ups: gauge-resummed thermal masses, damping kernels, real-time thermal wall evolution, loop matching | `e3140a2` | P/M |
| N35 | Apply the field theorems in ZMod p for Brainpool-384 now that p is proved prime; Lean good-reduction kernel proof for 11/13 | `2fdc37d`, `0e34a9a` | L |

## Fifth update (this branch, massive push)

Closed on this branch:

| Item | Commit | Monograph |
|---|---|---|
| Genus-2 periods with complex branch points, automatic symplectic marking, Riemann relations, Sp(4,Z) consistency | `eb121c6` | GENUS2_COMPLEX_PERIODS_MONOGRAPH |
| 36 unresolved boxes: all 36 certified to *fail* (interior zeros; they are affine-face boxes, not metric boxes) | `71a8da9` | CURVE_CERTIFIED_CONTINUATION_MONOGRAPH |
| Certified Legendre connection, Frobenius charts incl. the positive-resonance chart at infinity, integral Γ(2) monodromy | `71a8da9` | same |
| Singular Richelot targets (E1×E2 or a Weil restriction); DDMM cluster stable reduction and conductors, any genus, p odd | `32856e1` | SINGULAR_RICHELOT_AND_CLUSTERS_MONOGRAPH |
| Annihilation-phase GW: enhancement ≈1.47 over the unbiased network, ε_gw≈0.7, offset-law K≈1.95 | `3ab3cf1` | WALL_ANNIHILATION_GW_MONOGRAPH |
| Nonlinear lifetime of the 154.225 GeV mode: real-time Gaussian pair emission reproduces Γ_GG to ~1–2% | `e01fa59` | WALL_MODE_LIFETIME_MONOGRAPH |
| CW and two-loop nucleation corrections (CW dominates; S3/T falls up to ~27%); Arb-certified spectral gap (>125.35 GeV, within 0.13% of the threshold) | `8c04fd9` | WALL_NUCLEATION_CORRECTIONS_AND_CERTIFIED_STABILITY |

Newly opened:

| # | Item | Tier |
|---|---|---|
| N36 | Fix the CONNECTED_CLOSURES monograph's "metric boxes" wording (they are affine-face boxes) | P (doc) |
| N37 | Asymptotic test of the p=1/2 annihilation law: larger boxes or earlier network formation | P (compute) |
| N38 | The electroweak (gauged) lifetime in real time: WW/ZZ channels | P/M |
| N39 | Certified gap for the declared λ=0.1 wall (main's checker coercivity constant is too large) and for the angular/gauge sectors | A |
| N40 | Two-loop thermal diagrams computed with counterterms, replacing the estimates; interval bounces | P/A |
| N41 | Cluster stable reduction at p=2 or with wild ramification; minimal regular models and Tamagawa numbers | P (research) |
| N42 | Higher-rank resonant Frobenius charts and irregular singular points for the certified connection | A |
