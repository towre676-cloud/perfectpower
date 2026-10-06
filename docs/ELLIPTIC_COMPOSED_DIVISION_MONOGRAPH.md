# Complete rational tripling and compositional division

The rational elliptic interface now solves [3]H=P completely and composes complete doubling and tripling fibres for every positive multiplier n at most 36 whose prime factors are only 2 and 3. This includes 6, 12, 18 and 36. The answer is an exact rational point list, including infinity when appropriate, together with every intermediate fibre and complete rational-root evidence. A resource limit causes a failed request rather than a partial list labelled complete. Nineteen deterministic scientific packets demonstrate nonempty and empty fibres, generalized coordinates, rational six-torsion and rational nine-torsion. Six cold-reload service responses retain the public interface.

## What changed since the previous handoff

The consolidated starting tree is 2a971d018fa8b87f3dc1d57678cd73d60a01cfae on claude/laughing-lamport-qqzdo9. Relative to the briefing at 22e4edf, incoming commits add general weighted Cauchy–Binet and native population certificates, scalar tree-decay calculations, and exact Gaussian spectral matching. Those commits are preserved. Flavor work remains in its separate mathematical lane; this release builds on the elliptic foundation already integrated by the Lean work.

The earlier witness push supplied complete rational halving and replayable lower bounds for independent rational witnesses. The subsequent Lean division push proved kernel-coset fibre equivalences, generalized square completion, short coordinate translation and integer-to-rational root transport. The native arithmetic push added complete rational roots and two-torsion theorems. These are useful mathematical foundations, but they do not certify the Python parser, root-search implementation or packet interpreter. The current extension supplies executable tripling and composition, with independently expanded coordinate replay. It adds no new Lean theorem and does not claim that the entire historical Lean census was rebuilt.

## Tripling in exact coordinates

Start with the nonsingular generalized Weierstrass equation y²+a1xy+a3y=x³+a2x²+a4x+a6. Write Y=y+(a1x+a3)/2 and Y²=x³+Ax²+Bx+C. Set u=x+A/3, a=B−A²/3 and b=C−AB/3+2A³/27. The short equation is Y²=u³+au+b. All transformations take place over the rational numbers; their denominators are nonzero.

Define psi3(u)=3u⁴+6au²+12bu−a² and F6(u)=u⁶+5au⁴+20bu³−5a²u²−4abu−8b²−a³. Then phi3(u)=u psi3(u)²−8(u³+au+b)F6(u), and u([3]H)=phi3(u(H))/psi3(u(H))² away from the multiplication-kernel denominator. For a finite target with short coordinate u0, the degree-nine polynomial phi3−u0 psi3² contains every possible preimage x-coordinate after translation. It is monic. The quartic psi3 contains every finite rational three-torsion x-coordinate.

For reference, the expanded numerator is u⁹−12au⁷−96bu⁶+30a²u⁵−24abu⁴+(36a³+48b²)u³+48a²bu²+(9a⁴+96ab²)u+8a³b+64b³. The producer uses the division-polynomial recurrence; replay constructs this independent expansion from the curve invariants a=−c4/48 and b=−c6/864. Tests compare both constructions and exact group multiplication on integral points of short and generalized models. SymPy is not a runtime dependency.

An x-coordinate polynomial alone does not solve the signed point equation. Each rational root must have a rational completed square root Y; both signs are lifted back to the original model, and the full equality [3]H=P is checked. This also filters roots that do not correspond to rational points. For the infinity target, lift the quartic roots and retain exactly the points killed by multiplication by three, together with infinity. Nonsingularity is required by the existing curve constructor.

## Completeness from kernels and anchors

If [3]H=P has one rational solution H, every other rational solution is uniquely H+T for rational T in E[3]. Therefore a complete rational kernel list and one exact anchor determine the entire fibre. The bounded p-adic shortcut seeks only that anchor. Every discovered candidate is evaluated exactly, lifted to the curve and checked against the full multiplication equation. Failure of the shortcut is not an emptiness conclusion.

When no anchor is found, the producer computes a complete rational-root certificate for the degree-nine equation. The existing monic integral transform sends a rational root r to the integer Dr, where D clears the monic coefficients. A complete signed-remainder Sturm tree determines the integer root list. Rational square lifting and the full group equation then either produce an anchor or establish that the rational fibre is empty. An anchor allows translation of the already complete kernel, even when it came from the exhaustive fallback.

The packet distinguishes three_torsion, torsion_coset and empty_division_fibre. A missing anchor may justify emptiness only when a complete finite-target root certificate is retained. Replay checks the exact polynomial transform, root transcript, canonical model, target, anchor and output ordering. It invokes no root-discovery routine. It shares exact group arithmetic and the existing Sturm checker with other repository components; independent Python replay is the appropriate claim.

## Composition retains every intermediate image restriction

For n=2^a3^b, divide the target first through a doubling stages and then through b tripling stages. If the current frontier is the complete set of rational solutions of [m]Q=P, replacing each Q by its complete rational [p] fibre gives exactly the solutions of [mp]H=P. Both implications follow directly by applying multiplication. Thus induction proves completeness of the final list. No finite-search assumption, rank hypothesis or rational torsion classification is needed for this composition argument.

Each stage retains its prime, ordered input targets, one certificate for every target, and the complete output union. Different input targets have disjoint prime fibres. Replay requires exactly one packet for each ordered target and rejects missing branches, changed targets, reordered factor stages, incorrect scalar metadata and forged final points. It checks the final multiplication equation as well. The identity multiplier has no stages and returns the singleton target. After a complete empty frontier, subsequent stages are recorded as empty.

Supported scalars are 1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 27, 32 and 36. The maximum scalar is an implementation scope, not a theorem that larger fibres are inaccessible. Other prime factors require their own complete prime-division implementation. Every request has one shared root-node budget, from 1 through 100000, and a branch bound from 1 through 64. Repeated kernel certificates are charged each time; there is no hidden cache or per-branch renewal. Allocation checks bound the final nested packet. Large intermediate coefficients or Sturm data may exceed the arithmetic allocation limits even when a mathematical fibre is small.

## Worked complete results

On y²=x³+1, the rational three-torsion fibre is infinity and (0,±1). The rational six-torsion fibre consists of infinity, (−1,0), (0,±1) and (2,±3). The complete rational kernels for multipliers 12, 18 and 36 are the same six points. These statements come from complete root packets and composition rather than an assumed torsion classification.

On y²−3xy−12y=x³−12x², the point (0,0) has order nine: its triple is (4,8) and its ninth multiple is infinity. The complete ninth-division fibre of infinity contains exactly its nine multiples. The packets for 18, 27 and 36 also contain exactly nine points. This tests torsion lifting across several nontrivial branches in generalized coordinates.

On y²=x³−2, the fibres above n(3,5), for n=3, 6, 12, 18 and 36, each recover precisely (3,5). The point (3,5) itself has no rational third, and its rational eighteenth fibre is empty. The generalized model with coefficients (1,−1/4,1,−1/2,−9/4) similarly recovers (3,3) from its thirty-sixth multiple. On y²=x³+9, the thirds of 3(3,6) form a three-point coset: (3,6) plus the kernel {infinity,(0,3),(0,−3)}. This is a finite nontrivial coset rather than only a kernel example.

## Public use and reproduction

An elliptic_curve object now exposes rational_thirds(p,node_limit) and rational_division(p,scalar,node_limit,branch_limit). Points use exact rational coordinate strings; infinity is JSON null. The public standalone operations verify_elliptic_thirds and verify_elliptic_division replay their respective packets. Existing rational_halves, model transport, two-isogeny and independence operations remain available.

Run make elliptic-composed-division to execute the focused tests and regenerate the corpus. The generator is python/develop_elliptic_division.py. Scientific packets and SHA-256 bindings are in receipts/elliptic_composed_division/summary.json. Cold service requests and responses are retained alongside them. Run make test for the repository Python regression. Exact mathematical scopes and the final regression counts are recorded in ELLIPTIC_COMPOSED_DIVISION_VALIDATION.md.

## What this makes possible, and what remains

A rational point obtained from a curve map or parameter-family calculation can now pass through a complete composite multiplication inverse. Its exact rational preimages, intermediate failures and torsion ambiguity remain visible. This provides a useful ingredient for testing individual witness divisibility and for future saturation algorithms. Testing individual points does not saturate a lattice: saturation also requires checking rational divisions of combinations of generators modulo the relevant prime. A complete Mordell–Weil basis, rank upper bound, global height bound and integral-point census are separate tasks.

The next formal bridge is a point-law refinement theorem together with tripling coordinate identities and a typed interpreter for the rational-root and staged-fibre packets. The existing group-coset theorem is reusable there. The next arithmetic expansion is complete prime division beyond three or a bounded lattice saturation algorithm that retains all residue combinations. Global Mordell bounds and explicit Matveev premises remain larger independent research fronts. Singular-endpoint period certification and source-to-native compiler semantics likewise retain their own mathematical obligations.
