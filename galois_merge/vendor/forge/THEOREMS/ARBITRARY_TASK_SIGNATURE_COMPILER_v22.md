# Arbitrary Wilson task-signature compiler and route/native co-design -- Forge v0.22

## 1. From named tasks to an arbitrary Hecke subspace

V0.20 solved degree-eight section synthesis for a frozen list of Hecke task spaces. V0.22 promotes that calculation to a reusable compiler. Let `T <= H_Wilson` be any supplied linear task space. In the degree-eight synchronized fiber product, retain the v0.21 good-prime signatures

`σ_A : A_native -> F_p^127`, `σ_H : H_Wilson -> F_p^127`, `p=1,000,003`.

For any pure-radical native mask `S`, the exact finite compiler evaluates

`im σ_H(T) <= im σ_A(S)`

and the kernel inequality

`dim ker(σ_A|S) >= dim ker(σ_H|T)`.

The first condition is equivalent to existence of a synchronized section. The second is exactly the additional condition for a native-faithful section. Since there are only two plus and three minus arrows, the compiler exhausts all 32 masks. At degree nine the coupling disappears and the criterion reduces to native dimension at least `dim T`.

## 2. Complete twelve-cell mask phase diagram

All masks with the same rank pair `(r_+,r_-)` have the same signature dimensions. The exact table at the frozen good prime is

| `(r_+,r_-)` | native dim | signature rank | signature kernel | arrow proxy |
|---|---:|---:|---:|---:|
| `(0,0)` | 0 | 0 | 0 | 0 |
| `(0,1)` | 75 | 75 | 0 | 1500 |
| `(0,2)` | 150 | 127 | 23 | 3000 |
| `(0,3)` | 225 | 127 | 98 | 4500 |
| `(1,0)` | 5 | 5 | 0 | 30 |
| `(1,1)` | 80 | 80 | 0 | 1530 |
| `(1,2)` | 155 | 127 | 28 | 3030 |
| `(1,3)` | 230 | 127 | 103 | 4530 |
| `(2,0)` | 10 | 10 | 0 | 60 |
| `(2,1)` | 85 | 85 | 0 | 1560 |
| `(2,2)` | 160 | 127 | 33 | 3060 |
| `(2,3)` | 235 | 127 | 108 | 4560 |

Two consequences are immediate. Any task with dimension at most 150 and coupling-kernel dimension at most 23 is faithfully realizable in any fixed two-minus code. The mixed `(1,2)` code is universal for **every** subspace of the 152-dimensional Hecke algebra: it has full 127-dimensional signature image, native dimension 155, and kernel dimension 28, while `ker σ_H` has dimension only 25.

## 3. Geometry of the five one-channel signature spaces

The two plus-channel signature spaces have dimensions `5,5`, trivial intersection, and 10-dimensional sum. The three minus-channel signature spaces each have dimension 75. Every pair of minus spaces has sum equal to the full 127-dimensional coupling space and intersection dimension 23. The triple intersection is zero. Every plus/minus pair is transverse: its sum has dimension 80 and intersection zero.

Thus a one-dimensional injective-signature task admits a one-channel degree-eight section only when its projective signature line lies in the union of five exceptional projective subspaces:

- two copies of `P^4`, from the plus arrows;
- three copies of `P^74`, from the minus arrows;
- with the three minus spaces intersecting pairwise in `P^22` and with no nonzero triple intersection.

Over `F_p`, the exact fraction of projective lines in this exceptional union is

`[3 L_75 - 3 L_23 + 2 L_5] / L_127`, `L_d=(p^d-1)/(p-1)`.

At `p=1,000,003` this is approximately

`2.9995320372 x 10^-312`.

Outside that exceptional union, **two channels are necessary**, and any two minus arrows are sufficient. This is the generic one-dimensional degree-eight schedule in the frozen coupling model.

## 4. EQ-LAB v0.13: physical route sparsity does not imply native-channel sparsity

V0.22 imports WILSON-EQ-LAB v0.13. Its new task-specific sensor is the linear operator

`A_12 + A_48`,

used through the nonlinear energy `|| (A_12+A_48) H ||^2`. It is the unique consistent member of the 13-element sparse signed physical-route dictionary on the first 16 frozen hard pairs, ranks all 8 held-out pairs correctly, and costs route-work 120 per node. Canonical Paley costs 360 on a healthy six-route fabric and 2220 through the new degraded three-route direct backend.

Despite that large physical saving, the synchronized native schedule does **not** shrink at degree eight. `A_12+A_48`, Paley, and `A_49` all lie outside every one-channel signature space and therefore require `(0,2)`: two minus channels, 150 native coordinates, arrow proxy 3000. At degree nine, after Chinese-remainder separation, each one-dimensional operator can be paired with a single plus channel, only five native coordinates and proxy 30.

The point is structural: physical route support and native section support are independent compiler axes. A task may be physically sparse and still be coupling-generic.

## 5. Complete finite-dictionary census

The result is not peculiar to the winning sensor. V0.22 checks three complete frozen dictionaries:

- all seven primitive Q192 route lines;
- all 13 nonzero signed supports on physical routes `(49,12,48)`, modulo global sign;
- all 32 signed six-`C7` operator lines used by the v0.12 path-sensor search, modulo global sign.

There are **zero one-channel degree-eight cases in all three dictionaries**. Every one of these 52 frozen task lines lies in the generic two-channel class. Each drops to one plus channel at degree nine.

This explains the repeated `(0,2)` schedules of v0.20-v0.21 without elevating them to a universal theorem for all possible Hecke lines: one-channel exceptions exist algebraically, but the exact projective census shows they form an extraordinarily thin set and none of the present Wilson task dictionaries lands there.

## 6. Formation v37 simplifies the live formation compiler

Formation Polarization v37 is imported as the current formation handoff. For finite nonabelian simple species under the **full outer action**, every residual Schur coinvariant is either `0` or `C2`. Odd-primary residual alphabets vanish, higher 2-adic residual depth disappears, and the cancellation-tether branch of v34-v36 is vacuous in this finite-simple/full-outer universe.

The only mixed critical atom that survives is the unique full-support binary projective line

`<(1,1,...,1)> <= F_2^r`.

V33-v36 remain valid for restricted outer actions, abstract Schur modules, and broader perfect/quasisimple palettes. Forge therefore keeps their primitive relation machinery as a general backend, but the live finite-simple formation front can now use the much smaller binary compiler.

## 7. Evidence boundary and next step

The task compiler is exact for the frozen good-prime coupling realization. The rank and noncontainment statements used for the named integral tasks are certified at that prime; a canonical integral 127-dimensional coupling lattice is still not claimed. The failed attempt to reconstruct the full degree-eight relation lattice by naive rational RREF confirms that this arithmetic lift remains ill-conditioned in the current word basis.

The next arithmetic target is therefore narrower: lift **task-selected** synchronized sections, beginning with the v0.13 two-route sensor and the Paley line, using sparse modular supports and CRT/rational reconstruction rather than reconstructing the entire 127-dimensional coupling lattice at once. The general compiler created here tells us exactly which section masks are worth lifting.

Machine data: `DATA/RELATION/ARBITRARY_TASK_COMPILER_V22/`.
Reproducer: `scripts/analyze_arbitrary_task_compiler_v22.py`.
