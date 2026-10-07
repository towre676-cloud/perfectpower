# Complete rational division by 5 and 7

This chapter delivers the first content extension proposed in Priority 5: complete rational division at the prime 5, together with 7, with degree, bit and work budgets and every exceptional branch handled. It extends the certified 2/3 division of the composed-division chapter without changing that interface. The existing `rational_division` keeps its contract of products of 2 and 3, and a separate `rational_division_general` composes the primes 2, 3, 5 and 7 for scalars up to 420.

## Construction

On the completed model u=x+A/3, Y^2=f(u)=u^3+pu+r, put F=4f and use the y-free division polynomials f_n, where psi_n=f_n for odd n and psi_n=2Y f_n for even n:

```text
f_{2m+1} = F^2 f_{m+2} f_m^3 - f_{m-1} f_{m+1}^3        (m even)
f_{2m+1} = f_{m+2} f_m^3 - F^2 f_{m-1} f_{m+1}^3        (m odd)
f_{2m}   = f_m (f_{m+2} f_{m-1}^2 - f_{m-2} f_{m+1}^2)
[n]u = phi_n / f_n^2,   phi_n = u f_n^2 - F f_{n+1} f_{n-1}   (n odd).
```

For a prime ell in {5, 7}, the rational ell-torsion kernel is closed by a complete rational-root certificate of psi_ell, which has degree (ell^2-1)/2, that is 12 or 24. For a finite target T, the division equation phi_ell-(x_T+A/3)psi_ell^2 has degree ell^2, that is 25 or 49. Fast discovery may supply one anchor. Otherwise a full rational-root certificate either finds an anchor or proves the fibre empty. The fibre is the anchor's torsion coset, and every point is checked against the generalized group law.

The exceptional branches are explicit:

- The target at infinity returns the kernel.
- Roots of psi_ell are never roots of the division equation, because psi_ell and phi_ell are coprime.
- An x-root with nonsquare cubic value has no rational lift and is discarded exactly.
- Two-torsion targets and generalized (a1, a3 nonzero) models go through the completed coordinate.

There are three budgets: a shared Sturm root-node budget, a coefficient-bit budget on psi_ell and on the division equation, and a branch budget on composed fibres. Exhaustion of any of them raises an error instead of returning a partial answer.

## Independent replay

The replay never searches. It rebuilds the division polynomials directly in the original x coordinate from the b-invariant recurrence, with psi_3=3x^4+b2x^3+3b4x^2+3b6x+b8, the corresponding psi_4/psi_2 and psi_2^2=B=4x^3+b2x^2+2b4x+b6, as in Silverman's AEC, Exercise 3.7. The producer uses the short model. The two psi_ell agree exactly on every tested curve, and the two division equations are the same polynomial, because the producer's phi includes the coordinate shift. The replay then checks the supplied Sturm certificates, the kernel lifts, the anchor coset and every node and bit count. Mutating an anchor, a method, a node count, a prime, a composed fibre, the factor order or the bit limit is rejected. At n=3 the recurrence reproduces the existing tripling polynomials exactly.

## Results

| Case | Result |
|---|---|
| 11a3, ker[5] | 5 points (Z/5) |
| 11a3, a 5-torsion point divided by 5 | empty fibre certified: no Z/25 |
| 26b1, ker[7] | 7 points (Z/7) |
| 37a1, 5P and 7P with P=(0,0) | fibre {P} |
| 37a1, P divided by 5 | empty: P is not 5-divisible |
| 37a1, 70P and 210P | composed stages 2,5,7 and 2,3,5,7 recover {P} |
| 5077a1, 5(g1+g2) | {(3,3)} = {g1+g2} |
| 5077a1, g1+5g2 divided by 5 | empty |
| 5077a1, 7 g3 | {g3} |
| 26b1, ker[35] | the 7 points of ker[7]; no 5-torsion |

Every packet is replayed independently. The node, bit and branch budgets each exhaust deliberately on a case built to exceed them.

## Scope

A complete rational division fibre is a statement about one target. It is not a Mordell–Weil basis, a rank, or a saturation index. Combined with the existing subgroup-preimage machinery, it extends that machinery's reach to the primes 5 and 7. No Lean execution of these Python certificates is claimed.

## Reproduction

```sh
export PYTHONPATH=python
python python/develop_elliptic_prime_division.py
python -m unittest discover -s python/tests -p test_elliptic_prime_division.py
```

The receipt is receipts/elliptic_composed_division/prime_division.json.
