# The irreducible positive-`k` workload

`python3 python/positive_k_next.py` derives `receipts/positive_k_next.json` from
`receipts/positive_k.json`. It only reads the existing census and uses integer
arithmetic for the new identities. It can run while the generated `K*.lean`
modules compile. The recorded representations are bounded-search targets,
not complete solution lists.

The remaining locally admissible irreducible workload has 104 equations in
61 curves. Eighty-seven equations have a known representation. The leading
coefficient magnitudes are 1 (68 equations), 2 (25), 3 (10), and 4 (1).
Thirty-eight curves have just one irreducible equation. These counts make
the monic case the useful first shared source solver.

For a form `F=(a,B,C,d)` with `a=±1`, put `h=B/(3a)`,

```
p = C/a - 3h²,
q = d/a - (C/a)h + 2h³,
z³ + pz + q = 0.
```

The change of coordinates is integral and unimodular. With the norm in
`ℤ[z]`, the exact polynomial identity is

```
F(u,v) = a N((u+h v)-v z).
```

Thus `F(u,v)=1` implies norm `a`, so the encoded element is a unit in
this order. This skips the norm-representative step for 68 equations.
The discriminant check `-4p³-27q²=-108k` is performed for every monic
row by the receipt generator. An equality of discriminants alone does not
identify orders; order sharing still requires explicit maps.

**Status: done** (`Plus2.source`, `Generated/ClassLists/K2.lean`, `K2.plus2`; see
`MORDELL_BRANCH.md` §7.4). The generic version (`RankOne.lean`) also closes `k = 4, 33, 49, 81`. The plan as written:

The first pilot is `k=2`. Its two classes are
`(-1,0,-3,-2)` and `(0,-3,0,-2)`. The latter has no representation of 1
modulo 9. For the former, let `z³+3z+2=0`; then

```
-u³-3uv²-2v³ = -N(u-vz).
```

The bounded search sees `(-1,0)` and the curve points `(-1,±1)`. The
required source theorem must prove **every** solution is `(-1,0)`, before
the already available class-list and readout machinery can give an
unconditional curve theorem. This is the first useful end-to-end target
after the 39 generated modules finish.

The signature is `(1,1)`, so the unit rank is one. A Lean `RankOneUnitGen`
certificate can use rational root and embedding enclosures to prove that
the units of an explicit order are `±ε^n`. Choose `n` by rounding the real
logarithm; the normalized unit has bounded real embedding, and its complex
modulus follows from norm `±1`. Enumerate the resulting finite coordinate
slab and check its units explicitly. For the pilot, `ε=1+z-z²` has norm 1;
the finite slab must establish whether it generates all units. That last
claim is a proof obligation, not a consequence of finding a small unit.

After unit generation, the pilot reduces to the zeros of the `z²`
coefficient of `ε^n`. A finite exponent search does not establish its
complete zero set. A source certificate needs an effective bound and
reduction, or a complete `p`-adic zero argument on every exponent residue
class. A local calculation at 2 says that `ε` has order 2 modulo 2 and
that a zero exponent is even; it does not rule out other even exponents.
Keep that boundary visible in the source theorem. A successful pilot
would then provide the rank-one architecture for the other 67 monic
equations; the 36 nonmonic equations add norm representatives or covers.
