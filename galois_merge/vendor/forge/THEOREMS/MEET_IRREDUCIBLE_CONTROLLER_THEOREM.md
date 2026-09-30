# Meet-irreducible controller compression theorem

Let c be a finite closure operator on a feature set T and L=Fix(c) its finite closure lattice.  The v4 closed-set separator construction assigns one attribute coordinate to each proper closed set C and uses

W_t={C in L: t notin C}

to realize

t in c(S) iff W_t subset union_{s in S} W_s.

The all-proper-closed-set choice is universal but redundant.

## Theorem
Let MI(L) be the set of proper meet-irreducible closed sets.  Define

W_t^MI={M in MI(L): t notin M}.

Then for every S subset T and t in T,

t in c(S) iff W_t^MI subset union_{s in S} W_s^MI.

Moreover MI(L) is the unique inclusion-minimal closed-set separator family that works uniformly for all S,t.  Hence, within the v4 prime-support realization scheme, one attribute prime per meet-irreducible closed set is necessary and sufficient.

## Proof
If t notin c(S), put D=c(S).  Since every element of a finite lattice is the meet of the meet-irreducibles above it, some meet-irreducible M satisfies D subset M and t notin M.  Then M belongs to W_t^MI but not to W_s^MI for any s in S, so containment fails.  Conversely, if t in c(S), any closed M omitting t cannot contain all of S, or closure would force t in M.  Therefore every M in W_t^MI omits at least one s in S and belongs to the union of W_s^MI.

For minimality, let M be meet-irreducible with unique cover M+.  Choose t in M+\M.  Any closed C strictly above M contains M+ and hence t.  To separate the closed seed D=M from t, a separator family must therefore contain M itself.  This holds for every meet-irreducible M.

## Master-policy consequence
The nine-feature Wilson Forge demonstration has 81 closed states and therefore 80 proper closed sets.  It has exactly 10 meet-irreducibles.  The original universal compiler used 80 attribute primes; the compressed compiler uses exactly 10, an 8x reduction, with zero mismatches over all 512 input subsets and every target feature.

The chosen attribute primes are

17,19,23,29,31,37,41,43,47,53,

all disjoint from pi(M22)={2,3,5,7,11} and from the tag prime q=13.  The resulting congruence modulus is drastically smaller than the v0.1 all-closed-set realization; the first valid final prime found by the same construction is

p=1795281613703685528005854309.

See `DATA/master_program_compiled_minimal.json` for the exact supports, action orders, ten minimality witnesses, and complete regression result.
