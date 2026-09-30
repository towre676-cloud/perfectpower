# Closure of the two internal `L3(4)` marked `H_2` rows — v0.17

The v0.16 handoff left precisely two even-primary maps unresolved:

`M(A6)_(2) ~= C2 -> M(L3(4))_(2) ~= C4^2`,

`M(L3(2))_(2) ~= C2 -> M(L3(4))_(2) ~= C4^2`.

The double cover could not see the answer because every nonzero row lands in `2 C4^2`.  v0.17 instead pulls the three ATLAS classes of each subgroup through faithful permutation realizations of **both** `4_1.L3(4)` and `4_2.L3(4)`.  If `P` is the full inverse image of a subgroup `H`, its derived subgroup distinguishes the restriction: `P' ~= H` gives selector value `0 mod 4`, while `P' ~= 2.H` gives selector value `2 mod 4`.

For both `A6` and `L3(2)`, both 4-covers produce the selector pattern

`(0,2,2)`

on the three ATLAS conjugacy classes.  This alone does not mean the first class has zero `C4^2` row, because v24 already proved that the two named 4-cover selectors reduce to the same line modulo two.

The missing information is supplied by the outer action.  Direct computation in the frozen degree-21 permutation representation verifies that outer type `2_2` fixes class 1 and swaps classes 2 and 3, while the order-three outer automorphism cycles `1 -> 2 -> 3 -> 1`.  This happens **synchronously for both species**.  The v24 multiplier theorem identifies the induced action on `2C4^2 ~= F2^2` with the faithful natural `S3` action, whose order-three element cycles the three nonzero vectors.  Since classes 2 and 3 are selector-visible and therefore nonzero, class 1 cannot be zero: each three-class orbit is exactly the set of the three nonzero vectors.

Choose a common basis of `2C4^2` by

`x1 = image(A6 class 1) = (2,0)`,

`x2 = image(A6 class 2) = (0,2)`,

`x3 = x1+x2 = (2,2)`.

The synchronized outer action forces the `L3(2)` orbit to carry the same labels.  Hence the complete normalized row table is

| ATLAS class | row in `C4^2` |
|---|---|
| `A6` class 1 / maximal 3 | `(2,0)` |
| `A6` class 2 / maximal 4 | `(0,2)` |
| `A6` class 3 / maximal 5 | `(2,2)` |
| `L3(2)` class 1 / maximal 6 | `(2,0)` |
| `L3(2)` class 2 / maximal 7 | `(0,2)` |
| `L3(2)` class 3 / maximal 8 | `(2,2)` |

Thus the two marked first-class rows requested by the v0.16 handoff are

`A6: (2,0)`, `L3(2): (2,0)`

in the common normalized basis above.  The equality is meaningful because the class-orbit synchronization fixes the common marking; an independent basis choice for each row would make it vacuous.

This closes the first `L3(4)` simple-section branch: no even 2-primary internal `H_2` row remains open there.

Machine certificate: `DATA/FORMATION/L34_INTERNAL_H2_V17/l34_internal_h2_rows_v17.json`, reproduced from frozen ATLAS permutations by `scripts/compute_l34_internal_h2_rows_v17.py`.
