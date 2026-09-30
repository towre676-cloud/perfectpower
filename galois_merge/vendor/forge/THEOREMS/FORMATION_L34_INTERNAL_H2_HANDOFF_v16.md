# L3(4) internal H2 handoff — v0.16

Formation v24 is imported byte-for-byte and closes the **ambient** selector marking: the named `M22` `4_1` line and `U4(3)` `4_2` line are matched modulo 2, span `C4 x C2`, and jointly expose 8/16 frequencies.

It does not determine the two remaining internal maps

\[
M(A_6)_{(2)}\cong C_2\longrightarrow C_4^2,
\qquad
M(L_3(2))_{(2)}\cong C_2\longrightarrow C_4^2.
\]

The exponent sieve reduces each marked row to exactly four possibilities:

\[
(0,0),\quad(2,0),\quad(0,2),\quad(2,2)\pmod4.
\]

Current CTblLib double-cover data does not distinguish these four possibilities.  All three `A6` maximal-subgroup lifts in `2.L3(4)` have structure `2 x A6`, and all three `L3(2)` lifts have structure `2 x L3(2)`.  This split `C2` shadow is compatible with every row above: each nonzero candidate lands in `2C4^2` and disappears in the double-cover shadow.

Therefore v0.16 does **not** promote either internal map.  The correct next computation is specifically one of:

- a marked restriction inside `4_1.L3(4)` or `4_2.L3(4)` that records the selected central order-four coordinate; or
- an induced-`H_2` calculation for the corresponding subgroup inclusion.

The package freezes the two four-state marked variables and forbids the compiler from treating the split double-cover preimage as evidence for the zero row.
