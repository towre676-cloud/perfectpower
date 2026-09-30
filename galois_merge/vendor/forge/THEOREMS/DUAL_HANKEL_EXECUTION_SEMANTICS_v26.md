# V0.26 — Dual Hankel execution semantics

The Forge and EQ-LAB call-count ledgers were measuring two different directional residual machines of the same exact synchronized coefficient series.

For a written algebra word `s1...sd`, the **algebra-build** machine grows the formal word left-to-right by right multiplication and computes left residuals in written order. The **column-execution** machine evaluates the same operator on a column vector right-to-left; equivalently, reverse every written word before forming the residual-Hankel system.

Both are exact. Neither supersedes the other.

For the four frozen v0.23 constrained programs, reproduced at five independent primes, the directional profiles are:

| degree | algebra-build calls | column-execution calls |
|---:|---:|---:|
| 8 | 82 | 81 |
| 9 | 114 | 92 |

The degree-eight state dimensions are the same in both directions,
`1,2,4,8,16,15,7,3,1`, but the middle transition differs by one rank: written order has `(15,15)` while column execution has `(15,14)`. At degree nine the directional residual widths themselves differ: written order has `1,2,4,8,16,23,15,7,3,1`, while column execution has `1,2,4,8,16,19,9,4,2,1`.

The same 82/81 directional split persists for the exact v0.25 two-exchange sensor and Paley programs. Hence v0.25's global 81-call support theorem is specifically a theorem about **column-vector physical execution order**. EQ-LAB v0.18-v0.20's 82/114 figures remain correct for its declared written-order depth-synchronous residual model.

## Compiler contract

Every synchronized program now carries two certified costs:

1. `algebra_build`: cost of constructing/composing the operator in written algebra order;
2. `column_execution`: cost of applying the compiled operator to column features.

Cost comparisons must name the direction. A claim of an absolute minimum is invalid unless its execution convention is stated.

## Current boundary

V0.26 does not claim a physical machine below 81 calls. The next arithmetic question remains coefficient-induced cancellation in the column-execution machine. A sub-81 result must survive multiple independent primes and then be verified over characteristic zero.
