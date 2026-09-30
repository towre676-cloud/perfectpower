import Mathlib.Data.Int.Basic

/-!
# Kernel-friendly integer square root (not trusted)

`Nat.sqrt` is slow under `decide +kernel`.  `nsqrt` is Newton's iteration with fuel.  It is
**never assumed correct**: every checker that uses it verifies `q^2 ≤ t < (q + 1)^2` (or
`j * j = k`) for the value it gets.
-/

namespace PerfectPower

/-- Newton iteration for `⌊√x⌋`, with fuel. -/
def nsqrtAux : ℕ → ℕ → ℕ → ℕ
  | 0, _, r => r
  | fuel + 1, x, r =>
    let r' := (r + x / r) / 2
    if r' < r then nsqrtAux fuel x r' else r

/-- `⌊√x⌋` for `x < 2^256` (checked by the caller, never assumed). -/
def nsqrt (x : ℕ) : ℕ := if x = 0 then 0 else nsqrtAux 300 x x

/-- `⌊√t⌋` for `t > 0`, and `0` otherwise. -/
def isqrtZ (t : ℤ) : ℤ := if t ≤ 0 then 0 else (nsqrt t.toNat : ℤ)

end PerfectPower
