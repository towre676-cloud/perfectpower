# The PerfectPower certificate format, `pp-cert/1`

A `pp-cert/1` certificate is a small JSON object. Its claim is that, for $n\ge1$, $F(n)=m^d$ is solvable in integers exactly for $n$ in a listed finite set. A proof-carrying checker, compiled once in Lean, turns any certificate it accepts into a kernel-checked theorem. The checker and its soundness theorems are in `PerfectPower/Reflect.lean`. The producer, validator, importer and parser are in `python/perfectpower/certfmt.py`. The committed certificates are in `certs/`, and the generated Lean is in `PerfectPower/Generated/{Runge,Sandwich}.lean`.

## Schema

```json
{"format": "pp-cert/1",
 "kind": "sandwich" | "runge",
 "name": "<Lean identifier>",
 "statement": {"F": [c0, c1, ...], "d": d, "hits": [n1, n2, ...]},
 "statement_sha256": "<sha256 of the canonical JSON of statement>",
 "data": {...},
 "producer": {"name": "...", "version": "..."}}
```

- **Statement.** `F` lists the coefficients of $F\in\mathbb Z[x]$, lowest degree first, and `d` is the exponent, with $d\ge2$. `hits` is the claimed complete, sorted list of $n\ge1$ with $F(n)$ a $d$-th power. The canonical JSON is `json.dumps(statement, sort_keys=True, separators=(',', ':'))`, and `statement_sha256` binds the statement.
- **Segments.** A list covering $[1,c)$ contiguously and in order:
  - `{"k":"hit","n","m"}` asserts $F(n)=m^d$;
  - `{"k":"gap","n","a"}` asserts $0\le a$ and $a^d<|F(n)|<(a+1)^d$;
  - `{"k":"neg","n"}` asserts that $d$ is even and $F(n)<0$;
  - `{"k":"ival","lo","hi","t"}` (sandwich only) asserts, for every $n\in[lo,hi]$, that $0<P(n)+t$ and $(P(n)+t)^d<D^dF(n)<(P(n)+t+1)^d$. The checker verifies this through the Taylor shift to $lo$ with the test $\mathrm{POS}(0)>\mathrm{NEG}(hi-lo)$.
- **`sandwich` data:** `D`, `P` (the truncated root $P/D$), `segments`, `tail_start` $=c$, and `tail_t`. The three sandwich polynomials with offset `tail_t` must have no negative coefficients after the Taylor shift to $c$.
- **`runge` data:** `D`, `P`, `x0` $=c$, `T`, `segments` (points only), and `signs`, one $\pm1$ for each $t\in[-T,T]$. After the shift to $x_0$ the checker requires:
  - $P>0$;
  - $(T+1)P^{d-1}\mp R'>0$, where $R'=D^dF-P^d$;
  - $P^d\mp R'>0$ when $d$ is odd;
  - $\mathrm{sign}_t\cdot(D^dF-(P+t)^d)>0$ for every $t$.

## Semantics and soundness

`Reflect.check` and `Reflect.rungeCheck` recompute every Taylor shift, product and power from the data by kernel evaluation (`decide +kernel`; no `Lean.ofReduceBool`). The segment walk requires each segment to start at the cursor, so gaps and overlaps are rejected; it must also end exactly at the tail start. The theorems, proved once, are

```lean
theorem Reflect.check_sound {C : Cert} (h : check C = true) :
    ∀ n : ℕ, 1 ≤ n → (IsHit C.d (ev C.F n) ↔ n ∈ hitsOf C.segs)
theorem Reflect.rungeCheck_sound {C : RungeCert} (h : rungeCheck C = true) :
    ∀ n : ℕ, 1 ≤ n → (IsHit C.d (ev C.F n) ↔ n ∈ hitsOf C.segs)
```

The importer (`certfmt.to_lean`) emits three things: the data literal, `cert_<name>_ok : check … = true := by decide +kernel`, and the hit-set theorem. That theorem's statement is rebuilt from `statement.F` and bound to the data by `rfl`.

**What binds what.** A producer that changes `F` without changing the statement fails the hash check in `validate`. A producer that changes both can only obtain a theorem about the new `F`, and only if that theorem is true. `audit/CertReject.lean` shows this in two directions:
- the $(12,4)$ cover, applied unchanged to $F+1$, is *accepted*: $n(n+1)\cdots(n+11)+1$ is never a fourth power;
- applied to $F+783616$, which has $F(1)+783616=148^4$, it is *rejected*.

The same file checks by kernel evaluation that a gap, an overlap, an off-by-one tail, a wrong exponent, a fake hit, a wrong gap witness, a flipped Runge sign and a moved threshold are all rejected (`check … = false`).

**Python side.** `certfmt.validate` is a fast structural pre-check, which the tests exercise on planted malformations (`python/tests/test_certfmt.py`). It never makes a certificate valid; only the Lean kernel does. The round trip JSON → Lean → JSON (`to_lean`, `from_lean`) is tested for all 19 certificates, and so is the fact that the generated Lean files are exactly the import of the committed JSON. `make verify` regenerates both and requires zero diff.

## Benchmarks

The timings come from `make bench`, `receipts/cert_benchmarks.json`, on the build machine. They vary by machine. "Lean check" is the time of `lake env lean` on a file holding just that certificate, minus the time of the import alone (1.96 s). "Explicit range" is the range that segments decide one by one or by intervals. Beyond it the certificate covers all $n$ by the analytic tail. By comparison, an exact sieve scan of the same range takes milliseconds but proves nothing beyond it.

| Certificate | kind | deg F | d | segments | explicit range | JSON bytes | Lean bytes | producer s | Lean check s |
|---|---|---|---|---|---|---|---|---|---|
| `consecutive10_fifth_power_hits` | runge | 10 | 5 | 1 | [1, 2) | 421 | 2034 | 0.042 | 2.18 |
| `consecutive12_cube_hits` | runge | 12 | 3 | 58 | [1, 59) | 2178 | 3168 | 0.546 | 1.9 |
| `consecutive12_sixth_power_hits` | runge | 12 | 6 | 8 | [1, 9) | 636 | 2368 | 0.065 | 2.3 |
| `consecutive12_square_hits` | runge | 12 | 2 | 87 | [1, 88) | 3394 | 4030 | 0.292 | 1.35 |
| `consecutive4_fourth_power_hits` | runge | 4 | 4 | 0 | [1, 1) | 331 | 1514 | 0.002 | 0.24 |
| `consecutive4_square_hits` | runge | 4 | 2 | 0 | [1, 1) | 322 | 1450 | 0.001 | 0.57 |
| `consecutive6_cube_hits` | runge | 6 | 3 | 1 | [1, 2) | 361 | 1586 | 0.012 | 0.65 |
| `consecutive6_sixth_power_hits` | runge | 6 | 6 | 1 | [1, 2) | 374 | 1660 | 0.006 | 0.54 |
| `consecutive6_square_hits` | runge | 6 | 2 | 21 | [1, 22) | 919 | 1905 | 0.035 | 0.47 |
| `consecutive8_eighth_power_hits` | runge | 8 | 8 | 2 | [1, 3) | 425 | 1855 | 0.025 | 1.36 |
| `consecutive8_fourth_power_hits` | runge | 8 | 4 | 0 | [1, 1) | 370 | 1830 | 0.009 | 0.79 |
| `consecutive8_square_hits` | runge | 8 | 2 | 3 | [1, 4) | 440 | 1823 | 0.012 | 0.45 |
| `ljunggren_quartic_hits` | runge | 4 | 2 | 3 | [1, 4) | 396 | 1431 | 0.005 | 0.23 |
| `n4_plus_1_square_hits` | runge | 4 | 2 | 0 | [1, 1) | 322 | 1306 | 0.001 | 0.16 |
| `n4_plus_7_square_hits` | runge | 4 | 2 | 1 | [1, 2) | 345 | 1314 | 0.002 | 0.14 |
| `n6_plus_n_plus_1_cube_hits` | runge | 6 | 3 | 1 | [1, 2) | 349 | 1384 | 0.005 | 0.25 |
| `sextic_1_2_3_4_5_6_1_cube_hits` | runge | 6 | 3 | 20 | [1, 21) | 861 | 1890 | 0.072 | 0.81 |
| `consecutive10_square_hits` | sandwich | 10 | 2 | 283 | [1, 20277) | 10699 | 8912 | 0.384 | 34.64 |
| `consecutive12_fourth_power_hits` | sandwich | 12 | 4 | 49 | [1, 478) | 2046 | 3232 | 0.105 | 7.64 |

Totals: 25189 JSON bytes, 44692 Lean bytes, and 56.67 s of Lean checking for all 19 complete hit sets.

## Relation to other work (to be verified against primary sources)

The following comparisons were suggested by an external reviewer. **The primary texts could not be read in the build environment, where the network policy blocks arXiv**, so the notes below are not yet a verified comparison, and no novelty claim rests on them.
- **Beukers–Tengely**, *An implementation of Runge's method for Diophantine equations* (2005, arXiv:math/0512418). By the reviewer's account, it implements Runge's method without Puiseux series or algebraic coefficients. Their implementation, not a brute-force scan, is the right comparison for producer speed and for the range excluded before the analytic tail. This repository's producer is Theorem R of the research notes. What `pp-cert/1` adds, if the comparison bears it out, is the *verified certificate*: a compact data object that a small, fixed, proved-once checker turns into a kernel theorem.
- **LeanCert** and similar verified numerical-certificate tools separate search, check and interpretation in the same way. The architecture here is the standard proof-by-reflection pattern.
- **Baanen–Best–Coppola–Dahmen** (CPP 2023) formalised complete solutions of selected Mordell equations. That work concerns genus one. `pp-cert/1` covers only the rigid (Runge) branch, so the two are complementary; for genus one see `PerfectPower/Genus1.lean`, where completeness is still a named hypothesis.

**The claim to be earned.** Whenever the Runge or sandwich producer succeeds on a polynomial perfect-power instance, it yields a compact certificate of the complete hit set, checked independently by the Lean kernel. The benchmarks above measure that claim. The comparison with previous Runge software is still to be done against the primary sources.
