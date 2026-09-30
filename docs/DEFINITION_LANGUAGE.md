# The definition language for OEIS names: grammar, semantics, and the exact claim

`python/perfectpower/oeis_dsl.py` reads the `%N` line of an entry and, when it matches one of
the forms below, produces an **encoding**. `python/make_oeis_auto.py` emits a Lean definition from
the encoding and a theorem about it (`PerfectPower/Generated/OEISAuto.lean`).

## 1. What is proved, and what is not

| layer | status |
|---|---|
| the Lean definition equals an orbit coordinate, from a stated index (or enumerates a set) | **Lean theorem** |
| the Lean definition is the encoding | by construction: the emitter prints the encoding; `receipts/oeis_translation_review.md` shows both |
| the encoding reproduces every listed term at the entry's offset | exact Python check (a changed term makes the translation fail) |
| **the encoding is what the English name means** | **inspected translation, not a theorem** |

The Python parser is not a proof of natural-language understanding. The last row is guarded two
ways:
- the full term check, which is an effective error detector;
- a review file listing, for every accepted entry, the source text verbatim, the encoding, and the
  emitted Lean definition.

It can still be wrong where the English is ambiguous. Two cases are recorded:
- an initial value missing from the text is read from the terms (`init_from_terms`);
- "Numbers k" whose terms exclude the solution `k = 0` is read as positive `k` (`domain_note`).

## 2. Lexical normalization

Before matching, the name has all spaces removed and `−` (U+2212) replaced by `-`. Matching is
anchored as described per form. Nothing else is rewritten.

## 3. Grammar

The notation below is EBNF over the normalized string: `INT` is `-?[0-9]+`, `NAT` is `[0-9]+`, and
`S` is one of `a`, `L`, `F`, the same letter throughout one recurrence.

```
name        ::= gf | setsq | coord | linrec            (tried in this order; first success wins)

gf          ::= "Expansionof" ["g.f."] ratexpr ["inpowersofx"] ["."]
ratexpr     ::= term { ("+" | "-") term } | "-" term { ("+" | "-") term }
term        ::= power { ["*" | "/"] power }              (juxtaposition "(..)(..)" or "2x" is "*")
power       ::= atom { "^" NAT }
atom        ::= NAT | "x" | "(" ratexpr ")" | "-" atom

setsq       ::= ("Numbers" | "Positiveintegervalues" ["of"] | "Positiveintegers" | "Nonnegativeintegers")
                ("k" | "n") ["suchthat" | "forwhich" | "with" | "such"]
                [NAT] ["*"] ("k" | "n") "^2" ("+" | "-") NAT "isa" ["perfect"] "square" ["."]   (end of string)

coord       ::= ( "Squaresof" | "Squareof" | "Squared" ) base "numbers"
              | "a(n)=" [NAT "*"] basefn "(" [NAT] ["*"] "n" [("+"|"-") NAT] ")" ["^2"]   (not followed by + - * / or a digit)
              | basefn "(" [NAT] ["*"] "n" [("+"|"-") NAT] ")" ["^2"] "="              (at the start)
base        ::= "Pell" | "Fibonacci" | "Lucas"
basefn      ::= "Fibonacci" | "Lucas" | "F" | "L"

linrec      ::= … S "(n" ["+1"] ")=" rhs …                (the first match anywhere in the name)
rhs         ::= summand { ("+" | "-") summand }
summand     ::= [INT] ["*"] S "(n" [("+" | "-") NAT] ")" | NAT
init        ::= S "(" NAT ")=" [S "(" NAT ")="] INT      (every occurrence, anywhere in the name)
start       ::= "forn>=" NAT | "forn>" NAT | "n>" NAT     (the first occurrence, if any)
```

**Well-formedness conditions** (a match that violates one is rejected):
- `gf`: the reduced denominator has degree 2 or 3, and the normalized coefficients are integers.
- `setsq`: `D > 0` is not a square.
- `coord`: the base belongs to one family (below), and the shift is `≥ 0`.
- `linrec`: exactly order 2 (the two lags present after collecting terms), and every lag `≥ 1`.

## 4. Semantics

Each encoding denotes a sequence `a : {offset, offset+1, …} → ℤ`. The offset is the entry's
`%O`, never the parser's.

| encoding | denotation | Lean definition emitted |
|---|---|---|
| `LinRec(c₁, c₂, e, init, s)` | `a(n) = init(n)` for `n < s`; `a(n) = c₁ a(n-1) + c₂ a(n-2) + e` for `n ≥ s`. `s` is the stated start; else the least start consistent with the given initial values; else `offset + 2`. Missing initial values below `s` are read from the terms (recorded) | pattern-matching recursion, shifted so that index 0 is the offset |
| `GF(P, Q)` | the coefficient of `x^n` in `P/Q` as a formal power series (`Q(0) = 1`): `a(n) = p_n + Σ_j (-Q_j) a(n-j)` | `OEISLib.gf2`/`gf3`: exactly that recursion |
| `Coord(fam, X/Y, α, β, s, e)` | `s · X_{α m + β}^e` (or `Y`) of the family's orbit | the coordinate expression |
| `SetSquare(D, c, lo)` | the increasing enumeration, from the offset, of `{k ≥ lo : D k² + c is a square}` | the set `{k | lo ≤ k ∧ ∃ x, x^2 = D k^2 + c}` and its enumeration by merged seed orbits |

**Families** (orbits of `ε^k`, `x(k+2) = t x(k+1) + σ x(k)`):
- `fib`: `φ`, with `(X, Y) = (L, F)`;
- `pell2`: `1 + √2`, with `(A, B)`;
- `sqrt3`: `2 + √3`, with `(ox, oy)`.

**Theorems emitted:**
- `LinRec`, `GF`: `d · a(m + r) + s = p X_{αm+β} + q Y_{αm+β}` for all `m`, where `r` is the start of the
  relation.
- `Coord`: the entry's stated recurrence, when it has one.
- `SetSquare`: `Enumerates a offset Set`.

## 5. What falls outside

Floors (`⌊a(n-1)/(√2-1)⌋`), Pisot sequences, continued fractions, binomial transforms,
combinatorial objects, "Duplicate of", and every name matching none of the forms are
`NOT_TRANSLATED` (71 of 140 candidates). Some of these have hand-written Lean:
- continued fractions: `SqrtTwoBridges.A001333_eq`;
- Pythagorean triples: `SqrtTwoBatch.triples_listed`;
- duplicates: transport rules in `oeis_orbit.transport`.
