# Five minutes: from a polynomial to a compiled Lean certificate

This walk-through proves a complete hit set in Lean without trusting the Python tooling. The example is Ljunggren's equation $1+n+n^2+n^3+n^4=m^2$. Coefficients are always given low-to-high.

## 1. Classify

```sh
$ PYTHONPATH=python python3 -m perfectpower classify --coeff 1,1,1,1,1 --d 2
{ "kind": "finite", "t_profile": {"2": 4}, "growth": "bounded", "effective": true, ... }
```

The output says three things:

- The four roots are simple and $d=2$, so every root has $t=2$. By Siegel's theorem, through Theorem G ($S=4\cdot\tfrac12=2>1$), the hit set is finite; this step is conditional and ineffective (see [TRUST_BOUNDARY.md](TRUST_BOUNDARY.md)).
- The degree is divisible by $d$ and the leading coefficient is a square. So $F$ is *rigid* (the Runge case), and the finite set is computable.
- `effective: true` records exactly that.

## 2. Enumerate

```sh
$ PYTHONPATH=python python3 -m perfectpower enumerate --coeff 1,1,1,1,1 --d 2
... "hits": [[3, 11]] ...
```

The enumerator runs Theorem R of the research notes: it scans below a threshold, isolates roots of $D^dF-(P+t)^d$, and handles the tail. It reports $n=3$ with $F(3)=121=11^2$. This output is a claim, not yet a proof.

## 3. Emit a Lean certificate

```sh
$ PYTHONPATH=python python3 -m perfectpower lean --coeff 1,1,1,1,1 --d 2 --name ljunggren > Scratch.lean
```

The file contains one theorem:

```lean
theorem ljunggren (n : ℕ) (hn : 1 ≤ n) :
    IsHit 2 (let z : ℤ := n; (1) + z + z ^ 2 + z ^ 3 + z ^ 4) ↔ n ∈ ({3} : Finset ℕ)
```

Its proof is built only from the compiled lemmas `runge_pointwise`, `not_isHit_between` and `not_isHit_neg`, together with `ring`, `positivity` and `norm_num`.

For polynomials whose threshold is large, use `--method sandwich`. This covers $[1,\infty)$ by intervals on which $(P+t)^d<D^dF<(P+t+1)^d$ is proved once per interval, through `no_hit_of_sandwich`.

## 4. Check it

```sh
$ lake env lean Scratch.lean          # about 6 s once the library is built
```

If this compiles, the statement is a theorem of Lean and Mathlib.

To confirm the axioms, append `#print axioms ljunggren` and check the output reads `[propext, Classical.choice, Quot.sound]`. The Python steps above only proposed the data, and any mistake there would make the file fail to compile rather than prove something false.

## 5. Where this stops

- **Rigid case.** This pipeline covers rigid $F$ with positive leading coefficient, and more generally every $F$ that is rigid for some divisor $d'\ge2$ of $d$.
- **Structural types.** Families of power, radical or Pell type have infinite or explicitly structured hit sets. For those, use `count`, which relies on paper proofs.
- **Non-rigid finite type.** For example $n^3+n+4=m^2$ is non-rigid. The Python tool can then only scan. Certified hit lists for these families currently come from Sage's integral-point machinery (`crosscheck/`), not from Lean.
