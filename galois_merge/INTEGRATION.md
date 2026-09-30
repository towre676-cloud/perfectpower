# How the Galois × Forge package was integrated

The package was added **additively**: its files are kept as received under `galois_merge/`.
The repository work it asked for lives in the repository's own modules.

## Provenance

- `vendor/forge/` holds the selected original Wilson Formation Forge bytes. All 109 member hashes
  match `receipts/vendor_sources.json`, which also records the source archive SHA-256. They were
  re-checked after `run_experiments.py`.
- **Version label mismatch, kept as is.** The archive is labelled `WILSON_FORMATION_FORGE_v0.26.0`,
  but its root `vendor/forge/README.md` begins "WILSON FORMATION FORGE v0.25.0". The v0.26 dual
  execution notes are present in the archive, so the README is stale. It is left unchanged
  because it is original bytes.
- No Wilson algebra or number-field identification is asserted anywhere in the repository.

## What ran

- The package's own tests: 8 OK (`make test` now runs `galois_merge/tests`).
- `run_experiments.py`: 5 exact Forge programs, 1200 transport certificates and 1000 modular
  checks. The Forge checks need NumPy, so they ran under the Sage Python. These are the package's
  derived experiments, not the 316 real branches.
- **On the real data** (`run_repo_adapters.py`, part of `make receipts`, writing
  `receipts/galois_adapters.json`):
  - `branch_adapter` logic on the **316 actual Thue obligations** of `receipts/thue_graph.json`,
    with matrix entries bounded by 2 and every edge re-checked exactly:
    - 474 edges, **0** between different repository classes;
    - the edges connect the nodes into exactly the repository's **79** classes;
    - with the readout restrictions attached, the adapter finds 0 edges: it refuses unrestricted
      maps between restricted nodes. Restrictions pull back along `T` by
      `PerfectPower.Interfaces.restricted_transport`.
  - `corpus_adapter` logic on the **144 committed `.seq` files**: `B`-index shifts A000129 at 0,
    A048624 at 2, and A069306 at 1. All three are finite agreement only; nothing is promoted.

## What was ported into Lean (`PerfectPower/Interfaces.lean`, axiom-audited)

| package draft (`lean/IntegerTransport.lean`, never compiled) | repository theorem |
|---|---|
| `cubic`, exact substitution | `ThueLocal.evalF`, `compF`, `evalF_compF` (already present) |
| `determinant_one_inverse` | `ThueLocal.sols_transport` (inverse for `det = ±1`) |
| `complete_transport` (restrictions in `P`) | `Interfaces.restricted_transport`, `restricted_empty` |
| composition | `Interfaces.mulM`, `evalF_compF_mul`, `detM_mul` |
| bound transport | `Interfaces.bound_transport` |
| offset/shift checks | `Interfaces.shift`, `shift_shift`, `split_prefix`, `A048624_shift_unique` |

The draft file itself stays here as received and is not part of the build.

## Interning

`python/make_lean_thue_branch.py` now interns **exact** repeated descent subproblems. The 15
certificates become DAGs of 178 nodes (220 as trees), and the leaf work drops from 2,487 lifts
to 2,008. GL₂(ℤ)-equivalent but non-identical nodes are **not** shared: 163 exact against 108
up to GL₂(ℤ), and sharing those would need a transport step inside the checker. A field match
is never treated as an equivalence.

## The mathematical asks

See `docs/MORDELL_BRANCH.md` §5 and §7:
- the canonicalizer qualification;
- the D = 72 local–global diagnosis;
- solution-preserving descent;
- the field-756 pilot;
- the positive-`k` interface.

See `docs/OEIS.md` for the three A048624 claims.
