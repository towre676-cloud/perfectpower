# The k=22 source and its complete curve list

All 100 chunks, the assembled source theorem, the complete curve theorem and the emitted whole-query equivalence have passed Lean 4.20.0. The focused axiom audits use only propext, Classical.choice and Quot.sound.

For y²=x³+22, the class-list reduction has two binary-cubic classes. The reducible-looking class (0,-3,0,-22) is impossible modulo 9. The remaining class is

$$F(u,v)=-u^3-6u^2v-3uv^2-4v^3.$$

In the integral order z³=9z−14, it has the exact encoding

$$F(u,v)=-\operatorname{Norm}((u+2v)-vz).$$

The unit η=(388537,-357959,99671) has inverse ε=(-199,609,185). The rank-one certificate brackets the real root and bounds the reduced unit representatives. Its original rational slab contains 971,659 lattice candidates, with C=99,671. The checked denominator-clearing theorem preserves every original floor and ceiling endpoint. It does not enlarge or truncate the box.

The integer version partitions the slab into 100 modules of 2,000 slices. Each module proves the original rational slab predicate using `decide +kernel`, after rewriting by exact endpoint equality. No `native_decide` or custom axiom is used. The final source combines these checks with the two inverse-unit identities, unit norm identities, rational certificate conditions, and the two checked Skolem periods at the prime 3. Its proved all-integer statement is

$$-u^3+9uv^2-14v^3=1\quad\Longleftrightarrow\quad u=-1\ \text{and}\ v=0.$$

Applying it at u+2v proves F(u,v)=1 exactly at (-1,0). The class-list proof enumerates all 82 reduced forms in its finite coefficient box (|a|≤4 and |b|,|c|≤14), supplies exact unimodular transports to the two classes, and checks nine slices. This is what upgrades a solved source equation to completeness for the original curve. The proved curve theorem is

$$y^2=x^3+22\quad\Longleftrightarrow\quad(x,y)\in\{(3,-7),(3,7)\}.$$

`parallel_formula/k22` then uses that curve theorem through the existing finite-formula emitter. It retains the complete-query Lean certificate, original SMT input, finite replacement and source hashes. The illustrative additional constraint x>3 rejects both points. A bounded search for points, successful generation of a Lean file, or a solver answer is not substituted for the source and curve completeness checks.

Reproduction uses `python3 python/rank_one_split.py --integer --slices 2000`, followed by `python3 scripts/check_k22_split.py --resume`. The sequential checker records proof-input identities and reuses only matching accepted checks with an existing Lean object. The generator preserves matching receipt identities; any changed imported Lean source or toolchain pin changes that identity. The heavy-build script prebuilds the independent chunks sequentially before asking Lake to build the assembled source.

The earlier uncommitted 53-chunk job was removed by workspace maintenance. The current computation starts from the committed first-chunk proof and does not treat the lost artifacts as a completed source. The retained check log and validation receipt distinguish checks performed now from that historical checkpoint.
