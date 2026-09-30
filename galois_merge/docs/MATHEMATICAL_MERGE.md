# Symmetry, Effective Bounds, and Task-Specific Proof Compilation

## What this package actually contributes

The supplied Wilson Forge v0.26 archive was inspected directly. Selected original modules, exact rational program data, the native signature matrices, and theorem notes are preserved byte for byte with SHA256 provenance. The current PerfectPower repository, its 316-equation receipt, and the earlier full OEIS corpus were not present. This package therefore contains executable arithmetic primitives and derived-family experiments, rather than an invented replay of those unavailable objects. Existing project numbers such as 79 classes, 26 cubic fields, 220 descent nodes and 77 certified Mordell lists are supplied-report claims.

The immediate unification is a compiler contract: source problem and domain, target obligation, transformation, preserved restrictions, proof of coverage, terminal theorem, and verification cost. Forge supplies task-specific interfaces, exact transport composition, and directional execution accounting. PerfectPower supplies arithmetic semantics and the Lean completeness boundary. The Wilson/Hecke algebra is not asserted to be a Galois representation of the cubic fields.

## Exact unimodular transport

Represent a binary cubic by F=(c0,c1,c2,c3), meaning c0*x³+c1*x²*y+c2*x*y²+c3*y³. Store matrices in row-major order T=(a,b,c,d). Define G(u,v)=F(a*u+b*v,c*u+d*v). For determinant ±1, T induces a bijection of Z² and its inverse has integer entries. The package computes all four coefficients by exact binomial expansion, checks the inverse and polynomial identity, and transports absolute bounds: |x|≤|a|U+|b|V and |y|≤|c|U+|d|V whenever |u|≤U, |v|≤V.

The orientation is essential. A target point (u,v) maps to a source point T(u,v). Applying T inverse maps source points back to the target. Composition substitutes matrices in the order S*T: (F composed with S) composed with T equals F composed with S*T. Tests check these identities, discriminant preservation, deliberate coefficient mutations, and bound inequalities. All arithmetic is integer-exact.

The discriminant is b²c²−4ac³−4b³d−27a²d²+18abcd for coefficients (a,b,c,d). It is an invariant under unimodular changes, but equal discriminants do not prove equivalence. The edge discovery searches a bounded set of matrices and checks every returned identity. It deliberately makes no complete GL2 classification claim. A certified canonicalizer would require a termination argument, orbit invariance, and completeness of reduction, with boundary and stabilizer conventions handled exactly. Random invariance tests alone cannot establish these.

Branch domains must travel too. A parity condition, divisibility condition, or y-readout restriction is part of the obligation. The present discovery adapter refuses restricted nodes rather than silently forgetting restrictions. Extend it using explicit pullbacks P(T(u,v)), and prove that pullback theorem in Lean. A shared cubic field is not an edge of this equation-isomorphism graph.

## Proof DAGs and semantic keys

The interning routine merges only identical form/rhs/restriction payloads. Different rhs or restriction data produces a different key. This is a safe first step toward sharing repeated descent suffixes. General sharing via a transformation requires an explicit edge certificate and a proof that the child restriction is the pullback of the parent restriction. Hashes are indexing aids; the proof checker must compare actual payloads and validate actual identities, not assume hash equality is mathematical equality.

Do not collapse two nodes because they have the same field discriminant, modular signature, class label, or bounded solution list. The right quotient depends on what the terminal proof needs. Empty leaves need universal impossibility; solution leaves need complete lists with their inverse readout. The desired extension is a finite DAG whose nodes partition or cover solutions and whose leaves are empty certificates, proved bounded enumeration, exact factorization, or an imported previously proved obligation.

Forge's linear residual-Hankel machinery models a coefficient series. Arithmetic descent is nonlinear and is not automatically that model. Reuse exact suffix sharing and cost accounting first. Any richer behavioral minimization needs its own arithmetic congruence theorem establishing that the retained state preserves all future obligations.

## Task-adapted interfaces

Forge's section theorem concerns linear maps f:T→C and g:S→C. A lift s with g*s=f exists iff image(f) is contained in image(g); an injective lift additionally needs dim ker(g)≥dim ker(f). These are genuine finite-dimensional linear statements. They do not imply that a nonlinear Thue equation admits a finite proof representation.

The transferable engineering principle is to choose the smallest sufficient proof interface. For a representative Thue obligation, the interface might be a complete seed list, a proved exponent bound, and exact lattice membership. It need not expose every operation of a general number-field library. Each interface should have an explicit completeness premise and an independently checkable consumer theorem.

Forge's invariant channel-rank analysis also warns that apparent sparsity depends on coordinates. In arithmetic, a small matrix or a short coefficient vector can conceal large denominator or lattice-index costs. Optimize height, lattice index, proof-term size, and checking time together rather than declaring a representation optimal from one coordinate count.

## The remaining nonempty Thue branches

For irreducible F and theta a root of F(t,1), F(a,b)=c0*N(a−b theta). Norm solutions can be organized using ideal factorizations and units, but the original problem constrains the element to a specific two-dimensional lattice. Totally real cubic fields have unit rank two. A future certificate may express candidates as gamma*epsilon1^n1*epsilon2^n2 with complete seed coverage, then prove bounds on n1,n2 and exhaust the remaining region.

Shared fields can reuse verified multiplication tables, embeddings, unit data and selected analytic bounds. They do not share the same order, lattice, seeds or target automatically. The next meaningful pilot chooses one field shared by several obligations and establishes one reusable effective argument with separately proved obligation-specific inputs. PARI outputs remain external evidence until those completeness arguments are replayed. The package does not claim a Baker, Skolem, or global Thue solver implementation.

## D=72 and local-global diagnosis

The two reportedly empty D=72 classes need an exact local problem, including their actual restrictions. Testing primes to 43 does not prove everywhere local solvability. At exceptional primes, a nonsingular residue point and a proved lifting theorem can establish compatible solutions at all powers. At other primes, prove point existence as well as smoothness; smoothness alone does not provide a point. Include the real place and the justification for covering untested primes.

If the restricted equations are everywhere locally soluble, identify whether global failure concerns rational points, integral points, norm elements in a sublattice, or simultaneous unit conditions. These are distinct claims. A local-global obstruction must be established, not assigned from failure of bounded searches. An elementary specialized descent may still be the best first completeness proof.

The generic modular kernel here exhausts all pairs modulo q and records exact emptiness. It is useful for experiment and checking small terminal certificates; it is not the optimized 220-node p-adic checker from the unavailable current repository. Do not replace that successful checker with this slower exploratory routine.

## Positive k

For positive nonsquare k, (y+sqrt(k))(y−sqrt(k))=x³ lives in a real quadratic order. With a certified fundamental unit epsilon, epsilon^(3q+r)=(epsilon^q)³ epsilon^r for r=0,1,2. The sign is itself a cube. This reduces an infinite unit action to finitely many unit classes modulo cubes, but does not enumerate the residual branch solutions.

A complete reduction needs the actual ring of integers, unit generation, ideal-class coverage, common-factor valuations and integral readout. Square k uses a separate rational-factorization dispatch. QuadOrbit contributes a unit-orbit interface only after its coverage hypotheses are connected to the descent. First prove one positive-k family through the entire reduction and terminal enumeration.

## Sequence observations and indexing

A sequence is an observation plus a starting coordinate and domain. The corpus adapter reads raw .seq entries, preserves byte hashes, parses the true first offset, and checks the equation a(n)=B(n+s) over the supplied terms. This differs from indexing by list position. A source with offset one uses different shift parameters from one with offset zero. Tests deliberately check this distinction.

Matching finitely many terms does not prove an infinite sequence definition. A048624 remains an inspected shifted interpretation unless its source definition supplies a full recurrence or another exact characterization. Strict monotonicity can prove uniqueness of a shift throughout an admissible family when the first coordinate is in its increasing region; it cannot turn a finite prefix into the missing source semantics.

The earlier full OEIS ZIP was not available here. Use corpus_adapter.py on the actual repository's data/oeis or on the existing full corpus ZIP. It reads ZIP members without extracting the corpus and cannot promote entries. No downloaded terms or invented OEIS files were included.

## Cost and execution semantics

Forge v0.26 distinguishes written-order algebra construction from reverse-order column execution. Its 82/81 and 114/92 call counts refer to those separate models. For PerfectPower record discovery time, certificate emission, elaboration, kernel reduction time, peak RSS and proof-artifact bytes separately. Small node counts alone do not guarantee low kernel memory. Integer coefficient height and shared theorem boundaries matter.

The selected five Forge rational programs are checked exactly against the stored integral word matrices, and signature geometry is recomputed from the supplied finite-field matrices. These executions validate the selected source arithmetic, not every theorem or every archive manifest. Modular signature facts remain finite-field facts; exact rational equalities are checked separately. No Forge theorem is thereby promoted to Lean.

## Next integration release

Copy this package under a dedicated directory in the current repo. Export the actual 316 obligations into the documented adapter schema, retaining curve, branch, readout and restriction identifiers. Compare exactly verified edges with the existing 79-class receipt. Use the DAG primitive to measure exact repeated suffixes before adding general merging. Run the corpus adapter on committed raw sequences. Port transport and bound theorems to the pinned Lean toolchain, then integrate with complete_of_thue. Preserve all existing classifications and source attribution.

Report measured savings, new complete curves, and remaining hypotheses. Update the canonical reader and ship the complete relevant repo as a new checkpoint. This additive package itself claims no newly closed curve or newly compiled Lean declaration.
