# All-future operator identities checked in Lean

This follow-up to the operator-recovery release moves its key infinite-time conclusion into Lean and applies it to all seven supplied recurrence comparisons. Five generic theorems describe commuting transport, invariant zero outputs, finite matrix certificates and task-lift obstructions. Seven generated theorems prove zero difference outputs at every nonnegative index for the concrete paired recurrence models. This is a mathematical conclusion about the supplied models, not an independent identification of their OEIS definitions.

## The finite certificate behind an infinite conclusion

For a state operator A, a coordinate receiver C, an internal operator B and output matrix H, the certificate consists of

    AC=CB, HC=0, seed=Cz.

The first identity means that the image of C is stable under A. Induction gives A^t(Cz)=C(B^t z) for every natural t. The second identity then gives H A^t(seed)=0 for every t. Independence of C's columns is unnecessary for this implication: redundant spanning vectors can still provide a sound certificate. The Python Krylov algorithm finds independent columns for economy, but the Lean soundness theorem trusts neither that algorithm nor its independence claim.

OrbitRecovery.transport proves the orbit-transport identity for arbitrary functions with a commuting receiver. zero_output adds a readout that vanishes on the receiver's image. invariant_zero states the corresponding result for an invariant submodule and linear readout. matrix_zero packages the finite rational matrix form used by the generated examples. These results do not rely on numerical eigenvalues, a tested orbit length or a claimed rank stabilization.

## Seven actual checked comparisons

The generator reads the staged recurrence atlas and supplied generating-function bridges, constructs their companion operators, and compares the definitions using the existing exact Krylov calculation. It emits literal rational matrices and a seed representation for A048739, A052995, A078057, A128588, A176981, A212804 and A373566. The generating-function state for A128588 is advanced by its recorded offset of one before forming the paired state.

For each pair, A is the direct sum of the two companion operators. H subtracts their first coordinates. C consists of the independent paired orbit vectors, and B shifts these columns, using the final closure coefficients for the last column. The first coordinate vector z represents the original seed. Lean checks AC=CB, HC=0 and seed=Cz by kernel evaluation, then invokes matrix_zero for every future index.

The theorem statements expose the exact state operator, seed and readout through named definitions. Their conclusion is that the difference readout vanishes for all natural times. The association of the literal matrices with a source file is recorded by sequence identifier, offset and SHA256 in the generated source. The source-file parsing and recurrence discovery implementation is not itself verified; changing the generator or input can change which supplied definitions are emitted. The arithmetic certificate identities and all-future conclusion are independently checked by Lean.

This distinction matters. Previously the seven comparisons were exact Python invariant-subspace calculations with execution_verified=false. Now each committed paired operator has a Lean all-future theorem. The sequence atlas still cannot promote an OEIS prose definition merely because its sampled terms agree with that operator. That further step requires proving that the intended sequence satisfies the defining recurrence or generating function.

## Task-lift obstructions

OrbitRecovery.lift_obstruction formalizes the negative witness returned by task_section. If a linear functional a kills the image of G but a(Fw) is nonzero for some source w, then no linear map T can satisfy GT=F. Assuming a lift would give a(Fw)=a(GTw)=0, a contradiction. This is an obstruction to every possible linear lift, not merely a failure of the chosen elimination routine.

The theorem does not prove the full image-containment characterization of lift existence or the kernel-dimension criterion for injective lifts. Nor does it formalize the generic Fitting decomposition algorithm, the five-arrow algebra's unit criterion, or the field-756 global exponent bound. Those remain distinct next developments. The current all-future certificates handle their own infinite-time statement without requiring any of those missing results.

## Reproduction and validation

Run scripts/check_orbit_recovery.sh from a configured Lean 4.20.0 checkout. It regenerates the seven certificates, compiles the generic and generated modules, checks twelve theorem axiom reports and runs the operator-recovery tests. Kernel evaluation is used for the literal matrix identities; native_decide is not used. Only propext, Classical.choice and Quot.sound are permitted by the audit. An additional negative control rejects a false entry in an actual certificate.

The main PerfectPower module imports both new Lean modules. The generated source is committed alongside its generator so that the exact mathematical statements remain reviewable even without rerunning sequence acquisition. Validation is targeted; no full rebuild of the historical heavy Lean corpus is claimed.
