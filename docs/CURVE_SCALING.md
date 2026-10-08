# Curve scaling: the Brainpool r1 → t1 isomorphism

The Brainpool "twisted" curves of RFC 5639 come from the map φ_Z(x, y) = (Z²x, Z³y). For
E: y² = x³ + Ax + B over a field and Z ≠ 0, φ_Z sends E onto E′: y² = x³ + (AZ⁴)x + BZ⁶. Brainpool
chooses Z with AZ⁴ = −3. The inverse uses Z⁻² and Z⁻³, so this is an isomorphism over the same field,
not a quadratic twist.

## Proved in Lean, with no premise

[`CurveScaling.lean`](../PerfectPower/CurveScaling.lean), over any field:

| theorem | statement |
|---|---|
| `residual` | (Z³y)² − (Z²x)³ − (AZ⁴)(Z²x) − BZ⁶ = Z⁶(y² − x³ − Ax − B), in any commutative ring |
| `residual_zero_iff_of_isUnit` | curve-equation membership is equivalent in any commutative ring when Z is a unit, including composite residue rings |
| `equation_iff`, `nonsingular_iff` | a point is on E (nonsingular) iff its image is on E′ (nonsingular), for Z ≠ 0 |
| `slope_scale` | the chord and tangent slope scales by Z, including the degenerate cases |
| **`phi_add`** | φ_Z(P + Q) = φ_Z(P) + φ_Z(Q) for Mathlib's group law on `WeierstrassCurve.Affine.Point` |
| `phi_zsmul` | φ_Z([n]P) = [n]φ_Z(P) |
| **`phiEquiv`** | φ_Z is a group isomorphism E(F) ≃ E′(F) (`phi_injective`, `phi_surjective`) |

[`Brainpool384.lean`](../PerfectPower/Brainpool384.lean) is checked by the kernel on the 384-bit
constants. The constants are brainpoolP384r1 and brainpoolP384t1 as shipped by OpenSSL; the RFC text
was not reachable from this environment. The checks are integer congruences modulo p:
- A·Z⁴ ≡ −3 and B·Z⁶ ≡ B_t, with a Z computed here as a fourth root of −3/A;
- φ_Z maps the r1 generator onto the t1 generator. The other root −Z maps it to the negative of the
  t1 generator.
- Both generators lie on their curves, and Z is invertible.
- Z² ≢ 1. So an implementation that computes on t1 must export Z⁻²·x′, not x′: the two values differ.

## Not claimed

- **Lean primality of p.** A complete fifteen-stage ECPP certificate now proves the modulus
  prime mathematically; see [the descent and primality monograph](MORDELL_TWO_DESCENT_MONOGRAPH.md).
  Its exact arithmetic is checked independently of PARI. A compiled Lean primality theorem
  is still needed to instantiate the field theorems inside ZMod p. The ring-level
  `residual_zero_iff_of_isUnit` needs only invertibility of Z to preserve the equation; it does
  not establish the point-group isomorphism over these concrete constants.
- **No implementation is verified.** There is no TLS code, no P-384 or Brainpool scalar-multiplication
  code, and no proof that any library exports the right coordinate.
- **Nothing about constant-time behaviour or side channels.** Algebraic equivalence says nothing
  about timing; RFC 8734 flags side-channel concerns around this transformation.
- **The Mordell results do not transfer.** y² = x³ + k has A = 0, and AZ⁴ = 0 stays 0. What is shared
  is the transport machinery, not the integer-point lists. Integral points also give no way to
  recover secret scalars.

## Next

The next steps are a primality certificate for p, to apply the theorems in ZMod p, and a check
that a reference and an optimized scalar multiplication agree after transport. After that, P-384
(already A = −3): its formulas and multiword modular arithmetic, and fixed-length x-coordinate
encoding with leading zeros kept.
