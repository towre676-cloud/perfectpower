import Mathlib.Tactic

/-!
# Brainpool P-384: the r1 → t1 scaling, checked by the kernel

Constants of `brainpoolP384r1` and `brainpoolP384t1` as shipped by OpenSSL (`openssl ecparam
-name … -param_enc explicit`; RFC 5639 §3.6). `Z` is a fourth root of `−3/A` modulo `p`, computed
here; it is the one that maps the r1 generator onto the t1 generator. (The RFC text itself was not
reachable from this environment, so `Z` is not compared with the RFC's printed value; the three
congruences below are what define it.) All facts are integer congruences modulo `p`; the scaling
theorems of `CurveScaling` apply over `ZMod p` once `p` is known to be prime, which is not proved here.
-/

namespace PerfectPower.Brainpool384

/-- The field prime. -/
def p : ℤ := 0x8cb91e82a3386d280f5d6f7e50e641df152f7109ed5456b412b1da197fb71123acd3a729901d1a71874700133107ec53
/-- `A` of brainpoolP384r1. -/
def A : ℤ := 0x7bc382c63d8c150c3c72080ace05afa0c2bea28e4fb22787139165efba91f90f8aa5814a503ad4eb04a8c7dd22ce2826
/-- `B` of brainpoolP384r1. -/
def B : ℤ := 0x4a8c7dd22ce28268b39b55416f0447c2fb77de107dcd2a62e880ea53eeb62d57cb4390295dbc9943ab78696fa504c11
/-- `B` of brainpoolP384t1 (its `A` is `−3`). -/
def Bt : ℤ := 0x7f519eada7bda81bd826dba647910f8c4b9346ed8ccdc64e4b1abd11756dce1d2074aa263b88805ced70355a33b471ee
/-- The scaling factor. -/
def Z : ℤ := 0x41dfe8dd399331f7166a66076734a89cd0d2bcdb7d068e44e1f378f41ecbae97d2d63dbc87bccddccc5da39e8589291c
/-- The generator of r1. -/
def Gx : ℤ := 0x1d1c64f068cf45ffa2a63a81b7c13f6b8847a3e77ef14fe3db7fcafe0cbd10e8e826e03436d646aaef87b2e247d4af1e
/-- The generator of r1. -/
def Gy : ℤ := 0x8abe1d7520f9c2a45cb1eb8e95cfd55262b70b29feec5864e19c054ff99129280e4646217791811142820341263c5315
/-- The generator of t1. -/
def Gtx : ℤ := 0x18de98b02db9a306f2afcd7235f72a819b80ab12ebd653172476fecd462aabffc4ff191b946a5f54d8d0aa2f418808cc
/-- The generator of t1. -/
def Gty : ℤ := 0x25ab056962d30651a114afd2755ad336747f93475b7a1fca3b88f2b6a208ccfe469408584dc2b2912675bf5b9e582928

/-- **`A Z⁴ ≡ −3 (mod p)`**: the t1 curve has `a = −3`. -/
theorem a_scaled : (A * Z ^ 4 + 3) % p = 0 := by decide +kernel

/-- **`B Z⁶ ≡ B_t (mod p)`**. -/
theorem b_scaled : (B * Z ^ 6 - Bt) % p = 0 := by decide +kernel

/-- **`φ_Z(G) = G_t`**: the r1 generator maps onto the t1 generator. -/
theorem gen_scaled : (Z ^ 2 * Gx - Gtx) % p = 0 ∧ (Z ^ 3 * Gy - Gty) % p = 0 := by decide +kernel

/-- Both generators are on their curves. -/
theorem gen_on_curves : (Gy ^ 2 - Gx ^ 3 - A * Gx - B) % p = 0 ∧ (Gty ^ 2 - Gtx ^ 3 + 3 * Gtx - Bt) % p = 0 := by
  decide +kernel

/-- `Z` is invertible modulo `p` (`Z · Z⁻¹ ≡ 1`), with the inverse supplied. -/
theorem z_unit : (Z * 0x653667e5e2ff559db64702e4b51213d4d9b05653323d87347081dca72f5055b074727623d9832e67eaf3b49f6c077e8 - 1) % p = 0 := by decide +kernel

/-- The exported shared secret is the `x`-coordinate on the **original** curve: if an
implementation computes `Q' = φ_Z(Q)` on t1, it must return `Z⁻² x(Q')`, not `x(Q')`. For the
generator these differ (`Z² ≢ 1`). -/
theorem export_matters : (Z ^ 2 - 1) % p ≠ 0 := by decide +kernel

end PerfectPower.Brainpool384
