# Focused validation

Lean 4.20.0 with the pinned Mathlib c211948581bde9846a99e32d97a03f0d5307c31e compiles the reusable BoundedResiduePatch module and all six generated native programs. The focused script audits seven general declarations and fifty generated declarations. All 57 records use only propext, Classical.choice and Quot.sound. No sorryAx or Lean.ofReduceBool occurs. The complete execution log and structured record are in receipts/bounded_residue_patch.

All twelve focused Python tests pass. They cover complete signed-box enumeration, omitted points and lifts, source mutation, inverse mutation, auxiliary point substitution, singular charts, composite moduli, exact budget rejection, empty-source exclusion, correct Mordell membership and public query dispatch. The previous fourteen residue-determinant tests and eleven concurrent power-free tests pass. The interface, query-space and native-bridge suites pass 27 further tests; no whole historical rebuild is claimed.

An independent full-box census compares the producer with a direct integer-coordinate scan for all parabola residue classes modulo 2,3,5,7,11: 28 complete lists agree. This is independent of both the Hensel stride enumeration and the coarse-grid replay checker. The earlier 120 SymPy determinant/rank comparisons reproduce, with 31 bounded zero certificates.

The corrected earlier Mordell packet contains only (3,5) and (3,-5); both lie on y squared = x cubed - 2. Its regenerated native program and the other ten earlier native programs are rechecked by make check-residue-determinant. The earlier false curve claim for (129,±1465) is explicitly corrected in both monographs.

The new four-page monograph and corrected five-page previous monograph are rendered and visually inspected. Complete tracked-source ZIP parts are checked against the published Git tree, including every concurrent session file. Each ZIP is below 30,000,000 bytes and can be extracted into the same directory. Package hashes and the immutable publication commit accompany the delivery.

Publication was refreshed onto concurrent singlet quantum completion 22a3c223fa0b081b24be9382f4207e6556fb438a. Its README addition merged cleanly and its focused tests pass; the complete archive includes its new source, receipts and PDF.
