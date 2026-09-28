import PerfectPower.Generated.Runge
import PerfectPower.Generated.Sandwich
/-! Adversarial tests of the verified checkers: every mutation of a valid certificate below is
*rejected by kernel evaluation* (`check … = false`).  Run with `lake env lean audit/CertReject.lean`
(part of `make audit`).  Mutations: a gap, an overlap, an off-by-one tail start, a changed
polynomial, a wrong exponent, a fake hit, a wrong gap witness, a flipped Runge sign, and a Runge
threshold that no longer matches its segments. -/
open PerfectPower PerfectPower.Reflect PerfectPower.Generated

-- the valid certificates are accepted
example : check cert_consecutive12_fourth_power_hits = true := by decide +kernel
example : rungeCheck cert_ljunggren_quartic_hits = true := by decide +kernel
-- gap: a segment removed
example : check { cert_consecutive12_fourth_power_hits with
    segs := cert_consecutive12_fourth_power_hits.segs.eraseIdx 3 } = false := by decide +kernel
-- overlap: a segment repeated
example : check { cert_consecutive12_fourth_power_hits with
    segs := cert_consecutive12_fourth_power_hits.segs.take 5 ++
      cert_consecutive12_fourth_power_hits.segs.drop 4 } = false := by decide +kernel
-- off-by-one tail start
example : check { cert_consecutive12_fourth_power_hits with
    c := cert_consecutive12_fourth_power_hits.c + 1 } = false := by decide +kernel
-- a producer that silently changed F.  Soundness binds the theorem to the certificate's own F, so
-- a changed F can only yield a true theorem about that F.  Indeed the unchanged cover also proves
-- that n(n+1)⋯(n+11) + 1 is never a fourth power (accepted):
example : check { cert_consecutive12_fourth_power_hits with
    F := 1 :: cert_consecutive12_fourth_power_hits.F.tail } = true := by decide +kernel
-- whereas F + 783616, which has the hit F(1) + 783616 = 148^4, is rejected:
example : check { cert_consecutive12_fourth_power_hits with
    F := 783616 :: cert_consecutive12_fourth_power_hits.F.tail } = false := by decide +kernel
-- wrong exponent
example : check { cert_consecutive12_fourth_power_hits with d := 3 } = false := by decide +kernel
example : rungeCheck { cert_ljunggren_quartic_hits with d := 1 } = false := by decide +kernel
-- fake hit and wrong gap witness
example : check { cert_consecutive12_fourth_power_hits with
    segs := .hit 1 0 :: cert_consecutive12_fourth_power_hits.segs.tail } = false := by decide +kernel
example : check { cert_consecutive12_fourth_power_hits with
    segs := .gap 1 0 :: cert_consecutive12_fourth_power_hits.segs.tail } = false := by decide +kernel
-- flipped sign of some G_t
example : rungeCheck { cert_ljunggren_quartic_hits with
    signs := cert_ljunggren_quartic_hits.signs.map (- ·) } = false := by decide +kernel
-- threshold moved without new segments
example : rungeCheck { cert_ljunggren_quartic_hits with
    x₀ := cert_ljunggren_quartic_hits.x₀ + 1 } = false := by decide +kernel
