import json
import os
import unittest

from perfectpower.weil_orbit import (closed_form, commutant_dimension, orbit_census,
    orbit_basis, labelled_orbits, exact_orbit_certificate, transpose_fixed,
    exact_products_commute)


class WeilOrbitTests(unittest.TestCase):
    def test_closed_form_levels_2_to_160(self):
        for N in range(2, 161):
            self.assertEqual(commutant_dimension(N), closed_form(N), N)

    def test_prime_power_values_beyond_census(self):
        for N, want in ((81, 5), (125, 4), (128, 13), (243, 6), (256, 15), (343, 4), (512, 17)):
            self.assertEqual(commutant_dimension(N), want, N)

    def test_dyadic_primitive_orbits_die_and_imprimitive_survive(self):
        for N in (4, 8, 16, 32, 64):
            for rep, size, ok, d in orbit_census(N):
                self.assertEqual(ok, d >= 2, (N, rep))

    def test_conjugation_and_transpose_entry_phases_exactly(self):
        # Compare nonzero entry exponents modulo N; Fourier is never inverted.
        for N in range(1, 25):
            for s in range(N):
                for t in range(N):
                    for i in range(N):
                        for j in range(N):
                            self.assertEqual(((i+t)*(j+s) -
                                (s*t + s*i + (i+t)*j)) % N, 0)
                        j = (i-s) % N
                        self.assertEqual((i*i+t*i -
                            (-s*s+(t+2*s)*i+j*j)) % N, 0)
                        self.assertEqual((t*(i+s) - (s*t+t*i)) % N, 0)

    def test_exact_transpose_certificates(self):
        for N in range(1, 161):
            packet = exact_orbit_certificate(N)
            self.assertTrue(packet["all_surviving_orbits_transpose_fixed"])
            self.assertFalse(packet["execution_verified"])
            self.assertEqual(sum(r["size"] for r in packet["orbits"]), N*N)
        for N in (243, 256, 512, 625, 729):
            self.assertEqual(exact_orbit_certificate(N)["dimension"], closed_form(N))

    def test_twisted_convolution_independent_of_transpose_argument(self):
        for N in (3, 4, 6, 8, 9, 12, 16, 18):
            self.assertTrue(exact_products_commute(N), N)

    def test_transpose_phase_corruption_rejected(self):
        basis = orbit_basis(9)
        label = dict(next(x for x in basis if len(x) > 1))
        point = next(p for p in label if p[0] != 0)
        label[point] = (label[point] + 1) % 9
        self.assertFalse(transpose_fixed(9, label))

    def test_positive_levels_and_work_limits(self):
        self.assertEqual(commutant_dimension(1), 1)
        for N in (0, -1, True, 2.5, "8"):
            for fn in (closed_form, orbit_census):
                with self.assertRaises(ValueError):
                    fn(N)
        with self.assertRaises(ValueError):
            labelled_orbits(10, cell_limit=99)
        with self.assertRaises(ValueError):
            exact_products_commute(9, pair_limit=1)

    def test_query_preserves_finite_evidence_scope(self):
        from perfectpower.query_service import dispatch
        packet = dispatch(None, {"op": "weil_orbit_certificate", "args": {"level": 128}})
        self.assertEqual(packet["dimension"], 13)
        self.assertFalse(packet["execution_verified"])

    def test_against_certified_receipt_if_present(self):
        here = os.path.dirname(os.path.abspath(__file__))
        path = os.path.join(here, "..", "..", "receipts", "weil_commutant", "summary.json")
        if not os.path.exists(path):
            self.skipTest("receipt not present in this tree")
        with open(path) as stream:
            data = json.load(stream)
        for row in data["dimensions"]:
            self.assertEqual(commutant_dimension(row["level"]), row["dimension"], row["level"])


if __name__ == "__main__":
    unittest.main()
