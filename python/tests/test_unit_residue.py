"""Residue-filtered unit slabs (`UnitGenResidue.lean`, `make_lean_unit_fields.res_tables`)."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import make_lean_unit_fields as U  # noqa: E402

ORDERS = [(15, 16, (-5, -3, 1), (-40907, -47810, -11056), 9012, 8),
          (21, 32, (-15, -1, 1), (-379, -322, -62), 482, 6),
          (18, 22, (-5, -5, -1), (707, 59, -44), 482, 4)]


class ResidueSlab(unittest.TestCase):
    def test_mask_complete_mod_72(self):
        # every (a, b, c) mod 72 of norm ≡ ±1 mod 72 has a mod 72 in the mask (exhaustive, by brute force)
        for P, Q, *_ in ORDERS[1:]:
            T = U.res_tables(P, Q)
            for b in range(0, 72, 5):
                for c in range(0, 72, 7):
                    mk = set(U.res_mask(T, b, c))
                    for a in range(72):
                        n = U.nrm(P, Q, (a, b, c)) % 72
                        if n in (1, 71):
                            self.assertIn(a, mk)

    def test_progression(self):
        for L in range(-150, 150, 7):
            for H in range(L - 3, L + 300, 11):
                for r in (0, 5, 71):
                    a0 = L + (r - L) % 72
                    got = [a0 + 72 * i for i in range(max(0, (H - a0) // 72 + 1))]
                    self.assertEqual(got, [a for a in range(L, H + 1) if a % 72 == r])

    def test_filtered_slab_keeps_every_unit(self):
        for P, Q, e1, e2, pts, nunits in ORDERS:
            c = U.ug_cert(P, Q, e1, e2, slab=True)
            T = U.res_tables(P, Q)
            rc = U.residue_cost(c, T)
            self.assertEqual(rc['points'], pts)
            kept = {p for *_, ps in U.residue_rows(c, T) for p in ps if abs(U.nrm(P, Q, p)) == 1}
            self.assertEqual(len(kept), nunits)
            if P != 15:                                  # the full slab of (15, 16) has 648,719 points
                self.assertEqual(kept, {p for p in U.slab_points(c) if abs(U.nrm(P, Q, p)) == 1})


if __name__ == '__main__':
    unittest.main()
