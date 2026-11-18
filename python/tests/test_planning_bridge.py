"""Small literal trace and adversarial record mutations for the Lean bridge.

The semantic population is proved separately in PlanningReplayExamples.lean;
these tests do not promote Python acceptance to a Lean theorem.
"""
import struct
import tempfile
import unittest
from pathlib import Path
from perfectpower.planning_certificate import InvalidCertificate, verify

HEADER = b'PPBDD001' + struct.pack('<2Ii3I', 3, 1, 0, 0, 1, 0)
RECORDS = [
    (1, 1, 1, 0, 2, 0, 0, 0),  # level-one node, one free suffix bit
    (2, 0, 1, 0, 2, 0, 0, 0),  # threshold [1,0] <= 0
    (2, 0, 0, 0, 2, 1, 1, 0),  # zero-weight head, reduced equal branches
    (4, 0, 2, 2, 2, 0, 4, 0),  # one skipped root variable, count 4
    (5, 2, 4, 0, 0, 0, 0, 0),
]


def stream(records):
    return HEADER + b''.join(struct.pack('<8I', *r) for r in records)


class BridgeFixture(unittest.TestCase):
    def setUp(self):
        self.work = tempfile.TemporaryDirectory()
        self.path = Path(self.work.name)/'fixture.bin'

    def tearDown(self):
        self.work.cleanup()

    def check(self, records):
        self.path.write_bytes(stream(records))
        return verify(self.path, [[0,1,0]], [0])

    def test_literal_trace(self):
        self.assertEqual(self.check(RECORDS)['count'], 4)
        self.assertEqual(self.check(RECORDS)['records_by_tag'], [1,2,0,1,1])
        # Independently match the bytes in the kernel-decoded Lean allocation.
        source = (Path(__file__).resolve().parents[2]/'PerfectPower/PlanningTraceDecode.lean').read_text()
        import re
        values = re.search(r'def fixture : List UInt8 :=\s*\[([^]]+)\]', source).group(1)
        lean_bytes = bytes(int(x.strip()) for x in values.split(',') if x.strip())
        self.assertEqual(lean_bytes, struct.pack('<8I', *RECORDS[0]))

    def test_semantic_mutations(self):
        attacks = [(0,4,1), (0,5,1), (1,3,1), (2,5,0), (3,6,2), (4,2,8),
                   (0,6,1), (1,7,1), (3,1,1), (4,4,1), (4,0,6)]
        for record, field, value in attacks:
            with self.subTest(record=record, field=field):
                changed = [list(r) for r in RECORDS]
                changed[record][field] = value
                with self.assertRaises(InvalidCertificate):
                    self.check(changed)

    def test_missing_stage_and_trailing_record(self):
        for changed in (RECORDS[:3]+RECORDS[4:], RECORDS+RECORDS[-1:], RECORDS[:-1]):
            with self.assertRaises(InvalidCertificate):
                self.check(changed)


if __name__ == '__main__':
    unittest.main()
