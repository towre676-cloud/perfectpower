"""Reject malformed accounting receipts instead of trusting summary totals."""
import importlib.util
import json
from pathlib import Path
import struct
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location('compiled_evidence', ROOT/'independent_checks/planning_compiled/reproduce_evidence.py')
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


class CompiledEvidenceTests(unittest.TestCase):
    def test_prefix_accounting_and_rejection(self):
        with tempfile.TemporaryDirectory() as tmp:
            d = Path(tmp); p = d/'prefixes.bin'; r = d/'results_w0.jsonl'
            data = b'PFX1'+struct.pack('<4I3Q',50,5,13,2,10,5,16)
            for lo,hi in ((2,7),(3,9)):
                data += bytes([13,0,0,0])+struct.pack('<5H2Q',0,0,0,0,0,lo,hi)
            p.write_bytes(data)
            r.write_text(json.dumps({'prefix':0,'exact':5,'expansions':8})+'\n')
            self.assertEqual(MOD.prefix_accounting(p,d)['interval'],[18,24])
            r.write_text(r.read_text()*2)
            self.assertEqual(MOD.prefix_accounting(p,d)['prefixes_solved'],1)
            for row in ({'prefix':2,'exact':5,'expansions':0},
                        {'prefix':0,'exact':9,'expansions':0},
                        {'prefix':0,'exact':True,'expansions':0},
                        {'prefix':0,'exact':5,'expansions':-1}):
                r.write_text(json.dumps(row)+'\n')
                with self.assertRaises(ValueError): MOD.prefix_accounting(p,d)
            r.write_text('')
            for invalid in (data[:-1],data+b'x',data[:20]+struct.pack('<3Q',10,6,16)+data[44:]):
                p.write_bytes(invalid)
                with self.assertRaises(ValueError): MOD.prefix_accounting(p,d)
            tied = bytearray(data)
            struct.pack_into('<Q',tied,36,15)  # header sum_hi
            struct.pack_into('<Q',tied,len(tied)-8,8)  # second upper bound, width 5
            p.write_bytes(tied)
            r.write_text(json.dumps({'prefix':0,'exact':5,'expansions':8})+'\n')
            with self.assertRaisesRegex(ValueError,'partly solved width tie'):
                MOD.prefix_accounting(p,d)

    def test_recorded_result_is_not_a_replay(self):
        result=MOD.recorded_final()
        self.assertEqual(result['recorded_exact_count'],702508860122761)
        self.assertFalse(result['checkpoint_recovered'])
        self.assertFalse(result['exhaustive_search_replayed'])


if __name__ == '__main__': unittest.main()
