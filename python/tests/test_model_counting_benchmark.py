import sys
import tempfile
import unittest
from pathlib import Path
from run_model_counting import acquire_output_lock,run

class BenchmarkHarnessTests(unittest.TestCase):
    def test_exclusive_output(self):
        with tempfile.TemporaryDirectory() as folder:
            path=Path(folder)/'result.json'
            with acquire_output_lock(path):
                with self.assertRaises(RuntimeError):acquire_output_lock(path)
            with acquire_output_lock(path):pass
    def test_statuses_and_timeout(self):
        with tempfile.TemporaryDirectory() as folder:
            log=Path(folder)/'log.txt';memory=6*1024**3
            exact=run([sys.executable,'-c',"print('c s exact arb int 123456789012345678901234567890')"],1,memory,log)
            self.assertEqual(exact['status'],'EXACT');self.assertEqual(exact['count'],'123456789012345678901234567890')
            approximate=run([sys.executable,'-c',"print('c s exact arb float 1.23e20')"],1,memory,log)
            self.assertEqual(approximate['status'],'NO_COUNT')
            limited=run([sys.executable,'-c',"print('{\"status\":\"WORK_LIMIT\",\"reason\":\"limit\"}')"],1,memory,log)
            self.assertEqual(limited['status'],'WORK_LIMIT');self.assertIsNone(limited['count'])
            error=run([sys.executable,'-c','raise RuntimeError("failed")'],1,memory,log)
            self.assertEqual(error['status'],'ERROR');self.assertIsNone(error['count'])
            timed=run([sys.executable,'-c','import time;time.sleep(5)'],.05,memory,log)
            self.assertEqual(timed['status'],'TIMEOUT');self.assertIsNone(timed['count']);self.assertLess(timed['seconds'],1)
if __name__=='__main__':unittest.main()
