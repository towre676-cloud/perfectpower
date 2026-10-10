"""Run from the extracted PerfectPower directory with Python 3.10 or newer."""
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent/'python'))
from perfectpower.__main__ import main
sys.argv=[sys.argv[0],'budget-lab',*sys.argv[1:]]
main()
