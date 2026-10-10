#!/usr/bin/env python3
"""Run exact DIMACS counting directly from an extracted complete checkout."""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent/'python'))
sys.argv.insert(1,'model-count')
from perfectpower.__main__ import main
main()
