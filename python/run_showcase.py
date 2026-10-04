"""Build the complete demonstration packets; optionally benchmark installed Z3."""
import argparse
from pathlib import Path
from perfectpower.showcase import build_examples,benchmark_queries

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'receipts/showcase')
parser.add_argument('--benchmark',action='store_true')
parser.add_argument('--timeout-ms',type=int,default=2000)
parser.add_argument('--repeats',type=int,default=3)
args=parser.parse_args()
r=build_examples(args.output)
print('Complete hidden-needle points:',len(r['hidden_needle']['complete_points']))
print('Square-triangular count:',r['square_triangular']['query']['unfiltered_count'])
print('Residue-filtered count:',r['square_triangular']['query']['filtered_count'])
print('Whole queries reduced:',len(r['whole_queries']))
if args.benchmark:
    b=benchmark_queries(args.output,timeout_ms=args.timeout_ms,repeats=args.repeats)
    print('Timing results:',b['summary'])
