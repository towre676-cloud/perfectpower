from src.engine import write_receipts
import argparse
p=argparse.ArgumentParser();p.add_argument('--upper',type=int,default=100000);p.add_argument('--out',default='receipts');a=p.parse_args()
rows=write_receipts(a.out,a.upper)
print('Curves:',len(rows),'nonempty in bounded scan:',sum(bool(r['points']) for r in rows),'signed points:',sum(len(r['points']) for r in rows))
