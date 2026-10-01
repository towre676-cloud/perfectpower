"""Re-export VCs from the pinned independent Why3 sources using installed Why3."""
import argparse,pathlib,subprocess
ROOT=pathlib.Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--why3',default='why3');ap.add_argument('--config')
ap.add_argument('--drivers',required=True,help='Installed Why3 1.6 driver directory');ap.add_argument('--output',required=True)
a=ap.parse_args();out=pathlib.Path(a.output).resolve();out.mkdir(parents=True,exist_ok=True)
base=[a.why3]+(['-C',a.config] if a.config else [])
for source,driver in [('isqrt.mlw','z3.drv'),('isqrt_von_neumann.mlw','z3_487.drv')]:
 subprocess.run(base+['prove',str(ROOT/'upstream/hipsleek__why3/examples'/source),'-a','split_vc',
                     '-D',str(pathlib.Path(a.drivers)/driver),'-o',str(out)],check=True)
print('Exported VCs; path comments may change source hashes. Re-derive certificates for new bytes.')
