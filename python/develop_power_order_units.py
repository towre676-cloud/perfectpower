"""Certified PARI maximal-order units for the three formerly unpriced orders."""
import argparse,json,subprocess
from pathlib import Path
from perfectpower.elliptic_two_descent import gp_executable
from perfectpower.power_order_units import power_order_unit_lattice,compile_binary_source

ROOT=Path(__file__).resolve().parents[1]
ORDERS=[(39,2),(48,30),(195,830)]


def main():
    p=argparse.ArgumentParser();p.add_argument('--gp');args=p.parse_args()
    script='default(parisize,128000000);\n'
    for P,Q in ORDERS:
        script+=f'B=bnfinit(x^3-{P}*x-{Q},1);ok=bnfcertify(B);nc=nfcertify(B.nf);print("PP:",[{P},{Q},B.nf.index,B.nf.disc,ok,nc,B.nf.sign,B.tu[1],vector(3,i,vector(3,j,Str(polcoef(B.nf.zk[i],j-1)))),vector(#B.fu,i,vector(3,j,Str(polcoef(lift(B.fu[i]),j-1))))]);\n'
    script+='quit\n'
    r=subprocess.run([gp_executable(args.gp),'-fq'],input=script,text=True,capture_output=True,timeout=30,check=True)
    rows=[json.loads(s[3:])for s in r.stdout.splitlines()if s.startswith('PP:')]
    warning='***   Warning: new stack size = 128000000 (122.070 Mbytes).'
    if len(rows)!=len(ORDERS) or '***'in r.stderr.replace(warning,''):
        raise RuntimeError('maximal-order computation failed: '+r.stderr[:400])
    packets=[]
    sources=json.loads((ROOT/'receipts/order_cost.json').read_text())['sources']
    for P,Q,m,disc,cert,nc,signature,torsion,basis,units in rows:
        if cert!=1 or nc!=[] or signature!=[3,0] or torsion!=2:
            raise ArithmeticError('uncertified totally real cubic unit group')
        c=power_order_unit_lattice([-Q,-P,0,1],basis,disc,units)
        if c['power_order_index']!=m:raise ArithmeticError('power-order index mismatch')
        c.update(P=P,Q=Q,bnfcertify=cert,nfcertify=nc,signature=signature,torsion_order=torsion,
                 maximal_unit_group_source='PARI bnf.fu with bnfcertify=1',
                 complete_power_order_unit_group=True)
        c['binary_sources']=[compile_binary_source(c,row['form'],row['phi'])for row in sources if (row['P'],row['Q'])==(P,Q)]
        packets.append(c)
        print(P,Q,'unit index',c['free_unit_index'],'basis',c['exponent_hnf_columns'],flush=True)
    out=ROOT/'receipts/power_order_units.json'
    out.write_text(json.dumps(dict(schema='pp-power-order-unit-frontier/1',orders=packets,
                   units_complete=3,lean_unit_generation_proofs=0),indent=2)+'\n')


if __name__=='__main__':main()
