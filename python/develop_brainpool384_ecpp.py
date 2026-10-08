"""Generate or independently check the complete Brainpool-384 ECPP certificate."""
import argparse,json,subprocess
from pathlib import Path
from perfectpower.ecpp_certificate import BRAINPOOL384_PRIME,ecpp_chain_details
from perfectpower.elliptic_two_descent import gp_executable


def main():
    p=argparse.ArgumentParser();p.add_argument('--generate',action='store_true');p.add_argument('--gp');a=p.parse_args()
    out=Path(__file__).resolve().parents[1]/'receipts/brainpool384_ecpp';out.mkdir(exist_ok=True)
    if a.generate:
        script=f'default(parisize,128000000);\nsetrand(1);\nC=primecert({BRAINPOOL384_PRIME});print(C);print(primecertisvalid(C));\nquit\n'
        result=subprocess.run([gp_executable(a.gp),'-fq'],input=script,text=True,capture_output=True,timeout=120,check=True)
        lines=result.stdout.splitlines()
        if len(lines)!=2 or lines[-1]!='1':raise ValueError('ECPP generation failed')
        certificate=json.loads(lines[0])
    else:certificate=json.loads((out/'certificate.json').read_text())
    details=ecpp_chain_details(certificate,BRAINPOOL384_PRIME)
    (out/'certificate.json').write_text(json.dumps(certificate,indent=2)+'\n')
    (out/'details.json').write_text(json.dumps(details,indent=2)+'\n')
    print({k:v for k,v in details.items() if k!='rows'})


if __name__=='__main__':main()
