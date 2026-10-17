"""Publish only source-bound mathematics from the operator/induction bridge."""
import hashlib
import json
import subprocess
from pathlib import Path

from perfectpower.raghava_coxeter import receipt

ROOT=Path(__file__).resolve().parents[1]
WEB=ROOT/'web/integral-families'


def build():
    formal=json.loads((ROOT/'receipts/period_bridge_deep/unification_lean.json').read_text())
    if formal.get('kernel_checked') is not True:
        raise ValueError('Finite formalization has not passed its Lean audit')
    for name, expected in formal['source_sha256'].items():
        if hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=expected:
            raise ValueError('Formal proof source changed after checking: '+name)
    result=receipt(8)
    result['formalization']=formal
    names=['python/perfectpower/raghava_coxeter.py','python/tests/test_raghava_coxeter.py',
           'python/check_raghava_coxeter_lean.py','python/export_raghava_coxeter.py','python/perfectpower/period_bridge_cli.py',
           'docs/RAGHAVA_COXETER_UNIFICATION.md','python/perfectpower/e8_periods.py',
           'python/perfectpower/e8_lift.py']+list(formal['source_sha256'])
    result['source_sha256']={name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in names}
    result['note_url']='https://perfectpower-explorer-download.towre676.chatgpt.site/integrals/unification.html'
    raw=json.dumps(result,sort_keys=True,indent=2)+'\n'
    (ROOT/'receipts/period_bridge_deep/unification.json').write_text(raw)
    (WEB/'unification.json').write_text(raw)
    # Native MathML keeps the proof account readable without remote scripts.
    converted=subprocess.run(['pandoc',str(ROOT/'docs/RAGHAVA_COXETER_UNIFICATION.md'),
        '--from=markdown+tex_math_single_backslash','--mathml','--to=html5'],text=True,capture_output=True,check=True)
    if 'Could not convert TeX math' in converted.stderr:
        raise ValueError('A proof formula failed MathML conversion: '+converted.stderr)
    document=converted.stdout
    template=(WEB/'unification-template.html').read_text()
    (WEB/'unification.html').write_text(template.replace('__UNIFICATION_PROOF__',document))
    return dict(schema=result['schema'],finite_lean_theorems=formal['theorem_count'],
                analytic_series_formalized=False,bytes=len(raw.encode()),
                source_sha256=result['source_sha256'])


if __name__=='__main__':
    print(json.dumps(build()))
