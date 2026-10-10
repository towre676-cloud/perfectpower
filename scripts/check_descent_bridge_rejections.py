"""Ensure omitted support and omitted projective charts are rejected by Lean."""
import hashlib,json,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
HEADER='import PerfectPower.LocalQuarticBridges\nimport PerfectPower.IsogenyCoordinates\n'
CASES={
 'complete_signed_support':(True,'''
example : ∀ d ∈ Finset.Icc (-12:ℤ) 12,
    (∀ e ∈ ([2,3]:List ℤ), ¬e*e∣d) → d ∣ (-12:ℤ) →
    d ∈ ([-6,-3,-2,-1,1,2,3,6]:List ℤ) := by decide
'''),
 'omitted_negative_support':(False,'''
example : ∀ d ∈ Finset.Icc (-12:ℤ) 12,
    (∀ e ∈ ([2,3]:List ℤ), ¬e*e∣d) → d ∣ (-12:ℤ) →
    d ∈ ([1,2,3,6]:List ℤ) := by decide
'''),
 'unit_denominator_chart_alone':(True,'''
example : ∀ r s : ZMod 8, s^2 ≠ (-3:ZMod 8)*r^4+(-5:ZMod 8)*r^2+(-6) := by decide
'''),
 'omitted_nonunit_chart':(False,'''
example : ∀ r s : ZMod 8, (∃ t : ZMod 8, r*t=1) ∨
    s^2 ≠ (-3:ZMod 8)+(-5:ZMod 8)*r^2+(-6:ZMod 8)*r^4 := by decide
'''),
 'altered_isogenous_coefficient':(False,'''
example : ((2:ℚ)*(1-3/(1:ℚ)^2))^2 = ((1:ℚ)+3)*(((1:ℚ)+3)^2-3*3) := by decide
'''),
 'altered_reconstructed_y_sign':(False,'''
example : (2:ℚ)=(1:ℚ)*1*(-2)/(1:ℚ)^3 := by decide
''')}
def main():
 out=ROOT/'receipts/descent_bridges/rejections';out.mkdir(parents=True,exist_ok=True)
 records=[]
 for name,(accept,source) in CASES.items():
  path=out/(name+'.lean');path.write_text(HEADER+source)
  run=subprocess.run(['lake','env','lean',str(path)],cwd=ROOT,text=True,capture_output=True)
  (out/(name+'.log')).write_text(run.stdout+run.stderr)
  actual=run.returncode==0
  assert actual==accept,(name,run.stdout,run.stderr)
  if accept:assert not run.stdout.strip() and not run.stderr.strip(),name
  else:assert "tactic 'decide'" in run.stdout and ("is false" in run.stdout or "failed" in run.stdout),name
  records.append(dict(case=name,expected_acceptance=accept,accepted=actual))
 (out/'verification.json').write_text(json.dumps(dict(schema='pp-descent-rejections/1',cases=records,source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__).resolve(),*sorted(out.glob('*.lean'))]}),indent=2)+'\n')
 print(json.dumps(dict(cases=len(records),passed=True)))
if __name__=='__main__':main()
