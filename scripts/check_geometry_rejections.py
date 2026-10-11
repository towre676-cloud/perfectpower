"""Alter a matrix condition and a retained area equation; require rejection."""
from pathlib import Path
import os,subprocess,tempfile
rotation=Path('receipts/belyaev_geometry/Rotation.lean').read_text()
area=Path('receipts/belyaev_geometry/TriangleAreas.lean').read_text()
variants={
 'wrong-matrix':rotation.replace('(63 : Int)*(63)+(84)*(84)','(64 : Int)*(63)+(84)*(84)'),
 'wrong-area':area.replace('theorem area_conservation : (8 : Int)+(8 : Int)+(8 : Int)=(24)',
                          'theorem area_conservation : (8 : Int)+(8 : Int)+(8 : Int)=(25)')
}
for name,source in variants.items():
    original=rotation if name=='wrong-matrix' else area
    if source==original:raise AssertionError('rejection mutation did not apply: '+name)
    with tempfile.TemporaryDirectory() as directory:
        p=Path(directory)/'Rejected.lean';p.write_text(source)
        result=subprocess.run([os.environ.get('PERFECTPOWER_LEAN','lean'),str(p)],capture_output=True,text=True)
    if result.returncode==0:raise AssertionError(name+' accepted')
    print(name+': rejected (exit '+str(result.returncode)+')\n'+result.stdout+result.stderr)
