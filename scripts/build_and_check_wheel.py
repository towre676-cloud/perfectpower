"""Build and install a wheel into an isolated directory; replay public routes."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parents[1]


def main():
    with tempfile.TemporaryDirectory(prefix='pp-wheel-check-') as directory:
        base=Path(directory);wheels=base/'wheels';installed=base/'installed'
        subprocess.run([sys.executable,'-m','pip','wheel',str(ROOT),'--no-deps',
            '--no-build-isolation','--wheel-dir',str(wheels)],check=True,cwd=base)
        wheel=next(wheels.glob('perfectpower-*.whl'))
        subprocess.run([sys.executable,'-m','pip','install','--no-deps',
            '--target',str(installed),str(wheel)],check=True,cwd=base)
        environment=dict(os.environ,PYTHONPATH=str(installed))
        run=subprocess.run([sys.executable,str(ROOT/'scripts/check_installed_wheel.py')],
            cwd=base,env=environment,check=True,capture_output=True,text=True)
        print(json.dumps(dict(complete=True,wheel_sha256=hashlib.sha256(wheel.read_bytes()).hexdigest(),
            wheel_bytes=wheel.stat().st_size,installed_checks=json.loads(run.stdout))))


if __name__=='__main__':main()
