"""Build and install a wheel into an isolated directory; replay public routes."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import shutil
import sys
import tempfile

ROOT=Path(__file__).resolve().parents[1]


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--wheel-dir',type=Path,help='retain the successfully checked wheel here')
    args=parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='pp-wheel-check-') as directory:
        base=Path(directory);wheels=base/'wheels';installed=base/'installed'
        # Setuptools writes inside its source directory even when cwd is isolated.
        # Use a fresh source copy to keep repeated and concurrent checks independent.
        source=base/'source'
        shutil.copytree(ROOT,source,ignore=shutil.ignore_patterns(
            '.git','.lake','build','dist','*.egg-info','__pycache__'))
        subprocess.run([sys.executable,'-m','pip','wheel',str(source),'--no-deps',
            '--no-build-isolation','--wheel-dir',str(wheels)],check=True,cwd=base)
        wheel=next(wheels.glob('perfectpower-*.whl'))
        subprocess.run([sys.executable,'-m','pip','install','--no-deps',
            '--target',str(installed),str(wheel)],check=True,cwd=base)
        environment=dict(os.environ,PYTHONPATH=str(installed))
        run=subprocess.run([sys.executable,str(ROOT/'scripts/check_installed_wheel.py')],
            cwd=base,env=environment,capture_output=True,text=True)
        if run.returncode:
            sys.stdout.write(run.stdout);sys.stderr.write(run.stderr)
            run.check_returncode()
        if args.wheel_dir is not None:
            args.wheel_dir.mkdir(parents=True,exist_ok=True)
            shutil.copy2(wheel,args.wheel_dir/wheel.name)
        print(json.dumps(dict(complete=True,wheel_sha256=hashlib.sha256(wheel.read_bytes()).hexdigest(),
            wheel_bytes=wheel.stat().st_size,installed_checks=json.loads(run.stdout))))


if __name__=='__main__':main()
