"""Run the installed Lean/Lake, optionally adapting its own executable lookup.

Ordinary installations: python scripts/lean_runtime.py -- build MODULE
Affected Linux hosts: python scripts/lean_runtime.py --proc-self -- build MODULE
Requires an existing toolchain and caches; does not download or replace either.
"""
import argparse
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--proc-self',action='store_true')
    parser.add_argument('--tool',choices=('lake','lean'),default='lake')
    parser.add_argument('arguments',nargs=argparse.REMAINDER)
    args=parser.parse_args()
    binary=shutil.which(args.tool)
    if binary is None:parser.error('install the pinned toolchain and put '+args.tool+' on PATH')
    arguments=args.arguments[1:] if args.arguments[:1]==['--'] else args.arguments
    with tempfile.TemporaryDirectory(prefix='perfectpower-lean-runtime-') as directory:
        environment=os.environ.copy()
        if args.proc_self:
            if sys.platform!='linux':parser.error('--proc-self requires Linux')
            compiler=shutil.which('cc') or shutil.which('gcc')
            if compiler is None:parser.error('--proc-self requires a C compiler')
            helper=str(Path(directory)/'proc_self.so')
            subprocess.run([compiler,'-shared','-fPIC',str(Path(__file__).with_name('lean_proc_self.c')),
                            '-ldl','-o',helper],check=True)
            environment['LD_PRELOAD']=helper+(':'+environment['LD_PRELOAD'] if environment.get('LD_PRELOAD') else '')
        return subprocess.run([binary,*arguments],env=environment).returncode


if __name__=='__main__':sys.exit(main())
