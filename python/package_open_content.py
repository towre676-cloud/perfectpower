"""Package every tracked path in a git tree, without an archive size cap."""
import argparse
from io import BytesIO
from pathlib import Path
import subprocess
import tarfile
import zipfile
from datetime import datetime,timezone


def package(reference,output):
    root=Path(__file__).resolve().parents[1]
    archive=subprocess.check_output(['git','archive','--format=tar',reference],cwd=root)
    output=Path(output).resolve();output.parent.mkdir(parents=True,exist_ok=True)
    with tarfile.open(fileobj=BytesIO(archive)) as source,zipfile.ZipFile(output,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as target:
        for member in source:
            if not member.isfile() and not member.issym():continue
            data=member.linkname.encode() if member.issym() else source.extractfile(member).read()
            info=zipfile.ZipInfo('perfectpower/'+member.name,date_time=datetime.fromtimestamp(member.mtime,timezone.utc).timetuple()[:6])
            info.create_system=3;info.external_attr=((0o120000 if member.issym() else 0o100000)|member.mode)<<16
            target.writestr(info,data,compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)
    print(output,output.stat().st_size,'bytes')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--reference',default='HEAD');parser.add_argument('--output',required=True)
    args=parser.parse_args();package(args.reference,args.output)
