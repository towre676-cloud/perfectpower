"""Create plain JSON copies of losslessly compressed open-content receipts."""
import argparse
import gzip
import json
from pathlib import Path


def unpack(source,output):
    source=Path(source);output=Path(output);output.mkdir(parents=True,exist_ok=True)
    for path in sorted(source.glob('*.json.gz')):
        data=gzip.decompress(path.read_bytes());json.loads(data)
        target=output/path.name[:-3];target.write_bytes(data);print(target)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--source',default='receipts/open_content');parser.add_argument('--output',default='receipts/open_content')
    args=parser.parse_args();unpack(args.source,args.output)
