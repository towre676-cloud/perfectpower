"""Replay one SMT-LIB source through the bounded incremental transport engine."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'python'))
import z3
from perfectpower.industrial_replay import solve_replay

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('source', type=Path)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--timeout-ms', type=int, default=250)
    p.add_argument('--batch-chars', type=int, default=262144)
    p.add_argument('--command-control', action='store_true')
    p.add_argument('--fast-split', action='store_true')
    args = p.parse_args()
    raw = args.source.read_bytes()
    result = solve_replay(raw.decode(), args.timeout_ms, 0 if args.command_control else args.batch_chars,
                          fast_split=args.fast_split)
    result.update(source_sha256=hashlib.sha256(raw).hexdigest(), z3=z3.get_version_string())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    raise SystemExit(1 if result['errors'] else 0)
