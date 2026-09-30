"""The OEIS atlas for the orbit of 1 + sqrt 2, and the Mordell count check.

Acquisition (needs the official export or a local copy; run by hand):

    python3 python/make_oeis_atlas.py --acquire --git /path/to/oeisdata \\
        --index /path/to/all_sequences_index.tsv

clones https://github.com/oeis/oeisdata.git if needed (shallow, blobless, sparse,
GIT_LFS_SKIP_SMUDGE=1), runs discovery on the global term index, adds the candidate entries to the
sparse checkout, and copies each original `.seq` file into `data/oeis/seq/` with a manifest
(export commit, time.txt, index provenance, SHA-256 of every file).  `--seqdir DIR` reads a
hand-supplied directory of `.seq` files through the same parser instead of `--git`.

Verification (default; run by `make verify`, no network): re-reads the committed `data/oeis/`,
re-checks every candidate against its full entry, applies the promotion rule, compares the
certified Mordell lists with A081119/A081120, and writes `receipts/oeis_sqrt2_atlas.json`.
"""
import argparse
import hashlib
import json
import shutil
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'python'))

from perfectpower.oeis_orbit import discover, run  # noqa: E402
from perfectpower.oeis_source import GitExport, SeqDir, load_global_index, seq_path  # noqa: E402

DATA = ROOT / 'data' / 'oeis'
MORDELL = ['A081119', 'A081120', 'A054504', 'A081121']


def acquire(args):
    from perfectpower.oeis_dsl import parse_setsq
    from perfectpower.oeis_orbit import ORBITS
    idx = load_global_index(args.index)
    found = {}
    for name, make in ORBITS.items():
        A, B = make(90)
        found[name] = discover(idx, A=A, B=B)
    cands = found['sqrt2']
    sets = sorted(aid for aid, (_, nm, _) in idx.items() if parse_setsq(nm))
    ids = sorted({c['oeis'] for v in found.values() for c in v} | set(sets) | set(MORDELL))
    src = GitExport(args.git) if args.git else SeqDir(args.seqdir)
    if args.git:
        src.clone()
    src.ensure(ids)
    files = {}
    for aid in ids:
        text = src.text(aid)
        if text is None:
            continue
        dest = DATA / seq_path(aid)
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(text, encoding='utf-8')
        files[aid] = hashlib.sha256(text.encode('utf-8')).hexdigest()
    index_manifest = Path(args.index).with_name('manifest.json')
    manifest = {
        **src.version(),
        'license': 'OEIS content: CC BY-SA 4.0 (The OEIS Foundation); files are unmodified copies',
        'global_index': {'file': Path(args.index).name, 'entries': len(idx),
                         **(json.loads(index_manifest.read_text()) if index_manifest.exists() else {})},
        'files': files,
    }
    (DATA / 'manifest.json').write_text(json.dumps(manifest, indent=1) + '\n')
    for name, c in found.items():
        (DATA / f'discovery_{name}.json').write_text(json.dumps(c, indent=1) + '\n')
    (DATA / 'setsq_candidates.json').write_text(json.dumps(sets, indent=1) + '\n')
    print(f"{ {k: len(v) for k, v in found.items()} } orbit candidates, {len(sets)} set definitions, "
          f'{len(files)} entries -> {DATA.relative_to(ROOT)}')


def verify():
    src = SeqDir(DATA)
    cands = json.loads((DATA / 'discovery_sqrt2.json').read_text())
    # the committed files must be the ones the manifest recorded
    man = json.loads((DATA / 'manifest.json').read_text())
    for aid, sha in man['files'].items():
        text = src.text(aid)
        assert text is not None and hashlib.sha256(text.encode('utf-8')).hexdigest() == sha, aid
    out = run(src, cands)
    path = ROOT / 'receipts' / 'oeis_sqrt2_atlas.json'
    path.write_text(json.dumps(out, indent=1, default=str) + '\n')
    tally = {}
    for r in out['atlas']:
        tally[r['outcome']] = tally.get(r['outcome'], 0) + 1
    for name, rows in out['other_orbits'].items():
        t = {}
        for r in rows:
            t[r['outcome']] = t.get(r['outcome'], 0) + 1
        print(f'{name}: {len(rows)} entries {t}')
    m = out['mordell']
    print(f"sqrt2: {len(out['atlas'])} entries {tally}; Mordell: {m['certified_checked']} certified lists "
          f"checked, {len(m['disagreements'])} disagreements, {len(m['leads'])} leads "
          f"-> {path.relative_to(ROOT)}")
    if m['disagreements']:
        raise SystemExit('certified list disagrees with a published count')


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--acquire', action='store_true')
    ap.add_argument('--git')
    ap.add_argument('--seqdir')
    ap.add_argument('--index')
    a = ap.parse_args()
    acquire(a) if a.acquire else verify()
