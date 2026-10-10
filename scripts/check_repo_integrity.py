"""Repository integrity: Markdown links resolve and receipt file hashes match.

Checks
  1. Every relative link in tracked Markdown files points to an existing file or directory
     (external URLs, mailto and pure #anchors are skipped; a #fragment is stripped).
  2. Every tracked receipt JSON parses.
  3. Wherever a receipt records the hash of a data artefact (a file under receipts/, data/ or
     certs/), either as {"<repo path>": "<sha256>"} or as an object with a "path"/"file" key
     next to a "sha256" key, the file's SHA-256 matches. Hashes of source code, docs and Lean
     files are release-time provenance snapshots; they drift as code evolves and are only
     counted, not enforced.
Vendored upstream trees (why3_isqrt/upstream/) are skipped.
Exit status is nonzero on any failure. Run from anywhere: python scripts/check_repo_integrity.py
"""
from pathlib import Path
import hashlib, json, re, subprocess, sys

ROOT = Path(__file__).resolve().parents[1]
LINK = re.compile(r'\[[^\]]*\]\(([^)\s]+)(?:\s+"[^"]*")?\)')
HEX = re.compile(r'^[0-9a-f]{64}$')
DATA = ('receipts/', 'data/', 'certs/')


def tracked(pattern):
    out = subprocess.run(['git', 'ls-files', pattern], cwd=ROOT, capture_output=True, text=True, check=True).stdout
    return [ROOT/p for p in out.split('\n') if p]


def check_links():
    bad = []
    for md in tracked('*.md'):
        if 'why3_isqrt/upstream/' in str(md):
            continue
        text = md.read_text(errors='replace')
        text = re.sub(r'```.*?```', '', text, flags=re.S)  # ignore code blocks
        for target in LINK.findall(text):
            if re.match(r'^[a-z][a-z0-9+.-]*:', target, re.I) or target.startswith('#'):
                continue
            path = target.split('#', 1)[0]
            if not path:
                continue
            full = (ROOT/path.lstrip('/')) if path.startswith('/') else (md.parent/path)
            if not full.exists():
                bad.append(f'{md.relative_to(ROOT)}: {target}')
    return bad


_cache = {}


def sha(path):
    if path not in _cache:
        _cache[path] = hashlib.sha256(path.read_bytes()).hexdigest()
    return _cache[path]


def repo_file(name):
    if not isinstance(name, str) or not name or len(name) > 300 or name.startswith(('http', '/')):
        return None
    p = ROOT/name
    return p if p.is_file() else None


def walk(obj, found):
    if isinstance(obj, dict):
        for k, v in obj.items():
            if isinstance(v, str) and HEX.match(v):
                p = repo_file(k)
                if p:
                    found.append((k, v))
        for key in ('path', 'file'):
            if isinstance(obj.get(key), str) and isinstance(obj.get('sha256'), str) and HEX.match(obj['sha256']):
                if repo_file(obj[key]):
                    found.append((obj[key], obj['sha256']))
        for v in obj.values():
            walk(v, found)
    elif isinstance(obj, list):
        for v in obj:
            walk(v, found)


def check_receipts():
    bad, checked, drift = [], 0, 0
    for r in tracked('receipts/*.json'):
        try:
            data = json.loads(r.read_text())
        except (ValueError, UnicodeDecodeError) as e:
            bad.append(f'{r.relative_to(ROOT)}: invalid JSON ({e})')
            continue
        found = []
        walk(data, found)
        for name, digest in found:
            enforced = name.startswith(DATA)
            checked += enforced
            if sha(ROOT/name) != digest:
                if enforced:
                    bad.append(f'{r.relative_to(ROOT)}: hash of {name} does not match')
                else:
                    drift += 1
    return bad, checked, drift


def main():
    links = check_links()
    receipts, n, drift = check_receipts()
    for line in links:
        print('broken link', line)
    for line in receipts:
        print('receipt', line)
    print(f'{len(links)} broken links; {n} data-artefact hashes checked, {len(receipts)} failures; '
          f'{drift} source-provenance snapshots differ from current files (informational)')
    return 1 if links or receipts else 0


if __name__ == '__main__':
    sys.exit(main())
