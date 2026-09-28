"""Regenerate SOURCE_INVENTORY.json: size and SHA-256 of every tracked source file."""
import hashlib
import json
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parents[1]
files = subprocess.run(['git', 'ls-files'], cwd=root, capture_output=True, text=True,
                       check=True).stdout.split()
files = sorted(f for f in files if f != 'SOURCE_INVENTORY.json')
entries = []
for f in files:
    data = (root / f).read_bytes()
    entries.append({'path': f, 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()})
out = root / 'SOURCE_INVENTORY.json'
out.write_text(json.dumps({'release': '0.6', 'files': entries}, indent=2) + '\n')
print(out, len(entries), 'files')
