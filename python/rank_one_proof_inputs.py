"""Stable identity for a Lean source, its local imports, and pinned toolchain inputs."""
import hashlib
import re
from pathlib import Path


def proof_hash(root: Path, src: Path) -> str:
    seen = set()

    def visit(path):
        if path in seen:
            return b''
        seen.add(path)
        data = path.read_bytes()
        dependencies = b''
        for module in re.findall(rb'^import (\S+)', data, re.M):
            if module.startswith(b'PerfectPower.'):
                dependencies += visit(root / (module.decode().replace('.', '/') + '.lean'))
        return str(path.relative_to(root)).encode() + b'\0' + data + dependencies

    config = (root / 'lean-toolchain').read_bytes() + (root / 'lake-manifest.json').read_bytes()
    return hashlib.sha256(config + visit(src)).hexdigest()
