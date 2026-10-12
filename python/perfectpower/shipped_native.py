"""Load optional source-bound native binaries shipped with a desktop distribution."""
import hashlib,json,os,sys
from pathlib import Path
from .resources import runtime_root

def shipped_library(name,source):
    override=os.environ.get('PP_NATIVE_DIR')
    folder=Path(override) if override else runtime_root()/'desktop/explorer/native'/('windows-x64' if sys.platform=='win32' else 'linux-x64')
    binary=folder/(name+('.dll' if sys.platform=='win32' else '.so'))
    if not binary.exists():return None
    receipt=json.loads(binary.with_suffix('.json').read_text())
    if receipt.get('source_sha256')!=hashlib.sha256(Path(source).read_bytes()).hexdigest():raise ValueError('Shipped native source digest mismatch')
    if receipt.get('binary_sha256')!=hashlib.sha256(binary.read_bytes()).hexdigest():raise ValueError('Shipped native binary digest mismatch')
    return binary,receipt
