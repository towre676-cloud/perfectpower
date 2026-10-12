"""Read public research data by content digest, retaining an offline fallback.

Network reads never replace executable code or modify saved runs. Engine and
data identities remain separate, including when the data is newer than an APK.
"""
import hashlib
import json
import threading
import time
import urllib.request
from pathlib import Path

PUBLIC_URL = 'https://raw.githubusercontent.com/towre676-cloud/perfectpower/main/data/explorer_live.json'
MAX_BYTES = 1_000_000


def decode(raw):
    if len(raw) > MAX_BYTES:
        raise ValueError('research feed exceeds the supported size')
    envelope = json.loads(raw)
    if not isinstance(envelope, dict) or envelope.get('schema') != 'pp-explorer-live/1':
        raise ValueError('unknown live-data schema')
    if not isinstance(envelope.get('payload_json'), str):
        raise ValueError('encoded payload text required')
    encoded = envelope['payload_json'].encode('utf8')
    if hashlib.sha256(encoded).hexdigest() != envelope['payload_sha256']:
        raise ValueError('live-data content digest mismatch')
    payload = json.loads(encoded)
    if not isinstance(payload, dict) or not isinstance(payload.get('applications'), list):
        raise ValueError('application records required')
    return envelope, payload


class LiveResearch:
    def __init__(self, root, state, ttl=300):
        self.root, self.cache = Path(root), Path(state) / 'live-research.json'
        self.ttl, self.lock, self.checked = ttl, threading.Lock(), 0
        self.last = None

    def get(self, refresh=False):
        with self.lock:
            if self.last is not None and not refresh and time.monotonic() - self.checked < self.ttl:
                return dict(self.last)
            origin, error, raw = 'live', None, None
            try:
                req = urllib.request.Request(PUBLIC_URL, headers={'User-Agent': 'PerfectPower-Explorer', 'Cache-Control': 'no-cache'})
                with urllib.request.urlopen(req, timeout=8) as response:
                    raw = response.read(MAX_BYTES + 1)
                decode(raw)
                self.cache.parent.mkdir(parents=True, exist_ok=True)
                tmp = self.cache.with_suffix('.tmp')
                tmp.write_bytes(raw)
                tmp.replace(self.cache)
            except Exception as exc:
                error = str(exc)
                raw = None
                for path, label in ((self.cache, 'cached'), (self.root / 'data/explorer_live.json', 'bundled')):
                    try:
                        candidate = path.read_bytes()
                        decode(candidate)
                        raw, origin = candidate, label
                        break
                    except (OSError, ValueError, KeyError, TypeError):
                        pass
            if raw is None:
                result = {'status': 'unavailable', 'error': error, 'applications': []}
            else:
                envelope, payload = decode(raw)
                result = dict(payload, status=origin, source_parent=envelope.get('source_parent'),
                              payload_sha256=envelope['payload_sha256'], error=error)
            self.checked, self.last = time.monotonic(), result
            return dict(result)
