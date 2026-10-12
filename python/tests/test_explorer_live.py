import hashlib
import json
from unittest.mock import patch
import pytest
from perfectpower.explorer_live import decode, LiveResearch


def envelope():
    body = json.dumps({'applications': [{'id': 'test'}]})
    return json.dumps({'schema': 'pp-explorer-live/1', 'payload_json': body,
                       'payload_sha256': hashlib.sha256(body.encode()).hexdigest(), 'source_parent': 'test-parent'}).encode()


def test_payload_tampering_rejected():
    raw = json.loads(envelope())
    raw['payload_json'] = raw['payload_json'].replace('test', 'changed')
    with pytest.raises(ValueError): decode(json.dumps(raw).encode())


def test_live_cache_offline_and_invalid_cache_fallback(tmp_path):
    (tmp_path / 'data').mkdir()
    (tmp_path / 'data/explorer_live.json').write_bytes(envelope())
    reader = LiveResearch(tmp_path, tmp_path / 'state')
    with patch('urllib.request.urlopen', side_effect=OSError('offline')):
        assert reader.get()['status'] == 'bundled'
        reader.cache.parent.mkdir(exist_ok=True)
        reader.cache.write_bytes(envelope())
        assert reader.get(refresh=True)['status'] == 'cached'
        reader.cache.write_text('{}')
        assert reader.get(refresh=True)['status'] == 'bundled'
    assert not list(tmp_path.glob('*.py'))


def test_live_fetch_persists_validated_payload_and_uses_ttl(tmp_path):
    from io import BytesIO
    reader = LiveResearch(tmp_path, tmp_path / 'state')
    with patch('urllib.request.urlopen', return_value=BytesIO(envelope())) as fetch:
        assert reader.get()['status'] == 'live'
        assert reader.get()['applications'][0]['id'] == 'test'
        assert fetch.call_count == 1
    assert reader.cache.read_bytes() == envelope()
