"""Receipt CLI and live companion contract; runnable with unittest or pytest."""
import argparse
from contextlib import redirect_stdout
import hashlib
import importlib.util
from io import StringIO
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from perfectpower.period_bridge_cli import add_commands, application, cli, read_summary, receipt


def write_summary(folder):
    folder.mkdir(parents=True, exist_ok=True)
    summary = {
        'schema': 'pp-period-bridge/1', 'title': 'Integral families',
        'description': 'Exact reductions across related integrals.',
        'highlights': [{'label': 'Terms', 'value': '240 to 2', 'detail': 'A phase filter.'}],
        'limits': ['The categorical trace 264 has not been established.'],
    }
    path = folder / 'summary.json'
    path.write_text(json.dumps(summary))
    return path, summary


class PeriodBridgeCliTests(unittest.TestCase):
    def test_cli_preserves_exact_receipt_and_details(self):
        with tempfile.TemporaryDirectory() as temporary:
            path, summary = write_summary(Path(temporary) / 'release')
            result = {'exact': {'numerator': 22537, 'denominator': 6773760}}
            (path.parent / 'results.json').write_text(json.dumps(result))
            parser = argparse.ArgumentParser()
            add_commands(parser.add_subparsers(dest='command'))
            args = parser.parse_args(['integral-families', '--receipt', str(path.parent), '--details'])
            output = StringIO()
            with redirect_stdout(output):
                self.assertTrue(cli(args))
            packet = json.loads(output.getvalue())
            self.assertEqual(packet['summary'], summary)
            self.assertEqual(packet['results'], result)
            self.assertEqual(packet['receipt_sha256'], hashlib.sha256(path.read_bytes()).hexdigest())
            args = parser.parse_args(['integral-families', '--receipt', str(path), '--explain'])
            output = StringIO()
            with redirect_stdout(output):
                self.assertTrue(cli(args))
            self.assertIn('240 to 2', output.getvalue())
            self.assertIn('has not been established', output.getvalue())

    def test_live_companion_preserves_native_upgrade_boundary(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self.assertIsNone(application(root))
            path, summary = write_summary(root / 'receipts/period_bridge')
            record = application(root)
            self.assertEqual(record['result'], summary)
            self.assertEqual(record['receipt_sha256'], hashlib.sha256(path.read_bytes()).hexdigest())
            self.assertTrue(record['native_engine_requires_upgrade'])
            self.assertIs(record['live_data_is_executable_upgrade'], False)
            self.assertEqual(record['receipt_path'], 'receipts/period_bridge/summary.json')

    def test_exporter_adds_companion_without_changing_legacy_applications(self):
        source = Path(__file__).resolve().parents[2]
        spec = importlib.util.spec_from_file_location('period_test_exporter', source / 'scripts/export_explorer_live.py')
        exporter = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(exporter)
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            for name in ('monomial', 'crt', 'digits'):
                relative = Path('examples/research_counting') / (name + '.json')
                (root / relative).parent.mkdir(parents=True, exist_ok=True)
                (root / relative).write_bytes((source / relative).read_bytes())
            for relative in ('examples/planning/petersen_50_population.json',
                             'receipts/planning/explorer/validation.json',
                             'receipts/planning/explorer/geometry.json'):
                destination = root / relative
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes((source / relative).read_bytes())
            (root / 'data').mkdir()
            _, summary = write_summary(root / 'receipts/period_bridge')
            with patch.object(exporter.subprocess, 'check_output', return_value='snapshot\n'):
                report = exporter.export(root)
            from perfectpower.explorer_live import decode
            _, payload = decode((root / 'data/explorer_live.json').read_bytes())
            self.assertEqual(report['applications'], 3)
            self.assertEqual([entry['id'] for entry in payload['applications']], ['monomial', 'crt', 'digits'])
            self.assertEqual(payload['period_bridge']['result'], summary)
            self.assertEqual(payload['period_bridge']['id'], 'integral-families')

    def test_default_receipt_resolves_from_installed_runtime_assets(self):
        from perfectpower import resources
        with tempfile.TemporaryDirectory() as temporary:
            package = Path(temporary) / 'site-packages/perfectpower'
            _, summary = write_summary(package / '_assets/receipts/period_bridge')
            with patch.object(resources, '__file__', str(package / 'resources.py')):
                packet = receipt()
            self.assertEqual(packet['summary'], summary)
            self.assertIn('_assets/receipts/period_bridge/summary.json', packet['receipt_path'])

    def test_deep_summary_is_preferred_and_links_to_explorer(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            write_summary(root / 'receipts/period_bridge')
            path, summary = write_summary(root / 'receipts/period_bridge_deep')
            summary.update(schema='pp-period-bridge-deep/1', title='Deep integral families')
            path.write_text(json.dumps(summary))
            result = application(root)
            self.assertEqual(result['result'], summary)
            self.assertEqual(result['receipt_path'], 'receipts/period_bridge_deep/summary.json')
            self.assertTrue(result['url'].endswith('/integrals/'))
            self.assertTrue(result['monograph'].endswith('PERIOD_BRIDGE_DEEP_MONOGRAPH.md'))

    def test_deep_details_digest_is_verified_and_tampering_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            path, summary = write_summary(Path(temporary))
            raw = b'{"exact": "22537/6773760"}\n'
            (path.parent / 'results.json').write_bytes(raw)
            summary.update(schema='pp-period-bridge-deep/1',
                           results_sha256=hashlib.sha256(raw).hexdigest())
            path.write_text(json.dumps(summary))
            packet = receipt(path, details=True)
            self.assertEqual(packet['results'], {'exact': '22537/6773760'})
            self.assertEqual(packet['results_sha256'], summary['results_sha256'])
            (path.parent / 'results.json').write_text('{"exact": "1/2"}')
            with self.assertRaisesRegex(ValueError, 'results_sha256'):
                receipt(path, details=True)
            # The lightweight summary route remains inspectable without loading details.
            self.assertEqual(receipt(path)['summary'], summary)

    def test_installed_runtime_prefers_deep_and_checks_declared_digest(self):
        from perfectpower import resources
        with tempfile.TemporaryDirectory() as temporary:
            package = Path(temporary) / 'site-packages/perfectpower'
            write_summary(package / '_assets/receipts/period_bridge')
            path, summary = write_summary(package / '_assets/receipts/period_bridge_deep')
            raw = b'{"deep": true}'
            (path.parent / 'results.json').write_bytes(raw)
            summary.update(schema='pp-period-bridge-deep/1',
                           results_sha256=hashlib.sha256(raw).hexdigest())
            path.write_text(json.dumps(summary))
            with patch.object(resources, '__file__', str(package / 'resources.py')):
                packet = receipt(details=True)
            self.assertEqual(packet['summary'], summary)
            self.assertEqual(packet['results'], {'deep': True})
            self.assertIn('_assets/receipts/period_bridge_deep/summary.json', packet['receipt_path'])

    def test_wrong_receipt_schema_is_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / 'summary.json'
            path.write_text(json.dumps({'schema': 'unrelated/1'}))
            with self.assertRaisesRegex(ValueError, 'pp-period-bridge/1'):
                read_summary(path)


if __name__ == '__main__':
    unittest.main()
