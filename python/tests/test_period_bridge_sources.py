"""Integrity of the historical source snapshot and implementation source links."""
import json
from pathlib import Path
import re
import unittest
from urllib.parse import urldefrag, urlparse

REPO = Path(__file__).resolve().parents[2]


class PeriodBridgeSourceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.registry = json.loads((REPO / 'data/period_bridge_sources.json').read_text())

    def test_historical_counts_have_replayable_units(self):
        historical = self.registry['historical_collection']
        self.assertEqual(historical['status'], 'HISTORICAL_ACQUISITION_SNAPSHOT_NOT_NEW_EXECUTION')
        counts = historical['counts']
        urls = historical['source_urls']
        self.assertEqual(len(urls), len(set(urls)))
        self.assertEqual(counts['unique_source_urls'], len(urls))
        self.assertEqual(len(urls), 118)
        self.assertTrue(all(urldefrag(url)[0] == url for url in urls))
        formulas = historical['formula_provenance']
        self.assertEqual(counts['transcribed_formulas'], len(formulas))
        self.assertEqual(len(formulas), 73)
        self.assertEqual(len({entry['id'] for entry in formulas}), len(formulas))
        self.assertTrue(all(urldefrag(entry['source_url'])[0] in urls for entry in formulas))
        docs = historical['archive_documents']
        self.assertEqual(len({doc['url'] for doc in docs}), len(docs))
        self.assertEqual(sum(doc['attributed_entries'] for doc in docs), counts['archive_attributed_entries'])
        self.assertEqual(sum(doc['integral_bearing_entries'] for doc in docs), counts['archive_integral_entries'])
        self.assertEqual(counts['archive_attributed_entries'], 644)
        self.assertEqual(counts['archive_integral_entries'], 308)
        self.assertTrue(all(0 <= doc['integral_bearing_entries'] <= doc['attributed_entries'] for doc in docs))
        self.assertEqual(counts['catalog_entries'], 428)

    def test_primary_source_ids_modules_and_urls(self):
        records = self.registry['source_records']
        ids = {record['id'] for record in records}
        self.assertEqual(len(ids), len(records))
        urls = [record['url'] for record in records]
        self.assertEqual(len(urls), len(set(urls)))
        for url in urls + self.registry['historical_collection']['source_urls']:
            self.assertEqual(urlparse(url).scheme, 'https')
            self.assertTrue(urlparse(url).netloc)
            self.assertFalse(any(c.isspace() for c in url))
        for module, references in self.registry['module_sources'].items():
            self.assertTrue((REPO / module).is_file(), module)
            self.assertTrue(references)
            self.assertTrue(set(references) <= ids)
        self.assertEqual({record['url'] for record in records if record['id'].startswith('cody-artifact-')}, {
            'https://claude.ai/public/artifacts/1db99748-b7fd-477b-8a9c-1bb54fb33a19',
            'https://claude.ai/public/artifacts/4fd0f32a-22b6-4fae-b2d2-1f3732d324af'})

    def test_attribution_limits_and_snapshot_fingerprints(self):
        limits = self.registry['attribution_limits']
        self.assertEqual(limits['verified_original_facebook_posts'], 0)
        self.assertEqual(self.registry['historical_collection']['counts']['original_facebook_posts'], 0)
        self.assertEqual(limits['sazzie_lyon']['identity_status'], 'UNRESOLVED')
        self.assertEqual(limits['sazzie_lyon']['confirmed_integral_records'], 0)
        for snapshot in self.registry['historical_collection']['acquisition_snapshots']:
            self.assertRegex(snapshot['sha256'], re.compile(r'^[0-9a-f]{64}$'))
            self.assertGreater(snapshot['bytes'], 0)
            self.assertNotIn('/', snapshot['filename'])
        credits = self.registry['cheong_publisher_credits']
        self.assertEqual({entry['problem_id'] for entry in credits}, {'2892', '2893'})
        self.assertTrue(all('Henry Yang' in entry['summary'] for entry in credits))


if __name__ == '__main__':
    unittest.main()
