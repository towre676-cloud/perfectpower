import unittest
from perfectpower.resources import runtime_root


class RuntimeResourcesTests(unittest.TestCase):
    def test_assets_required_by_public_routes_exist(self):
        root=runtime_root()
        for name in ['certs','data','PerfectPower/BoundedNative.lean',
                     'receipts/mordell_registry.json','receipts/plan_certificates.json',
                     'python/make_mordell_registry.py',
                     'web/room-of-possibilities/PerfectPower-Room-of-Possibilities.html',
                     'contracts/current_frontier.json']:
            self.assertTrue((root/name).exists(),name)


if __name__=='__main__':unittest.main()
