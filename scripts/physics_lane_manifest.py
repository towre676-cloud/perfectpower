"""List the files of the flavor/cosmology physics lane (for a future repository split).

python scripts/physics_lane_manifest.py            prints counts per pattern
python scripts/physics_lane_manifest.py --files    prints every tracked file in the lane
Nothing is moved or deleted; the manifest only records what a split would carry.
"""
import subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PATTERNS = ['python/perfectpower/wall_*', 'python/perfectpower/flavor*', 'python/perfectpower/dimensionful_walls.py',
            'python/develop_wall_*', 'python/develop_flavor*', 'python/develop_valentiner*', 'python/tests/test_wall_*',
            'python/tests/test_flavor*', 'python/tests/test_valentiner*', 'receipts/flavor_cosmology/*',
            'receipts/m22_interactions/*', 'docs/WALL_*', 'docs/VALENTINER*', 'docs/FLAVOR*', 'docs/PHYSICS_LANE.md',
            'scripts/*wall*', 'scripts/*flavor*']


def files(pattern):
    out = subprocess.run(['git', 'ls-files', pattern], cwd=ROOT, capture_output=True, text=True, check=True).stdout
    return [f for f in out.split('\n') if f]


if __name__ == '__main__':
    seen = set()
    for p in PATTERNS:
        fs = files(p)
        seen.update(fs)
        if '--files' not in sys.argv:
            print(f'{len(fs):5d}  {p}')
    if '--files' in sys.argv:
        print('\n'.join(sorted(seen)))
    else:
        print(f'{len(seen):5d}  total tracked files in the physics lane')
