"""Reproduce the five final constructive closures from a pinned numeric source."""
import argparse
import json
from pathlib import Path
from perfectpower.elliptic_arithmetic import EllipticCurve
from perfectpower.elliptic_certificate_verifier import verify_independence
from perfectpower.mordell_published_witnesses import (
    read_published_candidates, source_provenance, augment_published_witnesses,
    recover_cover_preimages)

ROOT = Path(__file__).resolve().parents[1]
KEYS = (5935, 7482, 7823, 8210, 9454)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--source', type=Path, required=True,
                        help='local mwMordell10000.sobj; checksum is pinned')
    args = parser.parse_args()
    blob = args.source.read_bytes()
    candidates = read_published_candidates(blob)
    rows = []
    writes = []
    # Prepare and verify every result before changing any descent packet.
    for k in KEYS:
        path = ROOT / f'receipts/mordell_two_descent/p{k}.json'
        original = json.loads(path.read_text())
        updated = augment_published_witnesses(original, candidates[k])
        if not updated['rank_determined']:
            raise ArithmeticError(f'candidate does not close coefficient {k}')
        preimages = [lift for point in candidates[k]
                     for lift in recover_cover_preimages(updated,point)]
        retained = updated.setdefault('published_cover_preimages',[])
        for lift in preimages:
            if lift not in retained:
                retained.append(lift)
        rows.append(dict(k=k, points=candidates[k],
                         witness_rank_lower=updated['witness_rank_lower_bound'],
                         existing_rank_upper=updated['rank_upper_bound'],
                         independence=updated['independence'],
                         original_cover_preimages=preimages))
        writes.append((path, updated))
    replacement = {path.name: updated for path, updated in writes}
    frontier = list((ROOT/'receipts/mordell_two_descent').glob('[mp]*.json'))
    if len(frontier) != 457:
        raise ArithmeticError('expected all 457 frontier descent packets')
    for index, path in enumerate(sorted(frontier), 1):
        packet = replacement.get(path.name) or json.loads(path.read_text())
        certificate = packet['independence']
        if (packet['curve'] != EllipticCurve([0,packet['k']]).specification
                or certificate['curve'] != packet['curve']
                or certificate['original_points'] != packet['points']
                or certificate['rank_lower_bound'] != packet['witness_rank_lower_bound']
                or packet['witness_rank_lower_bound'] != packet['rank_upper_bound']
                or not packet['rank_determined']
                or not verify_independence(certificate)):
            raise ArithmeticError(f'frontier witness audit failed at {packet["k"]}')
        if index % 100 == 0:
            print(f'{index}/457 independence packets checked', flush=True)
    for path, updated in writes:
        path.write_text(json.dumps(updated, indent=2) + '\n')
    receipt = dict(schema='pp-mordell-published-witness-closure/1',
                   baseline_commit='5735bab8f88c42080390e2ba04d6cf5c5c47392a',
                   baseline_matching_witnesses=452, baseline_witness_gaps=5,
                   **source_provenance(), source_bytes=len(blob),
                   source_curves=len(candidates),
                   all_source_points_checked=sum(map(len, candidates.values())),
                   rows=rows, curves_closed=5, final_matching_witnesses=457,
                   final_witness_gaps=0, integral_lists_promoted=0,
                   frontier_independence_checks=len(frontier),
                   complete_bases_claimed=False, new_lean_theorems=0)
    output = ROOT / 'receipts/mordell_published_witnesses.json'
    output.write_text(json.dumps(receipt, indent=2) + '\n')
    print('Five exact witness closures; 457 matching witness ranks; zero witness gaps.')


if __name__ == '__main__':
    main()
