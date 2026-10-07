"""Reproduce complete smooth residue patches and their native proof sources."""
from pathlib import Path
import json
from perfectpower.bounded_residue_patch import patch_packet, verify_patch, native_patch


def main():
    out = Path(__file__).resolve().parents[1]/'receipts'/'bounded_residue_patch'
    out.mkdir(parents=True, exist_ok=True)
    mordell = [[2,0,0],[-1,3,0],[1,0,2]]
    cases = [
        ('Parabola', [[1,0,1],[-1,2,0]], [[-10,10],[0,100]],5,[1,1],None),
        ('MordellPositive',mordell,[[0,35],[-220,220]],7,[3,5],None),
        ('MordellNegative',mordell,[[0,35],[-220,220]],7,[3,2],None),
        ('MordellEmpty',mordell,[[10,20],[-20,20]],7,[3,5],None),
        ('Quartic',[[1,0,2],[-1,4,0]],[[-8,8],[-70,70]],3,[1,1],[[0,0],[4,0],[0,2]]),
        ('Cubic',[[1,0,3],[-1,2,0],[-1,0,0]],[[-20,20],[-10,10]],5,[0,1],None),
    ]
    corpus = {}
    for name, terms, bounds, p, residue, basis in cases:
        packet = patch_packet(terms,bounds,p,residue,exponents=basis)
        assert verify_patch(packet), name
        corpus[name] = packet
        (out/(name+'.lean')).write_text(native_patch(packet))
    (out/'corpus.json').write_text(json.dumps(corpus,indent=2)+'\n')
    print('6 complete bounded packets and native programs')


if __name__ == '__main__':
    main()
