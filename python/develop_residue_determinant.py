"""Reproduce the bounded OpenAI-math extraction without external dependencies."""
from pathlib import Path
import json
from perfectpower.residue_determinant import (
    auxiliary_packet, determinant_packet, kernel_packet, native_auxiliary,
    native_determinant, native_kernel, verify_auxiliary, verify_determinant, verify_kernel)


def main():
    out = Path(__file__).resolve().parents[1]/'receipts'/'residue_determinant'
    out.mkdir(parents=True, exist_ok=True)
    cases = {}
    for name, points, exponents, center in [
        ('Parabola', [[0, 0], [1, 1], [2, 4], [3, 9]], [[0, 0], [1, 0], [0, 1], [2, 0]], None),
        ('CenteredParabola', [[3, -2], [4, -1], [5, 2], [6, 7]], [[0, 0], [1, 0], [0, 1], [2, 0]], [3, -2]),
        ('MordellSample', [[3, 5], [3, -5]], [[0, 0], [3, 0], [0, 2]], None),
        ('QuarticSample', [[-2, 4], [-2, -4], [-1, 1], [-1, -1], [0, 0], [1, 1], [1, -1], [2, 4]],
         [[0, 0], [4, 0], [0, 2]], None),
    ]:
        packet = auxiliary_packet(points, exponents, center=center)
        assert verify_auxiliary(packet), name
        cases[name] = packet
        (out/(name+'.lean')).write_text(native_auxiliary(packet))
    for name, a in [('IndexGap', [[1, 1, 1]]), ('ZeroRank', [[0, 0, 0]]),
                    ('FullRank', [[1, 0], [0, 1]]), ('Rectangular', [[1, 2, 3], [2, 4, 6]])]:
        packet = kernel_packet(a)
        assert verify_kernel(packet), name
        cases[name] = packet
        (out/(name+'.lean')).write_text(native_kernel(packet))
    for name, a, m in [('ModularZero', [[1, 2, 3], [2, 3, 4], [3, 4, 5]], 1009),
                       ('TwoDivisibleRows', [[1, 2, 3], [2, 4, 6], [3, 6, 9]], 101),
                       ('CompositeModulus', [[1, 2], [2, 4]], 35),
                       ('InsufficientBound', [[3, 0], [0, 1]], 3)]:
        packet = determinant_packet(a, m)
        assert verify_determinant(packet), name
        cases[name] = packet
        if packet['status'] == 'zero-certified':
            (out/(name+'.lean')).write_text(native_determinant(packet))
    (out/'corpus.json').write_text(json.dumps(cases, indent=2)+'\n')
    print(f'{len(cases)} exact bounded packets; 11 native programs emitted')


if __name__ == '__main__':
    main()
