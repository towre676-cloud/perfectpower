"""Compile the PSG audit and reject unparsed output or nonstandard axioms."""
import re
import subprocess


def main():
    run = subprocess.run(['lake', 'env', 'lean', 'audit/PSGStructural.lean'],
                         check=True, capture_output=True, text=True)
    pattern = re.compile(r"'([^']+)'\s+(?:does not depend on any axioms|"
                         r"depends on axioms:\s*\[([^\]]*)\])")
    records = list(pattern.finditer(run.stdout))
    if len(records) != 20 or len({m.group(1) for m in records}) != 20:
        raise RuntimeError('expected twenty distinct compiled PSG declarations')
    if pattern.sub('', run.stdout).strip() or run.stderr.strip():
        raise RuntimeError('unparsed Lean audit output: ' + run.stdout + run.stderr)
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    for record in records:
        axioms = {a.strip() for a in (record.group(2) or '').split(',') if a.strip()}
        if axioms - allowed:
            raise RuntimeError('nonstandard axioms: ' + repr(axioms - allowed))
    print(run.stdout, end='')
    print('PSG axiom audit passed: twenty declarations, standard axioms only')


if __name__ == '__main__':
    main()
