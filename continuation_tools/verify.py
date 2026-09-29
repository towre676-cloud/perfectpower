#!/usr/bin/env python3
"""Replay the continuation checks with real exit codes and strict axiom auditing."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'docs/continuation/verification'
OUT.mkdir(parents=True, exist_ok=True)
ledger = {'original_base_commit': 'ddad6befc1f16219e4860bd90273a99a25e37bd6',
          'head_commit': subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=ROOT, stdout=subprocess.PIPE,
                                        text=True).stdout.strip(),
          'scope': 'continuation targeted build; not a claim of full make verify',
          'steps': [], 'source_sha256': {}}
for p in sorted((ROOT / 'PerfectPower/Continuation').glob('*.lean')):
    ledger['source_sha256'][str(p.relative_to(ROOT))] = hashlib.sha256(p.read_bytes()).hexdigest()


def save():
    (OUT / 'results.json').write_text(json.dumps(ledger, indent=2) + '\n')


def run(label, args):
    start = time.monotonic()
    result = subprocess.run(args, cwd=ROOT, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True)
    (OUT / (label + '.log')).write_text(result.stdout)
    ledger['steps'].append({'name': label, 'command': args,
                            'exit_code': result.returncode,
                            'seconds': round(time.monotonic() - start, 3)})
    save()
    print(label, 'exit', result.returncode, flush=True)
    if result.returncode:
        print(result.stdout)
        sys.exit(result.returncode)
    return result.stdout


run('lean_build', ['lake', 'build', 'PerfectPower.Continuation.DenominatorReduction'])
audit = run('axioms', ['lake', 'env', 'lean', 'audit/continuation/Axioms.lean'])
expected = json.loads((ROOT / 'audit/continuation/declarations.json').read_text())
found = dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", audit))
# Definitions may instead be reported as depending on no axioms.
for name in re.findall(r"'([^']+)' does not depend on any axioms", audit):
    found[name] = ''
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
if set(found) != set(expected['all_audited']):
    raise RuntimeError('missing or unexpected axiom audit entries')
for name, axioms in found.items():
    used = {x.strip() for x in axioms.split(',') if x.strip()}
    if used - allowed:
        raise RuntimeError(f'{name}: unapproved axioms {used - allowed}')
ledger['audited_entries'] = len(found)
ledger['audited_theorems'] = len(expected['theorems'])
save()
lint = run('lint', ['lake', 'env', 'lean', 'audit/continuation/Lint.lean'])
match = re.search(r'Found 0 errors in (\d+) declarations', lint)
if not match or int(match.group(1)) == 0:
    raise RuntimeError('linter checked no declarations or did not pass')
ledger['lint_declarations'] = int(match.group(1))
save()
run('new_python_tests', [sys.executable, '-m', 'unittest', 'discover', '-s', 'continuation_tests', '-v'])
run('baseline_python_and_certificates', ['make', 'test', 'cert-audit'])
ledger['status'] = 'PASS'
save()
print('Continuation checks passed; full repository make verify is a separate integration gate.')
