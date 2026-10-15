"""Translate a SMALL checked native trace into proof-carrying Lean nodes.
The finite source-predicate bridge is exhaustive; never use this for 50 bits.
"""
import struct
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'python'))
from perfectpower.planning_certificate import verify


def export(trace, rows, caps, target):
    n=len(rows[0]);m=len(rows)
    if n>10:raise ValueError('Exhaustive kernel fixture is restricted to at most ten variables')
    receipt=verify(trace,rows,caps)
    raw=Path(trace).read_bytes();start=16+4*m+4*n*m
    records=list(struct.iter_unpack('<8I',raw[start:]))
    lines=['import PerfectPower.PlanningCertificate',
           'namespace PerfectPower.PlanningCertificateExamples',
           'open PlanningDiagram PlanningCertificate',
           'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0',
           'def rows : List (List Nat) := '+str(rows),
           'def caps : List Nat := '+str(caps),
           f'def node0 : CheckedNode 0 := rejectNode 0',
           f'def node1 : CheckedNode 0 := acceptNode 0']
    levels=[n,n]
    for r in records:
        if r[0]!=1:continue
        _,level,lo,hi,cl,ch,_,_=r
        i=len(levels)
        gaplo=levels[lo]-level-1;gaphi=levels[hi]-level-1
        lines.append(f'def node{i} : CheckedNode {n-level} := branchNode (skipNode {gaplo} node{lo}) (skipNode {gaphi} node{hi})')
        lines.append(f'theorem count{i} : node{i}.count = {cl+(ch<<32)} := by decide')
        levels.append(level)
    root=records[-1][1]
    lines += [f'def root : CheckedNode {n} := skipNode {levels[root]} node{root}',
              f'theorem literal_count : root.count = {receipt["count"]} := by decide',
              f'theorem literal_source_check : (assignments {n}).all (fun xs => decide (eval root.diagram xs = feasible rows caps xs)) = true := by decide',
              f'theorem native_diagram_original_predicate : ∀ xs, xs.length = {n} → eval root.diagram xs = feasible rows caps xs := finite_validation_sound {n} _ _ literal_source_check',
              f'theorem native_population_original_predicate : census {n} (feasible rows caps) = {receipt["count"]} := by',
              '  rw [← small_source_bound_population root rows caps literal_source_check, literal_count]',
              'end PerfectPower.PlanningCertificateExamples']
    Path(target).write_text('\n'.join(lines)+'\n')
    return receipt


if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('trace');p.add_argument('target')
    args=p.parse_args()
    export(args.trace,[[3,4,2,5,1],[2,0,5,1,4]],[7,5],args.target)
