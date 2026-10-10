"""Rebuild the complete BLAST atlas from retained versioned source inputs."""
from pathlib import Path
import json
from hashlib import sha256
from perfectpower.blast_alignment import AlignmentFamily, exact_alignment, weights
from perfectpower.blast_parameters import normal_regions, plane_atlas, line_atlas, robustness, integer_grid
from perfectpower.blast_io import fasta, tabular, replay, provenance
from perfectpower.blast_chains import chain_population
from perfectpower.blast_machinery import semiring_alignment, partition_statistics, sensitivity_jet, fixed_alignment_null, alignment_machine, motif_machine, soe_packet, motif_count_machine, similarity_geometry, feature_diagnostic
from perfectpower.blast_explore import query_family, identity_correlation, graph_filtration
from perfectpower.blast_report import json_ready, write_report

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'receipts/blast'


def dump(name, value):
    path=OUT/name
    path.write_text(json.dumps(json_ready(value),sort_keys=True,indent=2,allow_nan=False)+'\n')
    return path


def develop():
    OUT.mkdir(parents=True,exist_ok=True)
    family=AlignmentFamily('ACGTACGT','CGTACGTA')
    plane=plane_atlas(family.terms,(2,0,0,-1),[(0,-1,0,0),(0,0,-1,0)],[(0,8),(0,12)])
    model,labels=alignment_machine('AC','AG')
    soe=soe_packet(model,compile_lean=True)
    generated=ROOT/'PerfectPower/Generated/BlastAlignmentSOE.lean'
    generated.write_text(soe['lean_compilation']['lean'])
    # Compilation is deterministic. Kernel acceptance is recorded separately,
    # never inferred from a saved source string or a Python replay.
    compilation=soe.pop('lean_compilation')
    soe['generated_lean_path']=str(generated.relative_to(ROOT))
    soe['source_sha256']=compilation['source_sha256']
    soe['state_labels']=[list(s) for s in labels]
    kernel_path=OUT/'kernel_build.json'
    kernel=json.loads(kernel_path.read_text()) if kernel_path.exists() else {}
    accepted={r['module']:r for r in kernel.get('modules',[]) if r.get('accepted')}
    row=accepted.get(str(generated.relative_to(ROOT)),{})
    soe['kernel_checked']=row.get('source_sha256')==sha256(generated.read_bytes()).hexdigest()

    namespace='PerfectPower.CheckedSOE.P'+compilation['specification_sha256']
    remaining=[len(family.query[:2])+len(family.subject[:2])-i-j for i,j,previous in labels]
    # This model is for AC/AG, hence remaining rank is exactly 4-i-j.
    expression=str(remaining[-1])
    for i in reversed(range(len(remaining)-1)):
        expression=f'if s = {i} then {remaining[i]} else ({expression})'
    count_source=f"""import PerfectPower.Generated.BlastAlignmentSOE
import PerfectPower.BlastAlignment
namespace PerfectPower.Generated.BlastPathCounts
open {namespace}
def remaining (s : Fin {len(labels)}) : Nat := {expression}
theorem decreases : ∀ s a t, step s a = some t → remaining t < remaining s := by decide
theorem terminal_disabled : ∀ s a, obs s = 1 → step s a = none := by decide
def countFuel : Nat → Fin {len(labels)} → Nat
  | 0, s => if obs s = 1 then 1 else 0
  | n+1, s => if obs s = 1 then 1 else
      ((List.finRange 6).map (fun a => match step s a with
        | none => 0
        | some t => countFuel n t)).sum
theorem count_at_root : countFuel 4 0 = 3 := by decide
theorem every_word_bounded (s t : Fin {len(labels)}) (word : List (Fin 6))
    (h : PerfectPower.SOESemantics.run step s word = some t) : word.length ≤ remaining s := by
  exact PerfectPower.BlastAlignment.path_length_bound step remaining decreases s t word h
#print axioms decreases
#print axioms terminal_disabled
#print axioms count_at_root
#print axioms every_word_bounded
end PerfectPower.Generated.BlastPathCounts
"""
    (ROOT/'PerfectPower/Generated/BlastPathCounts.lean').write_text(count_source)

    motif_model,prefixes=motif_machine(['AC','CG','ACG'])
    motif_soe=soe_packet(motif_model,compile_lean=True)
    (ROOT/'PerfectPower/Generated/BlastMotifSOE.lean').write_text(motif_soe['lean_compilation']['lean'])
    motif_soe.pop('lean_compilation');motif_soe['prefixes']=prefixes
    motif_source=ROOT/'PerfectPower/Generated/BlastMotifSOE.lean'
    motif_row=accepted.get(str(motif_source.relative_to(ROOT)),{})
    motif_soe['kernel_checked']=motif_row.get('source_sha256')==sha256(motif_source.read_bytes()).hexdigest()
    dump('motif_soe.json',motif_soe)
    dump('semiring_alignment.json',semiring_alignment('AC','AG'))
    dump('normal_regions.json',normal_regions(family.terms))
    from perfectpower.blast_motif_alignment import MotifAlignmentFamily
    constrained=MotifAlignmentFamily(family.query,family.subject,['CGT'])
    dump('conserved_motif_family.json',constrained.packet())
    graph_edges=[(0,1,'9/10',1),(1,2,'4/5',1),(0,2,'3/4',-1),(2,3,'2/3',1)]
    geometry=similarity_geometry(4,graph_edges)
    qpath=ROOT/'examples/blast/NM_000207.3.fasta';spath=ROOT/'examples/blast/XM_043971863.1.fasta'
    q=fasta(qpath.read_text());s=fasta(spath.read_text());qa,sa=next(iter(q)),next(iter(s))
    alignment=exact_alignment(q[qa],s[sa]);dump('insulin_exact_local.json',alignment)
    # An explicitly anchored short real window is small enough for the complete
    # generating polynomial. It is not a complete family for the full transcripts.
    qi,si=alignment['query_interval'][0],alignment['subject_interval'][0]
    real_family=AlignmentFamily(q[qa][qi:qi+10],s[sa][si:si+10])
    dump('insulin_window_family.json',{'family':real_family.packet(),
        'query_accession':qa,'subject_accession':sa,'query_interval':[qi,qi+10],
        'subject_interval':[si,si+10],'optimum':real_family.optimal(weights())})
    dump('insulin_polynomial_correlation.json',identity_correlation(q[qa],s[sa]))
    dump('motif_count_machine.json',motif_count_machine(['AC','CG','ACG']))
    dump('integer_score_grid.json',integer_grid(family.terms,[(2,2),(-4,-1),(-6,0),(-1,-1)],
        residue_filters=[(2,2,[0])],limit=100000))
    receipt={'schema':'pp-blast-atlas-demo/1','example_label':'illustrative shifted DNA words',
        'family':family.packet(),'representatives':{','.join(map(str,f)):family.select(f) for f in family.terms},
        'plane':plane,'line':line_atlas(family.terms,(2,-3,0,-1),(0,0,-1,0),(0,30)),
        'robustness':robustness(family.terms,weights()),'optimal':family.optimal(weights()),
        'partition_statistics':partition_statistics(family),'sensitivity_jet':sensitivity_jet(family,(1,1,1,1),(1,0,0,0)),
        'feature_query':query_family(family,min_matches=7,max_gap_openings=2),
        'fixed_comparison_null':fixed_alignment_null(8,7),'soe':soe,'geometry':geometry,
        'graph_filtration':graph_filtration(4,graph_edges),
        'diagnostic':feature_diagnostic({'ungapped':[0,8,0,0],'shifted':[7,0,2,2]}),
        'real':{'query_accession':qa,'subject_accession':sa,'alignment':alignment,
                'query_source':'https://www.ncbi.nlm.nih.gov/nuccore/'+qa,
                'subject_source':'https://www.ncbi.nlm.nih.gov/nuccore/'+sa,
                'query_file_sha256':sha256(qpath.read_bytes()).hexdigest(),
                'subject_file_sha256':sha256(spath.read_bytes()).hexdigest()},
        'scopes':['The complete polynomial covers the two displayed illustrative words under global alignment, literal character equality, affine gaps, and no immediately opposing gaps.',
                  'The real transcript example searches every cell of the supplied sequence pair under an explicit local affine model. It returns one optimum and does not supply a calibrated BLAST E-value.',
                  'The Hodge and strand-transport example is a supplied illustrative graph. Its topology is not a biological conclusion.',
                  'SOE source generation invokes the existing generic compiler. Actual Lean acceptance is recorded in kernel_build.json; polynomial population generation remains tested Python.']}
    blast_path=ROOT/'examples/blast/insulin_blast.tsv'
    if blast_path.exists():
        hits=tabular(blast_path.read_text())
        replays=[replay(h,q[h.fields['qseqid']],s[h.fields['sseqid']]) for h in hits]
        dump('insulin_blast_ingestion.json',{**provenance(hits,'NCBI BLAST+ retained pair search'), 'replays':replays})
        chains=chain_population(hits,weights(),min_coverage=50)
        dump('insulin_blast_chains.json',chains)
        receipt['real']['blast_hsp_count']=len(hits)
        receipt['real']['compatible_chain_count']=chains['count']
    dump('atlas.json',receipt)
    write_report(receipt,ROOT/'web/blast-atlas/index.html')
    # Kernel-check literal scores only on the retained support; do not pretend
    # that this proves the Python generator has retained every possible path.
    feature='\n  '+',\n  '.join('⟨'+', '.join(map(str,f))+'⟩' for f in sorted(family.terms))
    lean='''import PerfectPower.BlastAlignment
namespace PerfectPower.Generated.BlastScores
open PerfectPower.BlastAlignment
def candidates : List Features := ['''+feature+''']
def baseline : Weights := ⟨2, -3, -5, -1⟩
theorem retained_best : ∀ f ∈ candidates, score f baseline ≤ score ⟨7, 0, 2, 2⟩ baseline := by
  norm_num [candidates, score, baseline]
theorem retained_tie : score ⟨0, 8, 0, 0⟩ ⟨2, 0, -6, -1⟩ = score ⟨7, 0, 2, 2⟩ ⟨2, 0, -6, -1⟩ := by
  norm_num [score]
#print axioms retained_best
#print axioms retained_tie
end PerfectPower.Generated.BlastScores
'''
    (ROOT/'PerfectPower/Generated/BlastScores.lean').write_text(lean)
    print(json.dumps({'paths':family.count,'summaries':len(family.terms),'plane_regions':len(plane['regions']),
        'real_local_score':alignment['score'],'real_window_paths':real_family.count,'soe_states':soe['state_count'],
        'soe_classes':soe['class_count']}))


if __name__=='__main__':develop()
