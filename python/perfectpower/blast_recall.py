"""Complete pair accounting against an explicitly pinned finite database."""
from fractions import Fraction
from .blast_alignment import score
from .blast_io import replay


def recall_audit(queries, subjects, hits, reference, *, thresholds=(40,100,200), scoring=(2,-3,-5,-2)):
    expected = {(q,s) for q in queries for s in subjects}
    if set(reference) != expected:
        raise ValueError('reference must cover every query/database pair exactly once')
    if any(type(n) is not int or n < 1 for n in thresholds):
        raise ValueError('positive integer score thresholds required')
    best = {}
    for hit in hits:
        f = hit.fields; pair = f['qseqid'],f['sseqid']
        if pair not in expected:
            raise ValueError('reported hit outside pinned pair universe')
        if f.get('qlen')!=len(queries[pair[0]]) or f.get('slen')!=len(subjects[pair[1]]):
            raise ValueError('recall source lengths disagree')
        replay(hit,queries[pair[0]],subjects[pair[1]])
        value = score(hit.features,scoring)
        best[pair] = max(best.get(pair,Fraction(0)),value)
    rows = []
    for q,s in sorted(expected):
        values = reference[q,s]
        if len(values) != 2 or any(type(n) is not int or n < 0 for n in values):
            raise ValueError('two nonnegative integer strand reference scores required')
        optimum = max(values)
        reported = best.get((q,s),Fraction(0))
        if reported > optimum:
            raise ValueError('BLAST traceback score exceeds exhaustive reference optimum')
        rows.append({'query':q,'subject':s,'reference_forward':values[0], 'reference_reverse':values[1],
                     'reference_score':optimum,'blast_best_score':str(reported),
                     'reported_pair':(q,s) in best, 'score_deficit':str(optimum-reported)})
    tables = []
    for threshold in thresholds:
        relevant = [r for r in rows if r['reference_score'] >= threshold]
        found = [r for r in relevant if Fraction(r['blast_best_score']) >= threshold]
        missed = [r for r in relevant if Fraction(r['blast_best_score']) < threshold]
        tables.append({'threshold':threshold,'reference_positive_pairs':len(relevant),
                       'recovered_pairs':len(found),'missed_pairs':len(missed),
                       'recall':str(Fraction(len(found),len(relevant))) if relevant else None,
                       'misses':[{'query':r['query'],'subject':r['subject']} for r in missed]})
    return {'schema':'pp-blast-whole-corpus-recall/1','query_count':len(queries),'database_records':len(subjects),
            'complete_pair_count':len(expected),'strand_score_count':2*len(expected),'pairs':rows,'thresholds':tables,
            'scoring':list(scoring),'pair_accounting_complete':True,'kernel_checked':False,
            'complete_nt_nr_search':False,'scope':'every pair in supplied pinned FASTA database; score-threshold retrieval recall, not orthology recall'}
