import json
from pathlib import Path
import unittest
from perfectpower.dresden_eclipse import (station_audit,standard_table_candidates,
    overlap_schedule,schedule_count,schedule_select,node_drift,venus_table_audit,optimal_restart_order,lunar_interval_census,compare_lunar_report)
from perfectpower.semilinear_domains import contains
ROOT=Path(__file__).resolve().parents[2]

class SourceDrivenDresdenTests(unittest.TestCase):
    def setUp(self):
        self.data=json.loads((ROOT/'research/dresden/eclipse_stations.json').read_text())

    def test_complete_station_audit(self):
        a=station_audit(self.data)
        self.assertEqual(a['last_day'],11959)
        self.assertEqual(a['last_month'],405)
        self.assertEqual(a['classification_counts'],{'intended':55,'contrived':14})
        self.assertEqual(a['increment_counts'],{148:9,177:53,178:7})
        self.assertTrue(a['raw_corrections_hold'])
        self.assertEqual(a['published_increment_discrepancies'],[{'station':19,'reported':147,'derived':148}])
        self.data['stations'][12]['increment']+=1
        with self.assertRaises(ValueError): station_audit(self.data)

    def test_two_standard_hypotheses_preserved(self):
        outputs=standard_table_candidates(self.data)
        self.assertEqual([o['first_shifted_day'] for o in outputs],[7620,7797])
        for out in outputs:
            self.assertEqual(sum(r['increment'] for r in out['stations']),11960)
            self.assertEqual(len(out['stations']),69)
        self.assertNotEqual(outputs[0]['stations'][43]['corrected_day'],outputs[1]['stations'][43]['corrected_day'])

    def test_overlap_domain_exhaustive(self):
        stations=[r['month'] for r in self.data['stations'] if r['classification']=='intended']
        for steps in ([405],[358,358,358,358,223],[223,358,358,358,358]):
            packet=overlap_schedule(stations,steps)
            brute=set();base=0;i=0;limit=6000
            while base<=limit:
                brute.update(base+s for s in stations if base+s<=limit)
                base+=steps[i%len(steps)];i+=1
            self.assertEqual([n for n in range(limit+1) if contains(packet,n)],sorted(brute))
            self.assertEqual(schedule_count(packet,0,limit),len(brute))
            self.assertEqual([schedule_select(packet,r) for r in range(len(brute))],sorted(brute))

    def test_huge_overlap_population(self):
        stations=[r['month'] for r in self.data['stations'] if r['classification']=='intended']
        p=overlap_schedule(stations,[358]*4+[223])
        self.assertEqual(p['period_months'],1655)
        self.assertEqual(p['distinct_residues'],227)
        last=schedule_select(p,10**30)
        self.assertEqual(schedule_count(p,0,last),10**30+1)
        self.assertEqual(schedule_count(p,0,last-1),10**30)

    def test_mean_drift_mix_identity(self):
        from fractions import Fraction as Q
        self.assertEqual(Q(node_drift(1655,282)),4*Q(node_drift(358,61))+Q(node_drift(223,38)))
        self.assertLess(abs(Q(node_drift(1655,282))),abs(Q(node_drift(405,69))))

    def test_policy_global_bound_and_all_ties(self):
        import itertools
        from fractions import Fraction as Q
        for a,b in [(4,1),(2,2),(3,2),(0,0),(0,2)]:
            paths=set(itertools.permutations([358]*a+[223]*b));scores=[]
            for path in paths:
                drift=Q(0);maximum=Q(0)
                for action in path:
                    drift+=Q('0.0972') if action==358 else Q('-0.42356')
                    maximum=max(maximum,abs(drift))
                scores.append((maximum,path))
            p=optimal_restart_order(a,b)
            best=min(v for v,path in scores)
            self.assertEqual(Q(p['best_maximum_absolute_prefix_drift']),best)
            self.assertEqual(p['optimal_orderings'],sum(v==best for v,path in scores))
            self.assertIn((best,tuple(p['witness'])),scores)

    def test_lunar_census_against_small_pair_enumeration(self):
        days=[1,30,60,89,120,149]
        out=lunar_interval_census(days,4)
        from collections import Counter
        for row in out['rows']:
            n=row['months'];expected=Counter(days[j]-days[i] for i in range(len(days)) for j in range(i+1,len(days)) if j-i==n)
            self.assertEqual({v['days']:v['count'] for v in row['distribution']},expected)
        with self.assertRaises(ValueError):lunar_interval_census(days,4,work_limit=2)

    def test_full_external_lunar_corpus(self):
        source=json.loads((ROOT/'research/dresden/lunar_source.json').read_text())
        census=lunar_interval_census(source['days'])
        self.assertEqual(census['appearance_count'],8052)
        self.assertEqual(census['intervals_counted'],3178845)
        self.assertEqual(census['rows'][404]['distribution'],[
            {'days':11959,'count':1117,'frequency':'1117/7647'},
            {'days':11960,'count':6242,'frequency':'6242/7647'},
            {'days':11961,'count':288,'frequency':'96/2549'}])
        compared=compare_lunar_report(census,source['reported_rows'])
        self.assertEqual(compared['matching_rows'],387)
        duplicates={r['months']:r['duplicate_day_categories'] for r in compared['differences']}
        self.assertEqual(duplicates[196],[5789])
        self.assertEqual(duplicates[305],[9008])

    def test_260_source_numbers(self):
        d=json.loads((ROOT/'research/dresden/venus_numbers.json').read_text())
        a=venus_table_audit(d)
        self.assertEqual(a['entries_checked'],260)
        self.assertEqual(a['matching_entries'],259)
        self.assertEqual([(r['page'],r['row'],r['column'],r['reported_number'],r['canonical_expected_number'])
                          for r in a['mismatches']],[(48,1,'D',1,11)])
        d['records'].append(d['records'][0])
        with self.assertRaises(ValueError):venus_table_audit(d)

if __name__=='__main__':unittest.main()
