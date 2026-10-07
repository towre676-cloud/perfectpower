import unittest
from fractions import Fraction
from collections import Counter
from perfectpower.dresden_analysis import interval_distribution,distribution_summary,total_variation
from perfectpower.dresden import execute_request

class DresdenAnalysisTests(unittest.TestCase):
 def test_every_small_window_against_explicit_pairs(self):
  days=[0,29,59,88,118,148,177,207]
  for start in range(len(days)-1):
   for end in range(start+2,len(days)+1):
    for n in range(1,end-start):
     expected=Counter(days[j]-days[i] for i in range(start,end) for j in range(i+1,end) if j-i==n)
     self.assertEqual(interval_distribution(days,n,start,end),[{'days':d,'count':c} for d,c in sorted(expected.items())])
 def test_moments_and_discrete_quantiles(self):
  rows=[{'days':1,'count':1},{'days':3,'count':3}]
  result=distribution_summary(rows)
  self.assertEqual(result['mean'],'5/2');self.assertEqual(result['variance'],'3/4')
  self.assertEqual(result['median'],3);self.assertEqual(result['central95'],[1,3])
 def test_huge_counts_remain_exact(self):
  n=10**100;r=distribution_summary([{'days':-5,'count':n},{'days':5,'count':n}])
  self.assertEqual(r['count'],2*n);self.assertEqual(r['mean'],'0');self.assertEqual(r['variance'],'25')
 def test_total_variation_centering_and_duplicate_categories(self):
  a=[{'days':10,'count':1},{'days':10,'count':2}]
  b=[{'days':20,'count':3}]
  self.assertEqual(total_variation(a,b,10,20),'0');self.assertEqual(total_variation(a,b),'1')
  self.assertEqual(total_variation([{'days':1,'count':1},{'days':2,'count':1}],[{'days':1,'count':2}]),'1/2')
 def test_invalid_inputs_rejected(self):
  for args in [([1,1,2],1),([2,1,3],1),([1,2,3],0),([1,2,3],1,-1),([1,2,3],3)]:
   with self.assertRaises(ValueError):interval_distribution(*args)
  for rows in [[],[{'days':1,'count':0}],[{'days':True,'count':1}]]:
   with self.assertRaises((ValueError,TypeError)):distribution_summary(rows)
 def test_checkout_window_entry_point(self):
  r=execute_request({'operation':'lunar_window','months':405,'start':0,'end':4026})
  self.assertEqual(r['summary']['count'],3621)
  self.assertEqual(sum(x['count'] for x in r['distribution']),3621)
 def test_checkout_comparison_entry_point(self):
  r=execute_request({'operation':'lunar_compare','months':[405,405]})
  self.assertEqual(r['total_variation'],'0');self.assertEqual(r['offsets'],[11959,11959])

if __name__=='__main__':unittest.main()
