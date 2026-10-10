import copy
import os
import random
import json
import tempfile
from pathlib import Path
from types import SimpleNamespace
import unittest
from unittest.mock import patch
from perfectpower.checked_soe import compile_soe, accept_soe
from perfectpower.future_states import future_quotient
from perfectpower.divisor_square import WorkLimit
from perfectpower.checked_family import check_rebuilt

MODELS = [
    {'observations':[0,0,1],'actions':{'advance':[1,2,0],'stop':[None,1,2]}},
    {'observations':[0,0,0,1],'actions':{'a':[0,1,3,3],'b':[0,3,2,3]}},
    {'observations':[{'label':'λ'}, {'label':'λ'}, True, 1],
     'actions':{'disabled':[None,None,2,3],'cycle':[1,0,3,2],'reset':[0,0,0,0]}},
    {'observations':[None],'actions':{'idle':[None]}},
]

class CheckedSOETests(unittest.TestCase):
    def test_source_and_pair_specific_encodings(self):
        c=compile_soe(MODELS[1]);self.assertIn('Fin 4',c['lean'])
        self.assertIn('[0]',c['lean']);self.assertIn('[1]',c['lean'])
        c=compile_soe(MODELS[2]);self.assertEqual(len(c['observation_encoding']),3)
        self.assertEqual(len(c['packet']['blocks']),3)
        changed=copy.deepcopy(MODELS[0]);changed['actions']['advance'][0]=0
        self.assertNotEqual(compile_soe(changed)['specification_sha256'],compile_soe(MODELS[0])['specification_sha256'])

    def test_packet_rejections(self):
        model=MODELS[1];p=future_quotient(model)
        mutations=[]
        for edit in (
            lambda p:p['quotient']['actions']['a'].__setitem__(2,2),
            lambda p:p['projection'].__setitem__(1,0),
            lambda p:p['distinguishing_witnesses'][0].__setitem__('word',[]),
            lambda p:p.__setitem__('schema','bad'),
            lambda p:p.__setitem__('distinguishing_witnesses',[]),
            lambda p:p['projection'].__setitem__(0,False),
            lambda p:p.__setitem__('quotient',None),
            lambda p:p.__setitem__('extra',1),
            lambda p:p.__setitem__('refinement_rounds',True),
            lambda p:p.__setitem__('scope',[]),
        ):
            bad=copy.deepcopy(p);edit(bad);mutations.append(bad)
        disabled=copy.deepcopy(future_quotient(MODELS[0]));disabled['quotient']['actions']['stop'][0]=0
        for bad in mutations:self.assertFalse(accept_soe(model,bad)['accepted'])
        self.assertFalse(accept_soe(MODELS[0],disabled)['accepted'])
        changed=copy.deepcopy(model);changed['actions']['a'][0]=3
        self.assertFalse(accept_soe(changed,p)['accepted'])
        # A merged distinguishable pair with matching current observation fails transport.
        merged=copy.deepcopy(p);merged['blocks']=[[0,1],[2],[3]];merged['projection']=[0,0,1,2]
        self.assertFalse(accept_soe(model,merged)['accepted'])

    def test_limits_and_failed_kernel_never_accept(self):
        with self.assertRaises(WorkLimit):compile_soe({'observations':[0]*129,'actions':{'a':[0]*129}})
        with self.assertRaises(WorkLimit):compile_soe({'observations':['x'*2200000],'actions':{'a':[0]}})
        with patch('perfectpower.checked_soe.check_rebuilt',return_value={'accepted':False,'reason':'timeout'}):
            self.assertFalse(accept_soe(MODELS[0])['accepted'])

    def test_public_interface_requires_acceptance(self):
        from perfectpower.soe_console import cli
        with tempfile.TemporaryDirectory() as tmp:
            src=Path(tmp)/'model.json';out=Path(tmp)/'result.json'
            src.write_text(json.dumps(MODELS[1]))
            args=SimpleNamespace(command='soe-states',specification=src,out=out,kernel_check=True)
            with patch('perfectpower.checked_soe.accept_soe',return_value={'accepted':False,'reason':'kernel rejected'}):
                with self.assertRaises(ValueError):cli(args)
                self.assertFalse(out.exists())
            with patch('perfectpower.checked_soe.accept_soe',return_value={'accepted':True,'proof_status':'kernel_checked'}):
                self.assertTrue(cli(args));self.assertEqual(json.loads(out.read_text())['proof_status'],'kernel_checked')

    @unittest.skipUnless(os.environ.get('PERFECTPOWER_LEAN') and os.environ.get('LEAN_PATH'),'configured pinned Lean required')
    def test_kernel_larger_models_and_random(self):
        rng=random.Random(20261010)
        models=MODELS+[{'observations':[rng.randrange(3) for _ in range(n)],
                       'actions':{a:[rng.choice([None,*range(n)]) for _ in range(n)] for a in ('x','y','z')}}
                      for n in (3,4,5) for _ in range(2)]
        for model in models:
            with self.subTest(model=model):
                r=accept_soe(model);self.assertTrue(r['accepted'],r)

    @unittest.skipUnless(os.environ.get('PERFECTPOWER_LEAN') and os.environ.get('LEAN_PATH'),'configured pinned Lean required')
    def test_kernel_rejects_literal_corruptions_without_python_replay(self):
        # Bypass preflight intentionally: test that the generated proof obligations reject.
        c=compile_soe(MODELS[0]);original=c['lean']
        mutations=[
            original.replace('some 1','some 0',1),
            original.replace('none','some 0',1),
            original.replace('def q (s : Fin 3) : Fin 3 := if s = 0 then 0 else (if s = 1 then 1 else (2))',
                             'def q (s : Fin 3) : Fin 3 := 0'),
            original[:original.index('def experiment')]+original[original.index('def experiment'):].replace('[0]','[]').replace('[1]','[]'),
        ]
        for text in mutations:
            self.assertNotEqual(text,original)
            bad=dict(c,lean=text)
            result=check_rebuilt(bad,['SOESemantics'],['SOESemantics.quotient_complete'])
            self.assertFalse(result['accepted'],result)

if __name__=='__main__':unittest.main()
