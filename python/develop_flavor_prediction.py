"""Fit on training.json, freeze forecast bytes, then score separate heldout.json.

Usage: PYTHONPATH=python OPENBLAS_NUM_THREADS=1 python python/develop_flavor_prediction.py
Add --sensitivity for prior, phase, basis and quadrature comparisons.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
from fractions import Fraction
import numpy as np
from perfectpower.flavor_prediction import fit,locked_forecast,cyclotomic_golden_carrier

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'receipts/flavor_prediction'


def judge(draws, heldout):
    weights=draws['weights']; result={}; densities=[]
    for key in ('Vub','sin2beta'):
        obs=heldout[key]; delta=draws[key]-obs['mean']; sigma=obs['sigma']
        density=np.exp(-.5*(delta/sigma)**2)/(sigma*math.sqrt(2*math.pi))
        result[key]={'predictive_density':float(np.sum(weights*density)),
                     'log_predictive_density':float(np.log(np.sum(weights*density))),
                     'sampling_standard_error':float(np.sqrt(np.sum(weights**2*(density-np.sum(weights*density))**2))),
                     'observed_mean':obs['mean'],'observed_sigma':sigma}
        densities.append(density)
    joint=float(np.sum(weights*densities[0]*densities[1]))
    result['joint']={'predictive_density':joint,'log_predictive_density':float(np.log(joint)),
                     'sampling_standard_error':float(np.sqrt(np.sum(weights**2*(densities[0]*densities[1]-joint)**2))),
                     'scope':'paired latent posterior draws, independent heldout measurement errors'}
    return result


def compact_draws(draws,name,count=16384):
    # Paired resampling is for compact plot artifacts; judging uses full arrays.
    seed=int.from_bytes(hashlib.sha256(name.encode()).digest()[:4],'big')
    rng=np.random.default_rng(seed);p=draws['weights']/draws['weights'].sum()
    ix=rng.choice(len(p),size=count,p=p)
    out={k:a[ix] for k,a in draws.items() if k!='weights'};out['weights']=np.full(count,1/count)
    return out


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--sensitivity',action='store_true');parser.add_argument('--only-sensitivity',action='store_true');args=parser.parse_args()
    training=json.loads((OUT/'training.json').read_text())
    runs=[] if args.only_sensitivity else [('b5',{}),('smooth',{'model':'smooth'}),('legacy',{'model':'legacy'}),
        ('locked_golden',{'model':'locked','fixed_coefficient':(3-math.sqrt(5))/2,'fixed_phase':Fraction(11,30),'quadrature_order':5})]
    if args.sensitivity or args.only_sensitivity:
        runs += [('flat_prior',{'support_penalty':0,'denominator_penalty':0}),('strong_sparsity',{'support_penalty':1.6}),
            ('no_phi',{'omit_phi':True}),('one_axis',{'max_support':1}),
            ('enlarged_phase',{'phase_denominators':(3,4,5,12,18,30,60)}),
            ('order5',{'quadrature_order':5})]
    retained_draws={}
    for name,options in runs:
        if name in ('legacy','locked_golden'):
            c=(3-math.sqrt(5))/2 if name=='locked_golden' else 5/13
            phase=Fraction(11,30) if name=='locked_golden' else Fraction(2,5)
            forecast=locked_forecast(training,c,phase,return_samples=True)
        else:
            forecast=fit(training,return_samples=name in ('b5','smooth'),**options)
        draws=forecast.pop('_samples',None)
        raw=(json.dumps(forecast,sort_keys=True,indent=2)+'\n').encode()
        (OUT/(name+'.json')).write_bytes(raw)
        if draws is not None:
            retained_draws[name]=draws
            np.savez_compressed(OUT/(name+'_draws.npz'),**compact_draws(draws,name))
        print(name,forecast['predictions']['Vub'],forecast['predictions']['sin2beta'],flush=True)
    if not args.only_sensitivity:
        (OUT/'cyclotomic_carrier.json').write_text(json.dumps(cyclotomic_golden_carrier(),indent=2)+'\n')
    # Reading heldout measurements starts only after every requested forecast is saved.
    if not args.only_sensitivity:
        heldout=json.loads((OUT/'heldout.json').read_text());scores={}
        for name in ('b5','smooth','legacy','locked_golden'):
            scores[name]=judge(retained_draws[name],heldout)
            scores[name]['forecast_sha256']=hashlib.sha256((OUT/(name+'.json')).read_bytes()).hexdigest()
        scores['b5_over_smooth_joint_density_ratio']=scores['b5']['joint']['predictive_density']/scores['smooth']['joint']['predictive_density']
        scores['status']='retrospective heldout-observable check; selected locked candidate is not an independent discovery evidence calculation'
        (OUT/'heldout_scorecard.json').write_text(json.dumps(scores,indent=2)+'\n')
        print('joint heldout density ratio',scores['b5_over_smooth_joint_density_ratio'],flush=True)

if __name__=='__main__':main()
