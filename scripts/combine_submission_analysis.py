#!/usr/bin/env python3
"""Audit and visualize existing aggregate evidence. No player records accepted."""
import hashlib
import json
from pathlib import Path
import numpy as np

LABELS = ('Development 2023/24', '2023 → 2024', '2025 · exploratory')
STAGES = ('development', '2023_to_2024', 'exploratory_2025')
FILES = ('compact.json', 'getoff.json', 'repeatability.json', 'official_rebuild_full.json', 'getoff_extraction.json', 'reliability_pair_review.json','loss_geometry.json','rules_review.json')


def load(receipts):
    return {n: json.loads((Path(receipts)/n).read_text()) for n in FILES}


def stages(receipt):
    return [receipt['development'], *[receipt['temporal'][s] for s in STAGES[1:]]]


def analyze(evidence):
    c, g, r = [evidence[n] for n in FILES[:3]]
    assert c['cohort']['players'] == g['cohort']['players'] == 74
    assert c['cohort']['attempts'] == 361 and c['cohort']['rushes'] == g['cohort']['rushes'] == 14665
    assert c['cohort']['by_class'] == g['cohort']['by_class'] == {'2023':23,'2024':22,'2025':29}
    for receipt in (c, g):
        assert receipt['independent_confirmation'] is False and receipt['models_promoted'] is False
    # Recalculate gains from MSE, rather than copying percentages into figures.
    pressure=[]
    for name, stage in zip(STAGES, stages(c)):
        metric=stage if name=='development' else stage['evaluation']
        base=metric['baseline_mse']
        for model, v in metric['comparisons'].items():
            assert np.isclose(v['relative_gain'], (base-v['mse'])/base, atol=1e-12, rtol=0)
        pressure.append({'stage':name,'baseline_mse':base,**{m+'_gain_percent':100*metric['comparisons'][m]['relative_gain'] for m in ('fixed','selected')}})
    decompositions=[]
    for name, stage in zip(STAGES, stages(g)):
        for metric in ('primary','auxiliary'):
            t=stage[metric];base=t['baseline_mse_seconds2']
            for model, v in t['comparisons'].items():
                assert np.isclose(v['relative_gain'],(base-v['mse_seconds2'])/base,atol=1e-12,rtol=0)
        p,a=stage['primary'],stage['auxiliary']
        within=a['baseline_mse_seconds2']-p['baseline_mse_seconds2']
        assert within>=0
        # Every context+source variant shares the same play-varying Context fit.
        # Adding one constant per player leaves centered residuals unchanged.
        for model in ('context','fixed','selected'):
            assert np.isclose(a['comparisons'][model]['mse_seconds2']-p['comparisons'][model]['mse_seconds2'],within,atol=1e-12,rtol=0)
        assert p['comparisons']['selected']['mse_seconds2']==p['baseline_mse_seconds2']
        decompositions.append({'stage':name,'primary_mse_s2':p['baseline_mse_seconds2'],'play_mse_s2':a['baseline_mse_seconds2'],'within_player_residual_variance_s2':within,'within_share_percent':100*within/a['baseline_mse_seconds2'],'oracle_maximum_play_gain_percent':100*p['baseline_mse_seconds2']/a['baseline_mse_seconds2'],'fixed_gain_primary_percent':100*p['comparisons']['fixed']['relative_gain'],'fixed_gain_auxiliary_percent':100*a['comparisons']['fixed']['relative_gain'],'absolute_gain_s2':p['baseline_mse_seconds2']-p['comparisons']['fixed']['mse_seconds2']})
    audits=[a for rep in g['repeats'] for a in rep['audits']]+[v['audit'] for v in g['temporal'].values()]
    assert len(audits)==14 and not any(a['apply_correction'] for a in audits)
    f=list(r['features'].values())
    assert [x['repeat_players'] for x in f]==[39,39,4,0]
    assert r['outcome_free'] is True and r['classes']==[2023,2024]
    return {'schema':'pp-combine-submission-analysis/1','evidence_type':'Existing aggregate receipts plus exact loss identity; no new tracking experiment','pressure':pressure,'getoff_decomposition':decompositions,'getoff_fallback_fits':len(audits),'speed_minus_recovery_rank_correlation':f[0]['split_spearman']-f[1]['split_spearman'],'paired_reliability_difference_test_available':True,'paired_reliability_difference':evidence['reliability_pair_review.json'],'independent_confirmation':False,'raw_reexecution':False}


def render(evidence, out):
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from matplotlib.ticker import PercentFormatter
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    plt.rcParams.update({'font.family':'DejaVu Sans','font.size':11,'axes.spines.top':False,'axes.spines.right':False,'axes.titleweight':'bold','svg.hashsalt':'bdb2027-submission','savefig.facecolor':'#ffffff'})
    navy,teal,orange,gray='#182F46','#007E87','#C05A12','#5D6C7C'
    paths=[]
    def save(fig,name):
        fig.savefig(out/(name+'.png'),dpi=180,bbox_inches='tight',metadata={'Software':'PerfectPower aggregate receipt renderer'})
        fig.savefig(out/(name+'.svg'),bbox_inches='tight',metadata={'Date':None})
        svg=out/(name+'.svg')
        svg.write_text('\n'.join(line.rstrip() for line in svg.read_text().splitlines())+'\n')
        plt.close(fig);paths.append(name+'.png')
    # 1: rank stability and missing support, with no invented uncertainty bars.
    fig,ax=plt.subplots(figsize=(10,4.8));features=list(evidence['repeatability.json']['features'].values())
    names=['Pass-rush speed gain','Phase recovery acceleration','Hoop redirection','Four-bag braking']
    for i,(name,f) in enumerate(zip(names,features)):
        rho=f['split_spearman'];ci=f['descriptive_player_bootstrap_95'];color=teal if i==0 else gray
        if ci:
            ax.plot(ci,[i,i],color=color,lw=3);ax.scatter([rho],[i],s=75,color=color,zorder=3)
            ax.text(.98,i,f'ρ = {rho:.2f}; n = {f["repeat_players"]}',ha='right',va='center',fontsize=10)
        elif rho is not None:
            ax.scatter([rho],[i],s=65,marker='D',color=orange);ax.text(.03,i,'n = 4 · no supported interval',va='center',color=orange)
        else:ax.text(.03,i,'n = 0 · repeatability unavailable',va='center',color=gray)
    ax.set_yticks(range(4),names);ax.set_ylim(3.5,-.5);ax.set_xlim(-.2,1.08);ax.axvline(0,color='#CBD3D9',lw=1)
    ax.set_xlabel('Alternating-attempt Spearman rank correlation');ax.set_title('1  |  Repeatable rank is a measurement gate',loc='left',pad=18)
    fig.text(.01,-.04,'2023/24 Combine attempts only. Lines: descriptive 95% player bootstrap intervals.\nPaired difference: 0.260 (descriptive 95% interval −0.105 to 0.650). No established superiority; conditions may differ.',fontsize=10,color=gray)
    save(fig,'figure_1_repeatability')
    # 2: all stages, fixed and selected; intervals explicitly conditional.
    fig,ax=plt.subplots(figsize=(10,5.2));c=evidence['compact.json']
    for i,(label,stage) in enumerate(zip(LABELS,stages(c))):
        metric=stage if i==0 else stage['evaluation'];base=metric['baseline_mse']
        for model,offset,col,mark in [('fixed',-.13,orange,'o'),('selected',.13,teal,'s')]:
            v=metric['comparisons'][model];x=100*v['relative_gain'];ci=100*np.array(v['paired_player_bootstrap_95'])/base
            ax.plot(ci,[i+offset]*2,color=col,lw=2);ax.scatter(x,i+offset,s=60,color=col,marker=mark,label=model.capitalize() if i==0 else None)
            ax.annotate(f'{x:+.2f}%',(x,i+offset),xytext=(3,-17 if model=='selected' else 8),textcoords='offset points',fontsize=9,color=col)
    ax.set_yticks(range(3),LABELS);ax.set_ylim(2.5,-.65);ax.axvline(0,color=navy,lw=1);ax.set_xlim(-27,11)
    ax.set_xlabel('Pressure-rate MSE reduction (%) · positive favors movement');ax.set_title('2  |  A bounded correction still needs NFL evidence',loc='left',pad=18)
    ax.legend(loc='upper left',frameon=False,ncol=2)
    fig.text(.01,-.04,'Lines: pointwise 95% paired-player intervals, conditional on fitted predictions.\nExact fallback has a zero interval by construction; it is not evidence of certainty about future performance.',fontsize=10,color=gray)
    save(fig,'figure_2_pressure')
    # 3: mechanism-matched test, include the wide uncertainty rather than clipping.
    fig,ax=plt.subplots(figsize=(10,5.2));g=evidence['getoff.json']
    for i,(label,stage) in enumerate(zip(LABELS,stages(g))):
        p=stage['primary'];v=p['comparisons']['fixed'];base=p['baseline_mse_seconds2'];x=100*v['relative_gain'];ci=100*np.array(v['conditional_player_95'])/base
        ax.plot(ci,[i]*2,color=orange,lw=3);ax.scatter(x,i,s=75,color=orange)
        ax.scatter(0,i+.17,s=55,color=teal,marker='s',label='Selected: exact fallback' if i==0 else None)
        ax.annotate(f'Fixed {x:+.2f}%',(x,i),xytext=(4,-19),textcoords='offset points',fontsize=10,color=orange)
    ax.set_yticks(range(3),LABELS);ax.invert_yaxis();ax.axvline(0,color=navy,lw=1)
    ax.set_xlim(-83,65);ax.set_xlabel('Player-mean get-off MSE reduction (%) · positive favors launch')
    ax.set_title('3  |  Matching launch to get-off did not rescue transfer',loc='left',pad=18);ax.legend(loc='lower left',frameon=False)
    fig.text(.01,-.04,'Fixed: two half-second source launch coordinates. Lines: conditional pointwise 95% paired-player intervals.\nAll 14 selected fits use fallback. NFL context is observed: this is not an unconditional pre-draft forecast.',fontsize=10,color=gray)
    save(fig,'figure_3_getoff')
    # 4: deterministic decomposition of existing losses, not a fitted new result.
    d=analyze(evidence)['getoff_decomposition'];fig,ax=plt.subplots(figsize=(10,5))
    primary=np.array([x['primary_mse_s2'] for x in d]);within=np.array([x['within_player_residual_variance_s2'] for x in d]);y=np.arange(3)
    ax.barh(y,within,color='#CBD8E2',label='Within-player residual variation')
    ax.barh(y,primary,left=within,color=teal,label='Squared mean player residual')
    for i,row in enumerate(d):ax.text(.002,i,f'{row["within_share_percent"]:.1f}% within player',va='center',color=navy,fontweight='bold')
    ax.set_yticks(y,LABELS);ax.invert_yaxis();ax.set_xlim(0,.063);ax.set_xlabel('Conventional + context equal-player mean play loss (s²)')
    ax.set_title('4  |  A player constant cannot change snap-to-snap variation',loc='left',pad=18)
    ax.set_ylim(2.5,-.8);ax.legend(loc='upper center',ncol=2,frameon=False,fontsize=9)
    fig.text(.01,-.04,'Exact identity: mean(error²) = mean(error)² + mean((error − mean(error))²), within each player.\nThe gray component is unchanged by a constant launch correction. It is not an irreducible noise floor.',fontsize=10,color=gray)
    save(fig,'figure_4_loss_decomposition')
    return paths


if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--receipts',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
    e=load(a.receipts);result=analyze(e);render(e,a.out)
    result['input_sha256']={n:hashlib.sha256((a.receipts/n).read_bytes()).hexdigest() for n in FILES}
    (a.out/'aggregate_analysis.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
