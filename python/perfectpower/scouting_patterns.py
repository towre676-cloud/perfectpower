"""Descriptive forecast stratification with explicit exposure and multiplicity.

This module does not train, select or deploy a subgroup prediction model.
"""
import itertools
import numpy as np
import pandas as pd
EXPERTS=('combine','historical','raw','custom')

def validate(frame):
    if frame.pfr_id.duplicated().any():raise ValueError('repeat player in prediction population')
    if not np.isfinite(frame[['target','aggregate',*EXPERTS]].to_numpy(float)).all():raise ValueError('nonfinite predictions')

def loss_summary(frame):
    y=frame['target'].to_numpy(float);b=frame['combine'].to_numpy(float);a=frame['aggregate'].to_numpy(float)
    base=(y-b)**2;delta=base-(y-a)**2
    byclass={str(k):float((((g.target-g['combine'])**2)-((g.target-g['aggregate'])**2)).mean()) for k,g in frame.groupby('draft_year')}
    return {'players':len(frame),'classes':len(byclass),'baseline_mse':float(base.mean()),'candidate_mse':float(((y-a)**2).mean()),
      'absolute_gain':float(delta.mean()),'relative_gain':float(delta.sum()/base.sum()) if base.sum()>0 else None,
      'total_loss_reduction':float(delta.sum()),'player_win_fraction':float((delta>0).mean()),'median_player_gain':float(np.median(delta)),
      'baseline_mean_signed_error':float((b-y).mean()),'candidate_mean_signed_error':float((a-y).mean()),
      'class_absolute_gains':byclass,'positive_classes':sum(v>0 for v in byclass.values()),
      'all_observed_classes_positive':bool(len(byclass)>=2 and all(v>0 for v in byclass.values()))}

def group_masks(frame,task):
    groups={'all':(np.ones(len(frame),bool),False)}
    predictors=['draft_year','pos','role','identity_status','recruit_context','college_seasons','combine_missing','disagreement_band','correction_direction','prediction_band']
    for col in predictors:
        for key in sorted(frame[col].dropna().unique(),key=str):groups[col+'='+str(key)]=(frame[col].eq(key).to_numpy(),False)
    for (year,pos),g in frame.groupby(['draft_year','pos']):groups[f'class_position={year}:{pos}']=(frame.index.isin(g.index),False)
    if task=='pressure_target':
        for cols in [('correction_direction','disagreement_band'),('pos','correction_direction')]:
            for key,g in frame.groupby(list(cols)):
                groups['interaction='+':'.join(cols)+'='+':'.join(map(str,key))]=(frame.index.isin(g.index),False)
    for col in ('outcome_band','exposure_band'):
        for key in sorted(frame[col].dropna().unique(),key=str):groups[col+'='+str(key)]=(frame[col].eq(key).to_numpy(),True)
    return groups

def simultaneous_intervals(frame,groups,draws=4000,seed=42871):
    """Conditional within-class bootstrap with overlapping group max statistic.

    Each resample retains the original cohort sizes. Counts within a subgroup
    fluctuate. Sparse/empty replicates make an interval unavailable, not zero.
    """
    delta=((frame.target-frame['combine'])**2-(frame.target-frame['aggregate'])**2).to_numpy()
    keys=[k for k,(m,_) in groups.items() if m.sum()>=10 and frame.loc[m,'draft_year'].nunique()>=2]
    if not keys:return {},None
    masks=np.column_stack([groups[k][0] for k in keys]).astype(float);rng=np.random.default_rng(seed)
    # Multinomial counts give exactly the ordinary paired player bootstrap
    # distribution while retaining dependence across overlapping group queries.
    counts=np.zeros((draws,len(frame)))
    for _,g in frame.groupby('draft_year'):
        ix=frame.index.get_indexer(g.index);counts[:,ix]=rng.multinomial(len(ix),np.full(len(ix),1/len(ix)),size=draws)
    den=counts@masks
    with np.errstate(divide='ignore',invalid='ignore'):samples=(counts@(delta[:,None]*masks))/den
    valid=np.isfinite(samples).all(axis=0);keys=[k for k,v in zip(keys,valid) if v];samples=samples[:,valid];masks=masks[:,valid]
    if not keys:return {},None
    means=(delta[:,None]*masks).sum(axis=0)/masks.sum(axis=0);se=samples.std(axis=0,ddof=1)
    active=se>1e-14;maximum=np.zeros(draws)
    if active.any():maximum=np.max(np.abs((samples[:,active]-means[active])/se[active]),axis=1)
    critical=float(np.quantile(maximum,.95));result={}
    for j,key in enumerate(keys):result[key]={'pointwise_player_95':np.quantile(samples[:,j],[.025,.975]).tolist(),
      'simultaneous_player_95':(means[j]+np.array([-1,1])*critical*se[j]).tolist(),'bootstrap_se':float(se[j])}
    return result,{'draws':draws,'seed':seed,'eligible_groups':len(keys),'max_standardized_95':critical,
      'scope':'Conditional fixed-prediction within-class player bootstrap; excludes refitting, adaptive research, linkage uncertainty and between-class sampling. No new-cohort guarantee.'}

def mechanisms(frame):
    y=frame.target.to_numpy();experts=frame[list(EXPERTS)].to_numpy();b=frame['combine'].to_numpy();a=frame['aggregate'].to_numpy();correction=b-a
    equal=experts.mean(axis=1);mean_loss=np.mean((experts-y[:,None])**2);diversity=np.mean(np.var(experts,axis=1));equal_loss=np.mean((equal-y)**2)
    alignment=float(np.mean(2*(b-y)*correction));penalty=float(np.mean(correction**2));actual=float(np.mean((b-y)**2-(a-y)**2))
    errors=experts-y[:,None];std=errors.std(axis=0);corr=np.full((4,4),np.nan)
    for i in range(4):
        for j in range(4):
            if std[i]>0 and std[j]>0:corr[i,j]=np.mean((errors[:,i]-errors[:,i].mean())*(errors[:,j]-errors[:,j].mean()))/(std[i]*std[j])
    ablations={}
    for omit in EXPERTS:
        q=frame.copy();q['aggregate']=frame[[e for e in EXPERTS if e!=omit]].mean(axis=1);ablations[omit]=loss_summary(q)
    return {'average_expert_mse':float(mean_loss),'equal_average_mse':float(equal_loss),'between_expert_prediction_variance':float(diversity),
      'diversity_identity_error':float(mean_loss-equal_loss-diversity),'baseline_correction_alignment':alignment,'correction_square_penalty':penalty,
      'correction_identity_error':float(actual-alignment+penalty),'expert_error_correlations':{'order':EXPERTS,'matrix':corr.tolist()},
      'leave_one_expert_out_equal_average_diagnostics':ablations}

def influence(frame):
    q=frame.copy();q['gain']=(q.target-q['combine'])**2-(q.target-q['aggregate'])**2
    full=loss_summary(q);ordered=q.sort_values(['gain','pfr_id'],ascending=[False,True]);positive=ordered[ordered.gain.gt(0)]
    deletions={}
    for k in (1,3,5,10):
        if len(q)-k<10 or len(positive)<k:continue
        remaining=q.drop(index=positive.index[:k]);deletions[str(k)]=loss_summary(remaining)
    out={'full':full,'remove_largest_positive_gain_players':deletions,'leave_one_class_out':{str(y):loss_summary(q[q.draft_year.ne(y)]) for y in sorted(q.draft_year.unique()) if q.draft_year.ne(y).any()},
      'largest_five_positive_gains_sum':float(positive.gain.head(5).sum()),'total_gain_sum':float(q.gain.sum())}
    gains=np.array(list(full['class_absolute_gains'].values()))
    if len(gains)<=16:
        signed=np.array([np.mean(gains*np.array(s)) for s in itertools.product((-1,1),repeat=len(gains))])
        out['class_sign_flip_sensitivity']={'classes':len(gains),'sign_patterns':len(signed),'fraction_at_least_observed_equal_class_gain':float(np.mean(signed>=gains.mean()-1e-14)),
         'interpretation':'Enumeration under a hypothetical symmetric independent class-sign null; not an assumption-free or multiplicity-corrected p-value.'}
    return out,ordered

def exposure_metrics(frame):
    q=frame[frame.exposure.notna()&frame.exposure.gt(0)].copy()
    if q.empty:return {'players':0}
    w=q.exposure.to_numpy();base=(q.target-q['combine']).to_numpy()**2;candidate=(q.target-q['aggregate']).to_numpy()**2
    return {'players':len(q),'sum_exposure':float(w.sum()),'exposure_weighted_baseline_mse':float(np.average(base,weights=w)),
      'exposure_weighted_candidate_mse':float(np.average(candidate,weights=w)),
      'exposure_weighted_relative_gain':float(1-np.sum(w*candidate)/np.sum(w*base)) if np.sum(w*base)>0 else None,
      'scope':'Outcome-observed exposure changes the evaluation estimand; unavailable for pre-draft routing and not an intrinsic-ability adjustment.'}


def common_support_contrast(frame,indicator,min_cell=5):
    """Class/role standardized descriptive contrasts; never a causal effect."""
    q=frame.copy();q['_gain']=(q.target-q['combine'])**2-(q.target-q['aggregate'])**2
    cells=[]
    for (year,role),g in q.groupby(['draft_year','role']):
        a=g[g[indicator].eq(True)];b=g[g[indicator].eq(False)]
        if min(len(a),len(b))<min_cell:continue
        cells.append({'class':int(year),'role':str(role),'positive_group_players':len(a),'negative_group_players':len(b),'weight':len(g),
                      'positive_mean_gain':float(a['_gain'].mean()),'negative_mean_gain':float(b['_gain'].mean())})
    weight=sum(c['weight'] for c in cells)
    return {'indicator':indicator,'minimum_each_group_per_cell':min_cell,'common_support_cells':cells,'covered_players':weight,'population':len(q),
      'standardized_positive_minus_negative_gain':sum(c['weight']*(c['positive_mean_gain']-c['negative_mean_gain']) for c in cells)/weight if weight else None,
      'scope':'Observational comparison standardized over common class/role cells only; unmeasured source, school and selection confounding remain. Excluded cells cannot be generalized.'}

def matured_role_mean(training,query,strength=20.):
    """Simple negative control: role mean shrunk to prior matured pool only."""
    if training.pfr_id.duplicated().any() or query.pfr_id.duplicated().any():raise ValueError('repeat player')
    if strength<=0:raise ValueError('positive prior strength required')
    values=[];audit=[]
    for year,g in query.groupby('draft_year',sort=True):
        tr=training[training.draft_year.le(year-2)&training.label.notna()]
        if tr.empty:raise ValueError('no matured role-control training data')
        if set(tr.pfr_id)&set(g.pfr_id):raise ValueError('player overlap')
        prior=float(tr.label.mean());counts=tr.groupby('role').label.agg(['sum','count'])
        for index,row in g.iterrows():
            c=counts.loc[row.role] if row.role in counts.index else None
            mean=(float(c['sum'])+strength*prior)/(int(c['count'])+strength) if c is not None else prior
            values.append((index,mean))
        audit.append({'class':int(year),'latest_training_class':int(tr.draft_year.max()),'training_players':len(tr),'prior_mean':prior,'strength':strength,'role_counts':counts['count'].to_dict()})
    return pd.Series(dict(values)).reindex(query.index),audit
