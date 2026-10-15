"""Opportunity-aware source metrics and equally tuned nonlinear controls."""
import numpy as np
import pandas as pd
from sklearn.ensemble import HistGradientBoostingRegressor,ExtraTreesRegressor
from sklearn.linear_model import Ridge
from .scouting_metrics import Design,RAW_COMBINE,name_key,chronological_splits

SEED=84593
BANK=([('ridge',a) for a in (10.,100.,1000.,10000.)]
      +[('role_ridge',a) for a in (100.,1000.)]
      +[('boost',d,l) for d in (2,3) for l in (1.,10.)]
      +[('trees',10)])
GROUPS={'CB':'DB','FS':'DB','SS':'DB','S':'DB','DB':'DB','C':'OL','G':'OL','OG':'OL','OT':'OL','T':'OL','OL':'OL','DE':'DL','DT':'DL','EDGE':'DL','DL':'DL','ILB':'LB','OLB':'LB','LB':'LB'}
RAW_USAGE=['rushes','targets','receptions','touches','opportunities','rush_yards','receiving_yards','first_downs','touchdowns','fd_or_td','explosive_plays','rz_rushes','rz_targets','rz_touches','rz_touchdowns','so_rushes','so_targets','so_touches','so_touchdowns','third_down_opportunities','third_down_conversions','team_targets','team_first_downs','team_touches','games']
RAW_TACKLES=['tackles','assists','scrimmage_tackle_points','tackle_points','games','team_tackle_points','team_scrimmage_tackle_points']


def resolve_college_ids(rows,rosters):
    """Exact birth date + normalized name bridge across ESPN ID namespaces.

    Only roster seasons in the three years before the draft may contribute.
    Two candidate IDs are ambiguous and never resolved using outcomes.
    """
    source=rosters.copy();source['_dob']=source.date_of_birth.astype(str).str[:10]
    source['_name']=source.athlete_display_name.fillna(source.full_name).map(name_key)
    source=source[source['_dob'].str.match(r'^\d{4}-\d{2}-\d{2}$') & source['_name'].ne('none')]
    by_birth={dob:g for dob,g in source.groupby('_dob')};out=rows.copy();out['nfl_espn_id']=out.espn_id
    audit={'new_namespace_links':0,'same_namespace_birth_verified':0,'ambiguous_birth_name_links':0,'no_birth_name_bridge':0}
    for index,row in out.iterrows():
        group=by_birth.get(str(row.birth_date)[:10])
        match=group[group['_name'].isin(row['_join_names']) & group.season.between(row.draft_year-3,row.draft_year-1)] if group is not None else None
        ids=set(match.athlete_id.dropna()) if match is not None else set()
        if len(ids)==1:
            identity=next(iter(ids));key='same_namespace_birth_verified' if identity==row.espn_id else 'new_namespace_links';audit[key]+=1;out.at[index,'espn_id']=identity
        elif len(ids)>1:audit['ambiguous_birth_name_links']+=1
        else:audit['no_birth_name_bridge']+=1
    return out,audit


def aggregate_usage(frame,kind):
    """Sum transfers, retaining source-only counts; do not invent snap counts."""
    x=frame.copy();x['athlete_id']=pd.to_numeric(x.player_id,errors='coerce');x=x[x.athlete_id.gt(0)].copy()
    team='pos_team_id' if kind=='offense' else 'def_pos_team_id'
    if x.duplicated(['season','athlete_id',team]).any():raise ValueError('duplicate usage identity')
    cols=RAW_USAGE if kind=='offense' else RAW_TACKLES
    for c in cols:x[c]=pd.to_numeric(x[c],errors='coerce')
    g=x.groupby(['season','athlete_id']);out=g[cols].sum(min_count=1)
    names=g.player_name.agg(lambda a:tuple(sorted(set(a.dropna().map(name_key)))))
    out['_source_names']=names
    n=out.opportunities if kind=='offense' else out.team_scrimmage_tackle_points
    metric={}
    def ratio(a,b):return a/b.where(b>0)
    if kind=='offense':
        # Fixed, source-independent prior strength; priors use this college
        # season's counts only and never NFL outcomes or later college seasons.
        for key,den in [('catch',out.targets),('conversion',n),('explosive',n),('third_down',out.third_down_opportunities)]:
            num={'catch':out.receptions,'conversion':out.fd_or_td,'explosive':out.explosive_plays,'third_down':out.third_down_conversions}[key]
            prior=float(num.sum()/den.sum()) if den.sum()>0 else .5
            metric[key+'_shrunk']=((num+20*prior)/(den+20)).where(den>0)
            metric[key+'_variance']=((num+20*prior)*(den-num+20*(1-prior))/((den+20)**2*(den+21))).where(den>0)
        for key,num,den in [('yards_per_target',out.receiving_yards,out.targets),('yards_per_opportunity',out.receiving_yards+out.rush_yards,n),('target_share',out.targets,out.team_targets),('touch_share',out.touches,out.team_touches),('first_down_share',out.first_downs,out.team_first_downs),('opportunities_per_active_game',n,out.games),('third_down_share',out.third_down_opportunities,n)]:metric[key]=ratio(num,den)
    else:metric['tackle_share']=ratio(out.scrimmage_tackle_points,n)
    out=out.rename(columns={c:'depth_raw__'+kind+'_'+c for c in cols})
    for c,v in metric.items():out['depth_metric__'+kind+'_'+c]=v
    return out.reset_index().replace([np.inf,-np.inf],np.nan)


def attach_usage(rows,history,kind):
    out=rows.copy();features=[c for c in history if c.startswith(('depth_raw__','depth_metric__'))]
    audits={}
    for lag in (1,2,3):
        h=history.copy();h['draft_year']=h.season+lag;h=h.drop(columns='season').rename(columns={'athlete_id':'espn_id','_source_names':'_depth_names',**{c:c+f'__lag{lag}' for c in features}})
        out=out.merge(h,on=['draft_year','espn_id'],how='left',validate='many_to_one')
        valid=np.array([isinstance(src,tuple) and isinstance(names,tuple) and bool(set(src)&set(names)) for src,names in zip(out._depth_names,out._join_names)])
        out.loc[~valid,[c+f'__lag{lag}' for c in features]]=np.nan;out=out.drop(columns='_depth_names');audits[str(lag)]=int(valid.sum())
    return out,audits


def roles(rows):return rows.pos.map(GROUPS).fillna(rows.pos).astype(str)


def fit_predict(train,test,cols,spec):
    if set(train.pfr_id)&set(test.pfr_id):raise ValueError('player leakage')
    if train.draft_year.max()>test.draft_year.min()-2:raise ValueError('outcome maturity leakage')
    design=Design(train,cols);x=design.transform(train);z=design.transform(test)
    if spec[0]=='role_ridge':
        group=roles(train);testgroup=roles(test)
        x=np.c_[x,*[x*group.eq(g).to_numpy()[:,None] for g in sorted(group.unique())]]
        z=np.c_[z,*[z*testgroup.eq(g).to_numpy()[:,None] for g in sorted(group.unique())]]
    if spec[0] in ('ridge','role_ridge'):model=Ridge(alpha=spec[1])
    elif spec[0]=='boost':model=HistGradientBoostingRegressor(max_depth=spec[1],l2_regularization=spec[2],max_iter=150,learning_rate=.05,min_samples_leaf=30,early_stopping=False,random_state=SEED)
    elif spec[0]=='trees':model=ExtraTreesRegressor(n_estimators=200,min_samples_leaf=spec[1],max_features=.7,random_state=SEED,n_jobs=1)
    else:raise ValueError('unknown model')
    return np.maximum(model.fit(x,train.target).predict(z),0.)


def tune(train,test,cols):
    folds=chronological_splits(train)
    if not folds:raise ValueError('insufficient matured tuning data')
    predictions=[np.concatenate([fit_predict(train.iloc[i],train.iloc[j],cols,spec) for i,j in folds]) for spec in BANK]
    y=np.concatenate([train.iloc[j].target.to_numpy() for i,j in folds]);loss=np.array([(y-p)**2 for p in predictions]);best=int(np.argmin(loss.mean(axis=1)))
    return fit_predict(train,test,cols,BANK[best]),{'selected':BANK[best],'inner_mse':loss.mean(axis=1).tolist()},loss[best]


def specs(rows):
    historical=RAW_COMBINE+sorted(c for c in rows if c.startswith('college_raw__'))
    raw=historical+sorted(c for c in rows if c.startswith('depth_raw__'))
    custom=raw+sorted(c for c in rows if c.startswith(('depth_metric__','metric__')))
    return {'combine':RAW_COMBINE,'historical':historical,'raw':raw,'custom':custom,'draft_raw':raw+['log_pick'],'draft_custom':custom+['log_pick']}
