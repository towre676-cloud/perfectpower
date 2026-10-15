"""Source-defined scouting metrics, exact-ID joins and chronological ridge models.

These are operational measurements and retrospective estimators, not certified
latent athletic abilities. NFL outcomes never enter feature construction.
"""
from pathlib import Path
import re,unicodedata
import numpy as np
import pandas as pd
from sklearn.linear_model import Ridge
from .movement_residual import Numeric

RAW_COMBINE=['height_inches','wt','forty','bench','vertical','broad_jump','cone','shuttle','age_at_draft']
BOX_SPECS={
 'pass_yards':('passing','passingYards'),'pass_tds':('passing','passingTouchdowns'),'pass_ints':('passing','interceptions'),
 'rush_attempts':('rushing','rushingAttempts'),'rush_yards':('rushing','rushingYards'),'rush_tds':('rushing','rushingTouchdowns'),
 'receptions':('receiving','receptions'),'rec_yards':('receiving','receivingYards'),'rec_tds':('receiving','receivingTouchdowns'),
 'tackles':('defensive','totalTackles'),'sacks':('defensive','sacks'),'tfl':('defensive','tacklesForLoss'),'passes_defended':('defensive','passesDefended'),
 'fumbles':('fumbles','fumbles'),'fumbles_lost':('fumbles','fumblesLost')}
FRONT={'DE','DT','OLB','ILB','LB','EDGE','DL'}
ALPHAS=(1.,10.,100.,1000.,10000.)


def name_key(value):
    text=''.join(c for c in unicodedata.normalize('NFKD',str(value).lower()) if not unicodedata.combining(c))
    text=re.sub(r'\b(jr|sr|ii|iii|iv)\b','',text)
    return re.sub('[^a-z]','',text)


def exact_unique(frame,keys,label):
    frame=frame.dropna(subset=keys).copy()
    if frame.duplicated(keys).any():raise ValueError('ambiguous '+label+' identity')
    return frame


def physics_features(rows):
    """Fixed transforms of recorded tests; no fitted ranks or NFL response."""
    h=rows.height_inches*.0254;m=rows.wt*.45359237;t=rows.forty;v=36.576/t
    jump=rows.vertical*.0254;broad=rows.broad_jump*.0254
    out=pd.DataFrame(index=rows.index)
    out['metric__body_mass_index']=m/(h*h)
    out['metric__mean_dash_speed_mps']=v
    out['metric__constant_acceleration_proxy']=2*36.576/(t*t)
    out['metric__vertical_takeoff_proxy']=np.sqrt(2*9.80665*jump)
    out['metric__vertical_momentum_proxy']=m*np.sqrt(2*9.80665*jump)
    out['metric__vertical_energy_proxy']=m*9.80665*jump
    out['metric__relative_broad_jump']=broad/h
    out['metric__jump_shape_ratio']=jump/broad
    out['metric__shuttle_dash_ratio']=rows.shuttle/t
    out['metric__cone_dash_ratio']=rows.cone/t
    out['metric__bench_reps_per_kg']=rows.bench/m
    out['metric__mass_speed_index']=m/(t**4)
    return out.replace([np.inf,-np.inf],np.nan)


def college_box_features(frame):
    """Observed-category game means and captured-teammate production shares.

    Empty or absent categories stay missing. In particular older missing defense
    rows must never become zero performance. Synthetic negative team IDs excluded.
    """
    x=frame[frame.athlete_id.gt(0)].copy();keys=['season','athlete_id','team_id','game_id']
    if x.duplicated(keys+['category']).any():raise ValueError('duplicate college box category')
    z=x[keys].copy()
    for name,(category,field) in BOX_SPECS.items():
        z[name]=pd.to_numeric(x.get(field,pd.Series(np.nan,index=x.index)),errors='coerce').where(x.category.eq(category))
    pg=z.groupby(keys,sort=True).sum(min_count=1).reset_index();cols=list(BOX_SPECS)
    team=pg.groupby(['season','team_id','game_id'])[cols].transform('sum')
    for c in cols:pg['share_'+c]=(pg[c]/team[c]).where(team[c]>0)
    g=pg.groupby(['season','athlete_id'],sort=True);out=g[cols].mean().add_prefix('college_raw__')
    for c in cols:
        out['college_raw__'+c+'_games']=g[c].count()
        out['metric__college_share_'+c]=g['share_'+c].mean()
    out['college_raw__observed_games']=g.game_id.nunique()
    out['_source_name']=x.groupby(['season','athlete_id']).athlete_name.first().map(name_key) if 'athlete_name' in x else ''
    return out.reset_index()


def college_event_features(frame):
    """Shrink source play-success/explosive rates and adjust for other games
    against the same opponent. Credit-event availability is retained as support.
    No claim that these participant files contain all on-field opportunities.
    """
    rows=[]
    for kind,prefix,yards in [('rush','rush','rush_yds'),('receiving','reception','reception_yds'),('passing','completion','completion_yds')]:
        x=frame[['season','game_id','opponent','down','distance',prefix+'_player_id',yards]].copy()
        x=x.rename(columns={prefix+'_player_id':'athlete_id',yards:'yards'})
        x=x[x.athlete_id.notna() & x.yards.notna() & x.down.between(1,4) & x.distance.gt(0)].copy()
        if x.empty:continue
        x['success']=(x.yards>=x.distance*np.where(x.down.eq(1),.5,np.where(x.down.eq(2),.7,1))).astype(float)
        x['explosive']=(x.yards>=(10 if kind=='rush' else 15)).astype(float)
        # Passing observations here are COMPLETIONS only, so success is explicitly
        # conditional on a credited completion; never label it dropback success.
        league=float(x.success.mean());opp=x.groupby('opponent').success.transform('sum');oppn=x.groupby('opponent').success.transform('count')
        game=x.groupby(['opponent','game_id']).success.transform('sum');gamen=x.groupby(['opponent','game_id']).success.transform('count')
        x['excess']=x.success-np.where(oppn-gamen>=20,(opp-game)/(oppn-gamen).clip(lower=1),league)
        x['late_success']=x.success.where(x.down.ge(3))
        g=x.groupby(['season','athlete_id']);n=g.success.count();s=g.success.sum();p=(s+20*league)/(n+20)
        out=pd.DataFrame({'college_raw__'+kind+'_credited_events':n,'metric__'+kind+'_success_shrunk':p,'metric__'+kind+'_success_variance':(s+20*league)*(n-s+20*(1-league))/((n+20)**2*(n+21)),'metric__'+kind+'_opponent_excess':g.excess.mean(),'metric__'+kind+'_explosive_share':g.explosive.mean(),'metric__'+kind+'_late_down_success':g.late_success.mean()}).reset_index();rows.append(out)
    if not rows:return pd.DataFrame(columns=['season','athlete_id'])
    out=rows[0]
    for r in rows[1:]:out=out.merge(r,on=['season','athlete_id'],how='outer',validate='one_to_one')
    return out


def attach_college(rows,history):
    """Only explicit seasons before prospect draft; no carry-forward NFL fields."""
    out=rows.copy();features=[c for c in history if c not in ['season','athlete_id','_source_name']]
    for lag in (1,2,3):
        h=history.rename(columns={c:f'{c}__lag{lag}' for c in features}).copy();h['draft_year']=h.season+lag;h=h.drop(columns='season').rename(columns={'athlete_id':'espn_id','_source_name':f'_college_source_name__lag{lag}'})
        out=out.merge(h,on=['draft_year','espn_id'],how='left',validate='many_to_one')
        if '_join_names' in out and f'_college_source_name__lag{lag}' in out:
            valid=np.array([isinstance(names,tuple) and isinstance(source,str) and source in names for names,source in zip(out._join_names,out[f'_college_source_name__lag{lag}'])])
            out.loc[~valid,[f'{c}__lag{lag}' for c in features]]=np.nan
            out[f'_college_name_verified__lag{lag}']=valid
    # Changes of per-observed-game source production; missing endpoints stay missing.
    for c in ['college_raw__rec_yards','college_raw__rush_yards','college_raw__sacks','college_raw__tfl','college_raw__pass_yards']:
        if c+'__lag1' in out:out['metric__trend_'+c]=out[c+'__lag1']-out[c+'__lag2']
    return out


def season_coverage(snaps):
    coverage={}
    for season,g in snaps.groupby('season'):
        reg=g[g.game_type.eq('REG')];expected=271 if season==2022 else (272 if season>=2021 else 256)
        ok=reg.game_id.nunique()==expected and reg.team.nunique()==32
        if reg.duplicated(['game_id','pfr_player_id','team']).any():raise ValueError('duplicate NFL player game rows')
        games=reg.groupby('game_id').team.nunique()
        ok=ok and games.eq(2).all()
        coverage[str(int(season))]={'rows':len(reg),'games':reg.game_id.nunique(),'expected_completed_games':expected,'teams':reg.team.nunique(),'complete':bool(ok)}
    return coverage


def build_population(cache):
    cache=Path(cache);combine=pd.read_csv(cache/'combine.csv');draft=pd.read_csv(cache/'draft_picks.csv');players=pd.read_csv(cache/'players.csv',low_memory=False)
    source=combine.drop(columns=['draft_year','draft_team','draft_round','draft_ovr'],errors='ignore')
    c=exact_unique(source[source.season.between(2013,2024)],['season','pfr_id'],'Combine');d=exact_unique(draft,['season','pfr_player_id'],'draft')
    unit=c.merge(d[['season','pfr_player_id','pick']],left_on=['season','pfr_id'],right_on=['season','pfr_player_id'],how='inner',validate='one_to_one')
    unit=unit[~unit.pos.isin(['P','K','LS'])].rename(columns={'season':'draft_year'}).reset_index(drop=True)
    cross=exact_unique(players,['pfr_id'],'PFR crosswalk')[['pfr_id','espn_id','birth_date','display_name']]
    unit=unit.merge(cross,on='pfr_id',how='left',validate='one_to_one')
    if unit.pfr_id.duplicated().any():raise ValueError('repeat prospect across draft classes')
    unit['espn_id']=pd.to_numeric(unit.espn_id,errors='coerce')
    ambiguous_espn=players.loc[players.espn_id.notna() & players.duplicated('espn_id',keep=False),'espn_id']
    unit.loc[unit.espn_id.isin(ambiguous_espn),'espn_id']=np.nan
    unit['_join_names']=[tuple(sorted({name_key(a),name_key(b)})) for a,b in zip(unit.player_name,unit.display_name)]
    height=unit.ht.astype(str).str.extract(r'^(\d+)-(\d+)$');unit['height_inches']=pd.to_numeric(height[0],errors='coerce')*12+pd.to_numeric(height[1],errors='coerce')
    birth=pd.to_datetime(unit.birth_date,errors='coerce');unit['age_at_draft']=(pd.to_datetime(unit.draft_year.astype(str)+'-04-25')-birth).dt.days/365.2425
    unit=pd.concat([unit,physics_features(unit)],axis=1)
    histories=[];source_audit=[]
    for year in range(2014,2026):
        box=pd.read_parquet(cache/f'player_box_{year}.parquet');events=pd.read_parquet(cache/f'player_stats_{year}.parquet')
        if events.duplicated(['game_id','play_id']).any():raise ValueError('duplicate college event')
        b=college_box_features(box);e=college_event_features(events);histories.append(b.merge(e,on=['season','athlete_id'],how='outer',validate='one_to_one'))
        source_audit.append({'season':year,'box_games':box.game_id.nunique(),'box_players':box.athlete_id[box.athlete_id.gt(0)].nunique(),'defensive_box_rows':int(box.category.eq('defensive').sum()),'event_games':events.game_id.nunique(),'event_rows':len(events),'warning':'Box and event-game coverage differs; older defensive coverage sparse. Missing categories remain unknown.'})
    history=pd.concat(histories,ignore_index=True);unit=attach_college(unit,history)
    snaps=pd.concat([pd.read_csv(cache/f'snap_counts_{y}.csv') for y in range(2013,2026)],ignore_index=True);coverage=season_coverage(snaps)
    if not all(v['complete'] for v in coverage.values()):raise ValueError('incomplete NFL snap outcome seasons')
    nfl=snaps[snaps.game_type.eq('REG')].groupby(['season','pfr_player_id'])[['offense_snaps','defense_snaps']].sum()
    adv=pd.read_csv(cache/'advstats_season_def.csv');adv=adv[adv.season.between(2013,2025)].dropna(subset=['pfr_id']).copy()
    ambiguous=adv.duplicated(['season','pfr_id'],keep=False)
    ambiguous_groups=int(adv.loc[ambiguous,['season','pfr_id']].drop_duplicates().shape[0])
    # Multi-team and collision rows have no guaranteed total-row contract here.
    # Reject ambiguous season identities; never guess/sum pressure numerators.
    adv=adv.loc[~ambiguous].copy()
    adv=adv.set_index(['season','pfr_id'])
    targets=[];pressures=[];total_snaps=[]
    for row in unit.itertuples():
        scrim=0.;defense=0.;pressure=0.;known=True
        for year in (row.draft_year,row.draft_year+1):
            if str(year) not in coverage or not coverage[str(year)]['complete']:raise ValueError('censored NFL target')
            key=(year,row.pfr_id)
            counts=nfl.loc[key] if key in nfl.index else pd.Series({'offense_snaps':0.,'defense_snaps':0.})
            scrim+=counts.offense_snaps+counts.defense_snaps;defense+=counts.defense_snaps
            if counts.defense_snaps>0:
                if key not in adv.index or pd.isna(adv.loc[key,'prss']):known=False
                else:pressure+=adv.loc[key,'prss']
        targets.append(np.log1p(scrim));total_snaps.append(scrim)
        pressures.append(100*pressure/defense if known and defense>0 and row.pos in FRONT else np.nan)
    unit['target']=targets;unit['two_season_snaps']=total_snaps;unit['pressure_target']=pressures
    rawcollege=[c for c in unit if c.startswith('college_raw__')]
    audit={'source_combine_records':len(combine),'source_combine_years':[int(combine.season.min()),int(combine.season.max())],'population':len(unit),'population_by_class':{str(k):int(v) for k,v in unit.groupby('draft_year').size().items()},'population_by_position':unit.pos.value_counts().to_dict(),'college_source':source_audit,'nfl_snap_coverage':coverage,'zero_scrimmage_outcomes':int(unit.two_season_snaps.eq(0).sum()),'exact_espn_crosswalk':int(unit.espn_id.notna().sum()),'any_college_feature':int(unit[rawcollege].notna().any(axis=1).sum()),'secondary_pressure_players':int(unit.pressure_target.notna().sum()),'primary_scope':'Drafted, exactly ID-matched Combine invitees; two-season opportunity, not pure talent. Undrafted/unmatched invitees not silently labeled failures.','raw_row_publish':False}
    audit['rejected_advanced_player_season_groups']=ambiguous_groups
    audit['college_name_verified_any_lag']=int(unit[[f'_college_name_verified__lag{k}' for k in (1,2,3)]].any(axis=1).sum())
    audit['identity_scope']='College links require exact ESPN ID plus normalized exact Combine or NFL display name; punctuation/accents/suffixes normalized, no fuzzy match. Ambiguous crosswalk ESPN IDs excluded.'
    return unit,history,audit


class Design:
    def __init__(self,rows,cols):
        self.cols=cols;self.numeric=Numeric().fit(rows[cols]);self.positions=sorted(rows.pos.astype(str).unique())
    def transform(self,rows):
        num=self.numeric.transform(rows[self.cols]);missing=rows[self.cols].isna().to_numpy(dtype=float)
        return np.c_[num,missing,np.column_stack([rows.pos.astype(str).to_numpy()==p for p in self.positions])]


def feature_sets(rows):
    raw=RAW_COMBINE+[c for c in rows if c.startswith('college_raw__')]
    metrics=sorted(c for c in rows if c.startswith('metric__'))
    availability=RAW_COMBINE+sorted(c for c in rows if c.startswith('availability__'))
    return {'combine':RAW_COMBINE,'availability':availability,'broad_raw':raw,'custom':raw+metrics,'draft_control':raw+['log_pick'],'draft_control_custom':raw+metrics+['log_pick']}


def chronological_splits(rows,max_folds=3):
    years=sorted(rows.draft_year.unique());out=[]
    for year in years:
        tr=np.flatnonzero(rows.draft_year.to_numpy()<=year-2);te=np.flatnonzero(rows.draft_year.to_numpy()==year)
        if len(tr)>=100 and len(te)>=20:out.append((tr,te))
    return out[-max_folds:]


def predict(train,test,cols,alpha):
    if set(train.pfr_id)&set(test.pfr_id):raise ValueError('player leakage')
    if train.draft_year.max()>test.draft_year.min()-2:raise ValueError('outcome maturity leakage')
    design=Design(train,cols);model=Ridge(alpha=alpha).fit(design.transform(train),train.target)
    return np.maximum(model.predict(design.transform(test)),0.)


def tuned(train,test,cols):
    folds=chronological_splits(train)
    if not folds:raise ValueError('insufficient chronological tuning classes')
    loss=[]
    for a in ALPHAS:
        errors=np.concatenate([np.square(train.iloc[j].target.to_numpy()-predict(train.iloc[i],train.iloc[j],cols,a)) for i,j in folds]);loss.append(float(errors.mean()))
    ix=int(np.argmin(loss));return predict(train,test,cols,ALPHAS[ix]),{'alpha':ALPHAS[ix],'inner_mse':loss}


def optional_custom(train,test,base_cols,custom_cols):
    """Shrink a separately tuned custom ridge toward the tuned raw baseline.

    Each inner prediction tunes both endpoints on still-earlier matured classes.
    If too little history exists to tune those endpoints, use fixed penalties
    evaluated only on that inner training set's available chronological folds.
    """
    folds=chronological_splits(train);truth=[];bp=[];cp=[]
    for i,j in folds:
        tr=train.iloc[i];te=train.iloc[j]
        if chronological_splits(tr):
            b,_=tuned(tr,te,base_cols);c,_=tuned(tr,te,custom_cols)
        else:
            # Earliest chronological split has no independent tuning window.
            # Fixed 100 is predeclared implementation default, not chosen on te.
            b=predict(tr,te,base_cols,100.);c=predict(tr,te,custom_cols,100.)
        bp.extend(b);cp.extend(c);truth.extend(te.target)
    y=np.asarray(truth);b=np.asarray(bp);c=np.asarray(cp);base_loss=(y-b)**2;bank=(0.,.25,.5,1.)
    losses=[(y-(b+lam*(c-b)))**2 for lam in bank];ix=int(np.argmin([l.mean() for l in losses]));gain=base_loss-losses[ix];se=float(gain.std(ddof=1)/np.sqrt(len(gain)))
    lam=bank[ix] if gain.mean()>se else 0.
    b,ba=tuned(train,test,base_cols);c,ca=tuned(train,test,custom_cols)
    return np.maximum(b+lam*(c-b),0),{'shrinkage':lam,'inner_gain':float(gain.mean()),'paired_standard_error':se,'baseline':ba,'custom':ca}
