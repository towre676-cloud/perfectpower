"""Fail-closed identity, source availability and delayed convex aggregation."""
import re
import unicodedata
import numpy as np
import pandas as pd
EXPERTS=('combine','historical','raw','custom')
BOUNDS={'target':float(np.log1p(10000)),'receiving_efficiency':30.,'pressure_target':100.}

def strict_name(value):
    if not isinstance(value,str):return ''
    text=unicodedata.normalize('NFKD',value).encode('ascii','ignore').decode().lower()
    return ' '.join(re.sub(r'[^a-z0-9 ]','',text).split())

def birth(value):
    if value is None or pd.isna(value):return None
    text=str(value)[:10]
    if not re.fullmatch(r'\d{4}-\d{2}-\d{2}',text):return None
    try:return pd.Timestamp(text).date().isoformat()
    except ValueError:return None

def roster_identity(prospects,rosters):
    """Unique name AND birth evidence; ambiguity clears inherited IDs."""
    s=rosters.copy();s['_birth']=s.date_of_birth.map(birth)
    s['_name']=s.athlete_display_name.fillna(s.full_name).map(strict_name)
    by_birth={dob:g for dob,g in s.dropna(subset=['_birth']).groupby('_birth')};records=[]
    for row in prospects.itertuples():
        names={strict_name(row.player_name),strict_name(row.display_name)}-{''}
        g=by_birth.get(birth(row.birth_date),s.iloc[:0])
        m=g[g['_name'].isin(names)&g.season.between(row.draft_year-3,row.draft_year-1)]
        ids=sorted(set(m.athlete_id.dropna().astype(int)))
        prior=s[s.athlete_id.isin(ids)&s.season.between(row.draft_year-3,row.draft_year-1)]
        conflicts=[i for i in ids if set(prior.loc[prior.athlete_id.eq(i),'_birth'].dropna())-{birth(row.birth_date)}]
        if conflicts:ids=[]
        records.append({'pfr_id':row.pfr_id,'draft_year':int(row.draft_year),'pos':row.pos,
         'college_id':ids[0] if len(ids)==1 else None,'status':'verified_name_birth' if len(ids)==1 else 'ambiguous' if ids else 'unsupported',
         'conflicting_birth_ids':conflicts,'candidates':ids,'evidence_seasons':sorted(set(m.season.astype(int))),
         'previous_id':None if pd.isna(row.espn_id) else int(row.espn_id)})
    out=pd.DataFrame(records)
    duplicate=out.loc[out.status.eq('verified_name_birth'),'college_id'].duplicated(keep=False)
    ix=duplicate[duplicate].index
    out.loc[ix,'status']='ambiguous';out.loc[ix,'college_id']=np.nan
    return out

def contextual_recruits(recruits,rosters):
    """Reciprocal unique name/school/time evidence, never an ID crosswalk."""
    r=recruits.copy();r['_name']=r.player_name.map(strict_name)
    r['team_id']=pd.to_numeric(r.team_id,errors='coerce');r['recruit_id']=r.recruit_id.astype(str)
    if r.duplicated(['season','recruit_id']).any():raise ValueError('duplicate recruiting key')
    s=rosters[['season','athlete_id','team_id','athlete_display_name','full_name']].copy()
    s['_name']=s.athlete_display_name.fillna(s.full_name).map(strict_name)
    s['team_id']=pd.to_numeric(s.team_id,errors='coerce');first=s.groupby('athlete_id').season.min().to_dict()
    by_name={name:g for name,g in s[s['_name'].ne('')].groupby('_name')};records=[]
    for row in r.itertuples(index=False,name=None):
        q=dict(zip(r.columns,row));year=int(q['season']);g=by_name.get(q['_name'],s.iloc[:0])
        m=g[g.team_id.eq(q['team_id'])&g.season.between(year,year+1)]
        evidence=sorted(set(m.athlete_id.astype(int)));ids=[i for i in evidence if first[i]>=year]
        status='no_context_match' if not evidence else 'earlier_enrollment_conflict' if not ids else 'ambiguous_context' if len(ids)>1 else 'candidate'
        records.append({'recruit_season':year,'recruit_id_247':q['recruit_id'],
         'team_id_espn':None if pd.isna(q['team_id']) else int(q['team_id']),'player_name':q['player_name'],
         'status':status,'context_evidence_seasons':sorted(set(m.loc[m.athlete_id.isin(ids),'season'].astype(int))),'candidates':ids,'rejected_earlier_ids':sorted(set(evidence)-set(ids)),
         'college_id':ids[0] if len(ids)==1 else None,'stars':q['stars'],'grade':q['grade']})
    out=pd.DataFrame(records)
    conflict=out.loc[out.status.eq('candidate'),'college_id'].duplicated(keep=False)
    out.loc[conflict[conflict].index,'status']='nonunique_recruit_history'
    out.loc[out.status.eq('candidate'),'status']='corroborated_context_only'
    out.loc[~out.status.eq('corroborated_context_only'),'college_id']=np.nan
    return out

def available_before(published_at,cutoff,authoritative):
    """Unknown publication fails closed; retrieval is never publication."""
    if not authoritative or published_at is None or pd.isna(published_at):return False
    try:
        t=pd.Timestamp(published_at)
        return False if t.tzinfo is None else bool(t<=pd.Timestamp(cutoff))
    except (ValueError,TypeError):return False

def delayed_aggregate(predictions,bound):
    """Separate parity forecasters respect >=2-year label maturity delay.

    Fixed eta=1; normalized squared losses in [0,1], equal class weights.
    """
    if not np.isfinite(bound) or bound<=0:raise ValueError('positive finite bound required')
    if predictions.pfr_id.duplicated().any():raise ValueError('repeat player')
    values=predictions[['target',*EXPERTS]].to_numpy(dtype=float)
    if not np.isfinite(values).all():raise ValueError('missing prediction or outcome')
    out=predictions.copy();histories={0:np.zeros(len(EXPERTS)),1:np.zeros(len(EXPERTS))};audit=[]
    clipped=np.clip(values,0,bound)
    for year in sorted(out.draft_year.unique()):
        loc=out.draft_year.eq(year).to_numpy();parity=int(year)%2
        logw=-histories[parity];w=np.exp(logw-logw.max());w/=w.sum()
        out.loc[loc,'aggregate']=clipped[loc,1:]@w
        loss=((clipped[loc,1:]-clipped[loc,0,None])/bound)**2
        histories[parity]+=loss.mean(axis=0)
        audit.append({'class':int(year),'history_classes':[int(y) for y in sorted(out.draft_year.unique()) if y<=year-2 and int(y)%2==parity],
                      'weights':dict(zip(EXPERTS,w.tolist())),'players':int(loc.sum())})
    return out,audit

def recruitment_residual(production,recruitment,fit_mask,eligible,strength=20.):
    """Outcome-free ridge adjustment. Caller supplies explicit eligibility."""
    y,r=np.asarray(production,float),np.asarray(recruitment,float)
    mask=np.asarray(fit_mask,bool)&np.asarray(eligible,bool)&np.isfinite(y)&np.isfinite(r)
    if mask.sum()<20:raise ValueError('insufficient verified as-of recruiting links')
    center=r[mask].mean();scale=max(r[mask].std(),1.);x=np.c_[np.ones(len(r)),(r-center)/scale]
    beta=np.linalg.solve(x[mask].T@x[mask]+np.diag([0.,strength]),x[mask].T@y[mask])
    return np.where(np.asarray(eligible,bool),y-x@beta,np.nan)
