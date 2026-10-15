"""Player-separated residual ridge with an exact zero-correction option.

Optional scientific dependencies: requirements-movement.txt. Never reads labels
from evaluation players. Source-repeat weights are measurement heuristics, not
calibrated phase probabilities. Existing movement/PerfectJet engines unchanged.
"""
from dataclasses import dataclass
import numpy as np
import pandas as pd
from sklearn.linear_model import Ridge

PHYS = ['combine_height','combine_weight','hand_size','arm_length','wing_span','ten_yd_split','forty','vertical','broad_jump','three_cone','short_shuttle','bench_reps','ngs_athleticism_score','ngs_college_production_score','ngs_final_score']
SETS = {'full15': PHYS, 'core8': ['combine_height','combine_weight','ten_yd_split','forty','vertical','broad_jump','three_cone','short_shuttle'], 'motor4': ['ten_yd_split','forty','three_cone','short_shuttle']}
ALPHAS = (.1,1.,10.,100.,1000.,10000.,np.inf)
CORRECTION_ALPHAS = (1.,10.,100.,1000.)
SHRINKAGES = (.25,.5,1.)
PREFIXES = {'kinematic': ('path_length','peak_speed','speed_gain','mean_acceleration','braking_impulse','turn_work'), 'ordered': ('order_area_','order_triple_'), 'uncertain': ('recovery_accel','brake_accel','redirect_turn','phase_duration_','phase_sd_','phase_boundary_width_','phase_entropy_per_frame','onset_range_')}
FAMILY_NAMES = ('kinematic','ordered','uncertain','combined','reliability_combined')


def validate(rows):
    required = set(PHYS) | {'nfl_id','draft_year','target','combine_position'}
    if not required <= set(rows):
        raise ValueError('missing player schema: ' + ','.join(sorted(required-set(rows))))
    if rows.nfl_id.isna().any() or rows.draft_year.isna().any():
        raise ValueError('missing player identity/class')
    if rows.groupby('nfl_id').draft_year.nunique().max() != 1:
        raise ValueError('player occurs in multiple classes')
    if not np.isfinite(rows.target).all() or not rows.target.between(0,1).all():
        raise ValueError('target must be finite in [0,1]')


def separated(train, test):
    if set(train.nfl_id) & set(test.nfl_id):
        raise ValueError('athlete leakage')


def splits(rows, k=3, seed=714):
    """Class-stratified identity splits; bootstrap duplicate rows stay together."""
    groups = rows[['nfl_id','draft_year']].drop_duplicates()
    if len(groups) < 4:
        raise ValueError('at least four distinct training players required')
    k = min(k,len(groups)); buckets = [[] for _ in range(k)]
    rng = np.random.default_rng(seed)
    for _, g in groups.groupby('draft_year',sort=True):
        ids = g.nfl_id.to_numpy().copy(); rng.shuffle(ids)
        # Rotate short class slices so every fold receives players when possible.
        start = min(range(k),key=lambda j:len(buckets[j]))
        for j, ident in enumerate(ids):buckets[(start+j)%k].append(ident)
    for ids in buckets:
        mask = rows.nfl_id.isin(ids).to_numpy()
        if mask.any() and (~mask).any():yield np.flatnonzero(~mask),np.flatnonzero(mask)


class Numeric:
    def fit(self, frame):
        x = frame.to_numpy(dtype=float); x = np.where(np.isfinite(x),x,np.nan)
        # All-missing training columns become constant zeros without warnings.
        self.median = np.array([np.median(c[np.isfinite(c)]) if np.isfinite(c).any() else 0. for c in x.T])
        x = np.where(np.isfinite(x),x,self.median)
        self.mean=x.mean(axis=0); self.scale=x.std(axis=0); self.scale[self.scale<1e-12]=1
        return self
    def transform(self,frame):
        x=frame.to_numpy(dtype=float)
        return (np.where(np.isfinite(x),x,self.median)-self.mean)/self.scale


class ConventionalDesign:
    def __init__(self, rows, name):
        self.cols=SETS[name]+sorted(c for c in rows if c.startswith('available__'))
        self.numeric=Numeric().fit(rows[self.cols])
        self.positions=sorted(rows.combine_position.fillna('MISSING').astype(str).unique())
    def transform(self,rows):
        pos=rows.combine_position.fillna('MISSING').astype(str).to_numpy()
        return np.c_[self.numeric.transform(rows[self.cols]), np.column_stack([pos==p for p in self.positions])]


def ridge_predictions(x,y,xt,alpha):
    if np.isinf(alpha):return np.full(len(xt),np.mean(y))
    return Ridge(alpha=alpha).fit(x,y).predict(xt)


def families(rows):
    cols=sorted(c for c in rows if c.startswith('movement__'))
    out={name:[c for c in cols if c.split('__')[-1].startswith(prefix)] for name,prefix in PREFIXES.items()}
    out['combined']=sorted(set(sum(out.values(),[])));out['reliability_combined']=out['combined']
    if any(not v for v in out.values()):raise ValueError('missing movement family')
    return out


class Baseline:
    def __init__(self,rows,seed=714):
        y=rows.target.to_numpy(); configs=[(s,a) for s in SETS for a in ALPHAS]
        losses=np.zeros(len(configs)); folds=list(splits(rows,3,seed))
        for i,j in folds:
            for si,s in enumerate(SETS):
                design=ConventionalDesign(rows.iloc[i],s)
                x=design.transform(rows.iloc[i]);xt=design.transform(rows.iloc[j])
                for ai,a in enumerate(ALPHAS):
                    ci=si*len(ALPHAS)+ai
                    losses[ci]+=np.square(y[j]-np.clip(ridge_predictions(x,y[i],xt,a),0,1)).sum()/len(rows)
        ci=int(np.argmin(losses));self.name,self.alpha=configs[ci]
        self.design=ConventionalDesign(rows,self.name)
        self.mean=float(y.mean());self.model=None if np.isinf(self.alpha) else Ridge(alpha=self.alpha).fit(self.design.transform(rows),y)
        self.audit={'physical_set':self.name,'alpha':'mean' if np.isinf(self.alpha) else self.alpha,'inner_mse':losses.tolist()}
    def predict(self,rows):
        p=np.full(len(rows),self.mean) if self.model is None else self.model.predict(self.design.transform(rows))
        return np.clip(p,0,1)


def repeat_reliability(events, train_ids, columns):
    """Diagonal repeat-noise estimate, pooled within player per drill.

    Insufficient repeats or zero total variance yields zero reliability rather
    than inventing a calibration. Outcomes never enter this calculation.
    """
    e=events[events.nfl_id.isin(train_ids)];weights=[];support={}
    for col in columns:
        _,drill,feature=col.split('__',2)
        d=e[e.drill_name.eq(drill)]
        if feature not in d:weights.append(0.);continue
        d=d[['nfl_id',feature]].dropna();g=d.groupby('nfl_id')[feature]
        n=g.count();df=int((n-1).clip(lower=0).sum());total=float(d[feature].var(ddof=1)) if len(d)>1 else 0.
        within=float(((d[feature]-g.transform('mean'))**2).sum()/df) if df else 0.
        r=float(np.clip(1-within/total,0,1)) if df>0 and total>1e-12 else 0.
        weights.append(r);support[drill]={'players':int(len(n)),'repeat_players':int((n>1).sum()),'within_degrees_freedom':df}
    return np.asarray(weights),support


class ResidualFit:
    def __init__(self,rows,events,seed=714):
        validate(rows); self.rows=rows;self.cols=families(rows);self.baseline=Baseline(rows,seed)
        # OOF residual response: each nuisance baseline is itself tuned without
        # the held player's response. Full-data in-sample residuals are not used.
        oof=np.empty(len(rows))
        for f,(i,j) in enumerate(splits(rows,3,seed+1)):
            separated(rows.iloc[i],rows.iloc[j])
            oof[j]=Baseline(rows.iloc[i],seed+20+f).predict(rows.iloc[j])
        residual=rows.target.to_numpy()-oof
        self.transforms={};self.models={};self.support={}
        # Always residualize against the full conventional design for comparability.
        design=ConventionalDesign(rows,'full15');self.full_design=design;b=design.transform(rows)
        for family in FAMILY_NAMES:
            cols=self.cols[family];norm=Numeric().fit(rows[cols]);z=norm.transform(rows[cols]);nuisance=Ridge(alpha=10).fit(b,z)
            z=z-nuisance.predict(b).reshape(z.shape)
            w=np.ones(len(cols))
            if family=='reliability_combined':
                w,support=repeat_reliability(events,set(rows.nfl_id),cols);self.support=support
                w=np.sqrt(w)
            z=z*w;self.transforms[family]=(norm,nuisance,w)
            for a in CORRECTION_ALPHAS:self.models[family,a]=Ridge(alpha=a,fit_intercept=False).fit(z,residual)
    def predictions(self,test):
        separated(self.rows,test);base=self.baseline.predict(test);out={('zero',0.,0.):base}
        b=self.full_design.transform(test)
        for family in FAMILY_NAMES:
            norm,nuisance,w=self.transforms[family];z=norm.transform(test[self.cols[family]])
            z=(z-nuisance.predict(b).reshape(z.shape))*w
            for a in CORRECTION_ALPHAS:
                correction=self.models[family,a].predict(z)
                for lam in SHRINKAGES:out[family,a,lam]=np.clip(base+lam*correction,0,1)
        return out


def choose(predictions,y, family='selected'):
    zero=('zero',0.,0.); options=[zero]+[c for c in predictions if c!=zero and (family=='selected' or c[0]==family)]
    losses={c:np.square(y-predictions[c]) for c in options}
    best=min(options,key=lambda c:losses[c].mean())
    improvement=losses[zero]-losses[best]
    se=float(improvement.std(ddof=1)/np.sqrt(len(y))) if len(y)>1 else np.inf
    picked=best if improvement.mean()>se else zero
    return picked,{'config':list(picked),'minimum_config':list(best),'paired_gain':float(improvement.mean()),'paired_standard_error':se,'zero_inner_mse':float(losses[zero].mean()),'minimum_inner_mse':float(losses[best].mean())}


def fit_predict(train,test,events,seed=714):
    separated(train,test);validate(train);validate(test)
    train=train.reset_index(drop=True);y=train.target.to_numpy();inner={}
    for f,(i,j) in enumerate(splits(train,3,seed)):
        fit=ResidualFit(train.iloc[i],events,seed+100+f)
        for config,p in fit.predictions(train.iloc[j]).items():
            if config not in inner:inner[config]=np.empty(len(train))
            inner[config][j]=p
    fit=ResidualFit(train,events,seed+200);test_bank=fit.predictions(test)
    pp={'conventional':test_bank['zero',0.,0.]};audit={'baseline':fit.baseline.audit,'selection':{},'repeat_support':fit.support}
    for family in FAMILY_NAMES+('selected',):
        config,selection=choose(inner,y,family);pp[family]=test_bank[config];audit['selection'][family]=selection
    return pp,audit
