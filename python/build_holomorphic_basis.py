"""Build explicit representatives and link character dimensions to both atlases."""
import hashlib,json
from fractions import Fraction
from perfectpower.legendre_period_bounds import legendre_period_packet
from pathlib import Path
from perfectpower.holomorphic_basis import differential_basis,normalize_in_basis
from perfectpower import polyalg as P
from perfectpower.core import mul,power

def build(output='receipts/holomorphic_basis'):
    out=Path(output);out.mkdir(parents=True,exist_ok=True)
    source=Path('receipts/divisor_sum/complete_quartics.json')
    rows=[];representatives={};total=0
    for i,curve in enumerate(json.loads(source.read_text())['rows']):
        for d in (2,3,4,6):
            p=differential_basis(curve['coefficients'],d)
            key=(d,tuple(p['geometry']['root_multiplicities']))
            representatives.setdefault(key,{'curve_index':i,'packet':p})
            rows.append({'curve_index':i,'power':d,'components':p['geometry']['components'],
                         'basis_dimension_per_component':p['dimension_per_component'],
                         'characters':p['characters']})
            total+=p['dimension_all_components']
    (out/'quartic_characters.json').write_text(json.dumps({'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'rows':rows,'formalized':False},separators=(',',':'))+'\n')
    (out/'representative_bases.json').write_text(json.dumps(list(representatives.values()),separators=(',',':'))+'\n')
    collision_source=Path('receipts/positive_geometry/collision_strata.json');collisions=[]
    for family in json.loads(collision_source.read_text()):
        for stratum in family['strata']:
            shape=stratum['normalization'];f=P.poly([1])
            for a,r in enumerate(shape['multiplicities']):f=mul(f,power(P.poly([-a,1]),r))
            p=differential_basis(f,shape['power'])
            assert p['dimension_per_component']==shape['genus_per_component']
            assert p['geometry']['components']==shape['components']
            collisions.append({'power':shape['power'],'blocks':stratum['blocks'],'multiplicities':shape['multiplicities'],
                               'genus_per_component':p['dimension_per_component'],'characters':p['characters'],
                               'scope':'synthetic distinct cluster locations; normalization of collision polynomial, not stable-limit differentials'})
    (out/'collision_characters.json').write_text(json.dumps({'source_sha256':hashlib.sha256(collision_source.read_bytes()).hexdigest(),'rows':collisions,'formalized':False},separators=(',',':'))+'\n')
    examples=[]
    for name,f,d in [('genus_two',[0,-1,0,0,0,1],2),('cyclic_cubic',[-1,0,0,0,1],3),('split_cusps',[0,0,0,0,0,0,1],4),('repeated_root_genus_two',mul(power(P.poly([-1,1]),2),P.poly([0,-1,0,0,0,1])),2)]:
        examples.append({'name':name,'packet':differential_basis(f,d)})
    p=examples[0]['packet'];examples[0]['supplied_period_example']=normalize_in_basis(p,[[2,1],[1,1]],[3,2])
    (out/'examples.json').write_text(json.dumps(examples,separators=(',',':'))+'\n')
    periods=[legendre_period_packet(Fraction(i,10),80) for i in range(1,10)]
    (out/'legendre_period_intervals.json').write_text(json.dumps(periods,separators=(',',':'))+'\n')
    summary={'legendre_period_packets':len(periods),'quartic_profiles':len(rows),'representative_bases':len(representatives),'differentials_across_profiles':total,'collision_strata':len(collisions),'examples':len(examples),'formalized':False,'analytic_periods_computed':'Legendre family normalized rational interval enclosures only'}
    (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');return summary
if __name__=='__main__':print(json.dumps(build(),indent=2))
