"""Rebuild every literature-direction receipt, without optional dependencies."""
import argparse
import json
from pathlib import Path
from perfectpower.differential_modules import DifferentialModule
from perfectpower.superelliptic_families import SuperellipticFamily
from perfectpower.curve_correspondences import genus_three_elliptic_tower,richelot_correspondence
from perfectpower.formal_isogenies import elliptic_two_isogeny
from perfectpower.marked_curve_topology import reflection_kernel,braid_monodromy
from perfectpower.root_cluster_geometry import cluster_geometry,simultaneous_quadratic_nodes
from perfectpower.binomial_periods import BinomialSum
from perfectpower.sunrise_relative import sunrise_certificate
from perfectpower.certified_period_transport import certified_transport,legendre_marked_periods
from perfectpower.arithmetic_frobenius import frobenius_matrix,frobenius_deformation,tower_frobenius,zeta_by_counting


def build(output):
    output=Path(output);output.mkdir(parents=True,exist_ok=True)
    def save(name,packet):
        (output/(name+'.json')).write_text(json.dumps(packet,indent=2)+'\n');print(name,flush=True)
        return packet
    tower=save('genus_three_tower',genus_three_elliptic_tower())
    save('tower_frobenius',tower_frobenius(tower))
    save('richelot',richelot_correspondence([[1,1,1],[3,2,1],[7,3,1]]))
    save('formal_isogeny',elliptic_two_isogeny(1,2))
    save('marked_kernel',reflection_kernel())
    save('marked_braid',braid_monodromy(2,[1,2,1,-3,2]))
    save('root_clusters',cluster_geometry([0,3,1,4,2,5],3))
    save('simultaneous_nodes',simultaneous_quadratic_nodes([0,3,7]))
    trigonal=SuperellipticFamily({'coefficients':[[0,1],1,0,0,1],'cover_degree':3})
    save('trigonal',trigonal.evidence())
    m=DifferentialModule.from_matrix(trigonal.connection)
    save('trigonal_hodge_search',m.horizontal_endomorphisms(holomorphic_indices=[0,3,4]))
    a=DifferentialModule({'matrix':[[0,1],[[0,0,1],0]]})
    save('matrix_descent',a.involution_descent([[1,0],[0,-1]]))
    save('tensor_invariants',DifferentialModule({'matrix':[[0,0],[0,0]]}).horizontal_endomorphisms(holomorphic_indices=[0],pairing=[[0,1],[-1,0]]))
    for family in ('vandermonde','apery2','apery3'):
        b=BinomialSum({'family':family});save(family,dict(evidence=b.evidence(),terms=b.terms(),telescoper=b.telescoper()))
    save('apery_elliptic_bridge',BinomialSum({'family':'apery2'}).elliptic_bridge())
    save('sunrise',sunrise_certificate())
    save('certified_transport',certified_transport([[1]],['0','1/8'],18))
    save('marked_legendre',legendre_marked_periods(['1/2','9/16'],18))
    save('frobenius',frobenius_matrix([1,1,0,1],5,2))
    save('zeta',zeta_by_counting([1,-1,0,0,0,1],7))
    save('frobenius_deformation',frobenius_deformation([[1,1],1,0,1],5,2,6))
    manifest=dict(schema='pp-literature-curve-corpus/1',receipt_count=22,files=sorted(p.name for p in output.glob('*.json') if p.name!='manifest.json'),
        runtime_dependencies=[],scope='Executable bounded examples for every literature direction; mathematical identities and analytic/p-adic precision certificates retain their individual scopes.')
    save('manifest',manifest)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output',default='docs/literature_receipts');args=parser.parse_args();build(args.output)
