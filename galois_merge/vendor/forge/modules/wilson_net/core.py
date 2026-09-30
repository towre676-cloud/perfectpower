from __future__ import annotations
import numpy as np

def q192_consensus_step(graph_npz,x):
    z=np.load(graph_npz,mmap_mode='r'); nb=z['neighbors']; x=np.asarray(x)
    return x[nb].mean(axis=1)

def route_deletion_ledger():
    return {
      'full': {'degree':390,'normalized_nontrivial_radius':0.0986638949542967},
      'without_C3': {'degree':360,'normalized_nontrivial_radius':0.1293130698748649},
      'drop_pair_12_125': {'degree':270,'normalized_nontrivial_radius':0.15548145677777533},
      'drop_pair_48_116': {'degree':270,'normalized_nontrivial_radius':0.15609104688784875},
      'drop_pair_59_95': {'degree':270,'normalized_nontrivial_radius':0.1666666666666671},
    }
