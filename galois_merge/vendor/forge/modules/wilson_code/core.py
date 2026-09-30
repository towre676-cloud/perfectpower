from __future__ import annotations
import json
import numpy as np

def load_code_family(path):
    return json.load(open(path))

def q192_paley_signs(graph_npz):
    z=np.load(graph_npz,allow_pickle=False)
    return z['slot_paley_sign'].astype(np.int16)

def paley_precondition(local_words, signs):
    x=np.asarray(local_words); s=np.asarray(signs)
    return x*s.reshape((1,-1)+((1,)*(x.ndim-2))) if x.ndim>=2 else x*s

def paley_uncondition(local_words, signs):
    # signs are +/-1, so inverse equals itself
    return paley_precondition(local_words,signs)
