from __future__ import annotations
import json
from pathlib import Path
from .schur_section_relation_v16 import SchurSectionRelation
ROOT=Path(__file__).resolve().parents[2]
LIB=ROOT/'DATA'/'FORMATION'/'native_schur_section_library_v10.json'

def load_native_library():
    return json.load(open(LIB))

def relation_from_record(rec):
    return SchurSectionRelation(int(rec['n']),tuple(tuple(map(int,r)) for r in rec['U']),tuple(tuple(map(int,r)) for r in rec['V']),len(rec['U'][0]),len(rec['V'][0]))

def get_relation(rel_id:str):
    for r in load_native_library()['relations']:
        if r['id']==rel_id:return relation_from_record(r)
    raise KeyError(rel_id)
