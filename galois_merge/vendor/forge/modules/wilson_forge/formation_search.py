from __future__ import annotations
import json
from pathlib import Path

class ThetaArchitectureLattice:
    """Query the frozen v13/Hamming formation-normal-form architecture quotient."""
    def __init__(self, json_path):
        self.path=Path(json_path)
        self.data=json.loads(self.path.read_text())
        self.states=self.data['states']

    def by_dimension(self, k:int):
        return [s for s in self.states if s['dimension']==k]

    def minimum_traffic(self, k:int):
        rows=self.by_dimension(k)
        if not rows: raise KeyError(k)
        m=min(s['route_degree_cost'] for s in rows)
        return [s for s in rows if s['route_degree_cost']==m]

    def smallest_state_with_at_least_frequencies(self, n:int):
        rows=[s for s in self.states if s['frequency_count']>=n and s['dimension']>0]
        if not rows: raise ValueError('requested frequency count exceeds frozen Hamming layer')
        rows.sort(key=lambda s:(s['route_degree_cost'],s['frequency_count'],s['support_size'],s['support_routes']))
        return rows[0]

    def full_spatial_states(self):
        return [s for s in self.states if s['wilson_full_152_spatial_closure']]
