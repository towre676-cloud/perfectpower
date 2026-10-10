"""Source-bound finite SOE proof compiler; Python proposes, Lean accepts.

128 states, 16 actions, 16384 symbols/word, 100000 total witness symbols,
2 MiB canonical input and generated source. Kernel timeout <=600s per process.
No user supplied Lean is executed. Observation equality is exact canonical JSON.
"""
from hashlib import sha256
from copy import deepcopy
from .semantic_fibres import canonical
from .future_states import normalize, future_quotient, check_quotient
from .divisor_square import WorkLimit
from .checked_family import check_rebuilt

SCOPE = 'all finite action words of the supplied finite deterministic partial machine'
MAX_BYTES = 2 * 1024 * 1024


def _choices(values, var, encode=str):
    result = encode(values[-1])
    for i in reversed(range(len(values)-1)):
        result = f'if {var} = {i} then {encode(values[i])} else ({result})'
    return result


def _option(value):
    return 'none' if value is None else f'some {value}'


def compile_soe(spec, packet=None):
    """Validate packet shape/replay then emit literal tables and pair proofs."""
    if len(canonical(spec).encode()) > MAX_BYTES:
        raise WorkLimit('SOE input byte limit exceeded')
    try:
        if type(spec) is not dict or type(spec.get('observations')) is not list or type(spec.get('actions')) is not dict:
            raise ValueError('malformed SOE model')
        spec = normalize(spec)
    except (KeyError, TypeError, AttributeError) as error:
        raise ValueError('malformed SOE model') from error
    packet = future_quotient(spec) if packet is None else deepcopy(packet)
    try:
        if set(packet) != {'schema','model_id','blocks','projection','quotient',
                           'distinguishing_witnesses','refinement_rounds','scope'}:
            raise ValueError('malformed SOE packet fields')
        if packet['schema'] != 'pp-future-quotient/1':
            raise ValueError('unsupported SOE packet schema')
        if (type(packet['blocks']) is not list or type(packet['distinguishing_witnesses']) is not list
                or type(packet['refinement_rounds']) is not int or packet['refinement_rounds'] < 0
                or type(packet['scope']) is not str or type(packet['model_id']) is not str):
            raise ValueError('malformed SOE packet metadata or collections')
        if type(packet['projection']) is not list or any(type(q) is not int for q in packet['projection']):
            raise ValueError('integer projection required')
        total = 0
        for w in packet['distinguishing_witnesses']:
            if set(w) != {'first','second','word','reason'} or type(w['first']) is not int or type(w['second']) is not int or type(w['word']) is not list:
                raise ValueError('malformed distinguishing witness')
            if len(w['word']) > len(spec['observations'])**2:
                raise WorkLimit('SOE witness length limit exceeded')
            total += len(w['word'])
            if total > 100000: raise WorkLimit('SOE total witness limit exceeded')
        if len(canonical(packet).encode()) > MAX_BYTES:
            raise WorkLimit('SOE packet byte limit exceeded')
        check_quotient(packet, spec)
    except (KeyError, TypeError, IndexError, AttributeError) as error:
        raise ValueError('malformed SOE packet') from error
    actions = sorted(spec['actions'])
    labels = sorted(set(map(canonical, spec['observations'])))
    ids = {label: i for i, label in enumerate(labels)}
    n, m, k, o = len(spec['observations']), len(actions), len(packet['blocks']), len(labels)
    def observations(row): return _choices([ids[canonical(x)] for x in row], 's')
    def transitions(model):
        return _choices([_choices(model['actions'][a], 's', _option) for a in actions], 'a', lambda x:x)
    words = {}
    reps = {b[0]: i for i,b in enumerate(packet['blocks'])}
    for w in packet['distinguishing_witnesses']:
        i,j = reps[w['first']], reps[w['second']]
        word = '[' + ', '.join(str(actions.index(a)) for a in w['word']) + ']'
        words[i,j] = words[j,i] = word
    table = [_choices([words.get((i,j), '[]') for j in range(k)], 'j', lambda x:x) for i in range(k)]
    binding = canonical({'model':spec,'packet':packet})
    digest = sha256(binding.encode()).hexdigest()
    lean = f'''import PerfectPower.SOESemantics
namespace PerfectPower.CheckedSOE.P{digest}
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: {digest}; encodings are recorded in the compiler receipt.
def obs (s : Fin {n}) : Fin {o} := {observations(spec['observations'])}
def step (s : Fin {n}) (a : Fin {m}) : Option (Fin {n}) := {transitions(spec)}
def q (s : Fin {n}) : Fin {k} := {_choices(packet['projection'], 's')}
def out (s : Fin {k}) : Fin {o} := {observations(packet['quotient']['observations'])}
def target (s : Fin {k}) (a : Fin {m}) : Option (Fin {k}) := {transitions(packet['quotient'])}
def experiment (i j : Fin {k}) : List (Fin {m}) := {_choices(table, 'i', lambda x:x)}
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin {k}, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin {n}) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
#print axioms complete
end PerfectPower.CheckedSOE.P{digest}
'''
    if len(lean.encode()) > MAX_BYTES: raise WorkLimit('SOE generated source limit exceeded')
    return {'schema':'pp-checked-soe/1','lean':lean,'packet':packet,
            'specification_sha256':digest,'source_sha256':sha256(lean.encode()).hexdigest(),
            'scope':SCOPE,'action_encoding':actions,'observation_encoding':labels,
            'limits':{'states':128,'actions':16,'bytes':MAX_BYTES,'total_witness_symbols':100000,
                      'word_symbols':n*n,'heartbeats':2000000,'recursion':8192}}


def accept_soe(spec, packet=None, **kernel_options):
    """Regenerate from the supplied model; acceptance requires rebuilt Lean proofs."""
    try:
        compiled = compile_soe(spec, packet)
    except (ValueError, WorkLimit) as error:
        return {'accepted':False,'reason':str(error)}
    result = check_rebuilt(compiled, ['SOESemantics'], ['SOESemantics.quotient_complete'], **kernel_options)
    result.update({key:compiled[key] for key in ('packet','action_encoding','observation_encoding','limits')})
    return result
