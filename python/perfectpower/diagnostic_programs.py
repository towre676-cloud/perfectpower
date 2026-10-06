"""Global minimum worst-case resettable diagnostic trees over finite hypotheses."""
from copy import deepcopy
from fractions import Fraction as Q
from functools import lru_cache
from heapq import heappop,heappush
from . import exact_linear as E
from .observable_machine import _q
from .integral_machine import _iv
from .observable_machine import _inputs
from .divisor_square import WorkLimit


class DiagnosticPolicy:
    def __init__(self,specification):
        required={'operators','readouts','hypotheses'}
        if not required<=set(specification) or set(specification)-required-{'seed','operator_costs','readout_costs','state_limit','dp_limit','bit_limit'}:raise ValueError('operators, seed, named readouts and named hypotheses required')
        self.specification=deepcopy(specification);s=self.specification
        if not isinstance(s['readouts'],dict) or not s['readouts'] or not isinstance(s['hypotheses'],dict) or not 1<=len(s['hypotheses'])<=16:raise ValueError('one through 16 named hypotheses and nonempty named readouts required')
        self.names=tuple(sorted(s['hypotheses']));self.readout_names=tuple(sorted(s['readouts']))
        if any(not isinstance(name,str) or not name for name in self.names+self.readout_names):raise ValueError('nonempty names required')
        original_states=tuple(_iv(s['hypotheses'][name]) for name in self.names);n=len(original_states[0])
        original_ops,_,original_readouts=_inputs(s['operators'],s.get('seed',original_states[0]),[s['readouts'][name] for name in self.readout_names])
        if any(len(v)!=n for v in original_states) or len(original_ops[0])!=n:raise ValueError('matching hypothesis dimensions required')
        rows=[];witnesses=[]
        def add(row,witness):
            row=tuple(map(_q,row))
            if E.rank(tuple(rows)+ (tuple(row),))>len(rows):rows.append(tuple(row));witnesses.append(witness)
        for output,row in enumerate(original_readouts):add(row,(output,()))
        cursor=0
        while cursor<len(rows):
            row=rows[cursor];output,word=witnesses[cursor];cursor+=1
            for context,operator in enumerate(original_ops):add(tuple(sum(row[k]*operator[k][j] for k in range(n)) for j in range(n)),(output,(context,)+word))
        def coordinates(row):
            result=E.solve(E.transpose(rows),row) if rows else ()
            if result is None:raise AssertionError('observable span is not closed')
            return tuple(map(_q,result))
        operators=tuple(tuple(coordinates(tuple(sum(row[k]*operator[k][j] for k in range(n)) for j in range(n))) for row in rows) for operator in original_ops)
        readouts=tuple(coordinates(row) for row in original_readouts)
        self.machine=dict(operators_minimal=operators,readouts_minimal=readouts,observable_rows=rows,readout_words=witnesses)
        states=tuple(tuple(E.apply(rows,v)) if rows else () for v in original_states);self.states=states
        operators=self.machine['operators_minimal'];readouts=self.machine['readouts_minimal'];count=len(states)
        oc=tuple(map(_q,s.get('operator_costs',[1]*len(operators))));costs=s.get('readout_costs',[1]*len(readouts))
        if isinstance(costs,dict):
            if set(costs)!=set(self.readout_names):raise ValueError('cost mapping must name every readout')
            costs=[costs[name] for name in self.readout_names]
        rc=tuple(map(_q,costs))
        if len(oc)!=len(operators) or len(rc)!=len(readouts) or any(c<=0 for c in oc) or any(c<0 for c in rc):raise ValueError('positive operator and nonnegative matching readout costs required')
        self.oc,self.rc=oc,rc
        state_limit=s.get('state_limit',100000);dp_limit=s.get('dp_limit',2000000);bits=s.get('bit_limit',8192)
        if any(type(v) is not int or v<1 for v in (state_limit,dp_limit,bits)) or state_limit>1000000 or dp_limit>10000000 or bits>8192:raise ValueError('positive bounded diagnostic budgets required')
        groups={}
        for i,state in enumerate(states):groups.setdefault(state,[]).append(i)
        duplicates=[v for v in groups.values() if len(v)>1]
        if duplicates:
            self.packet=dict(schema='pp-diagnostic-policy/1',status='INDISTINGUISHABLE_HYPOTHESES',groups=[[self.names[i] for i in group] for group in duplicates],complete=True,execution_verified=False);self.nodes={};return
        def values(word,output):
            transformed=states
            for context in word:transformed=tuple(E.apply(operators[context],v) for v in transformed)
            return tuple(E.apply([readouts[output]],v)[0] for v in transformed)
        def partition(outputs):
            groups={}
            for i,value in enumerate(outputs):groups.setdefault(value,[]).append(i)
            return tuple(sorted((tuple(g) for g in groups.values())))
        @lru_cache(None)
        def incumbent(indices):
            if len(indices)<=1:return Q(0)
            a,b=indices[:2]
            options=[]
            for output,word in witnesses:
                answers=values(word,output)
                if answers[a]!=answers[b]:options.append((sum((oc[i] for i in word),Q(0))+rc[output],word,output))
            cost,word,output=min(options);answers=values(word,output);parts={}
            for i in indices:parts.setdefault(answers[i],[]).append(i)
            return cost+max(incumbent(tuple(g)) for g in parts.values())
        upper=incumbent(tuple(range(count)))
        # Remove the common state: only relative outputs determine partitions.
        relative=tuple(tuple(a-b for a,b in zip(v,states[0])) for v in states)
        frontier=[(Q(0),(),relative)];visited={relative:Q(0)};experiments={};expanded=0
        while frontier:
            price,word,state=heappop(frontier)
            if price+min(rc)>upper:break
            if visited[state]!=price:continue
            expanded+=1
            for output,cost in enumerate(rc):
                total=price+cost
                if total>upper:continue
                answers=tuple(E.apply([readouts[output]],v)[0] for v in state);parts=partition(answers)
                if len(parts)==1:continue
                candidate=(total,tuple(word),output)
                if parts not in experiments or candidate<experiments[parts]:
                    if parts not in experiments and len(experiments)>=min(state_limit,dp_limit):raise WorkLimit('diagnostic partition budget')
                    experiments[parts]=candidate
            for context,operator in enumerate(operators):
                cost=price+oc[context]
                if cost+min(rc)>upper:continue
                child=tuple(tuple(E.apply(operator,v)) for v in state)
                if any(abs(x.numerator).bit_length()>bits or x.denominator.bit_length()>bits for v in child for x in v):raise WorkLimit('diagnostic state bit budget')
                if child not in visited or cost<visited[child]:
                    if child not in visited and len(visited)>=state_limit:raise WorkLimit('diagnostic frontier budget; no optimal program returned')
                    visited[child]=cost;heappush(frontier,(cost,word+(context,),child))
        candidates=sorted(((*candidate,parts) for parts,candidate in experiments.items()));decisions={};dp_work=0
        @lru_cache(None)
        def optimum(indices):
            nonlocal dp_work
            if len(indices)<=1:return Q(0)
            selected=set(indices);best=None;winner=None
            for cost,word,output,parts in candidates:
                dp_work+=1
                if dp_work>dp_limit:raise WorkLimit('diagnostic subset budget; no optimal program returned')
                if best is not None and cost>best:break
                restricted=tuple(tuple(i for i in group if i in selected) for group in parts);restricted=tuple(g for g in restricted if g)
                if len(restricted)<2:continue
                value=cost+max(optimum(group) for group in restricted)
                if best is None or value<best:best=value;winner=(cost,word,output,restricted)
            if best is None:raise AssertionError('finite witness did not supply a diagnosis')
            decisions[indices]=winner;return best
        optimal=optimum(tuple(range(count)));nodes=[]
        def tree(indices):
            identity=len(nodes);node=dict(id=identity,hypotheses=[self.names[i] for i in indices]);nodes.append(node)
            if len(indices)==1:node.update(kind='leaf',identified=self.names[indices[0]],remaining_cost=Q(0));return identity
            cost,word,output,parts=decisions[indices];answers=values(word,output)
            node.update(kind='experiment',word=word,readout=output,name=self.readout_names[output],cost=cost,remaining_cost=optimum(indices),branches=[])
            for group in parts:node['branches'].append(dict(value=answers[group[0]],node=tree(group)))
            return identity
        root=tree(tuple(range(count)));self.nodes={node['id']:node for node in nodes}
        self.packet=dict(schema='pp-diagnostic-policy/1',status='OPTIMAL_RESETTABLE_DIAGNOSTIC',root=root,nodes=nodes,worst_case_cost=optimal,
            incumbent_cost=upper,experiment_partitions=len(candidates),relative_states=expanded,dp_subsets=optimum.cache_info().currsize,dp_work=dp_work,
            complete=True,execution_verified=False,operator_costs=oc,readout_costs=rc,
            observable_rows=rows,observable_witnesses=witnesses,
            semantics='each experiment resets to the original unknown hypothesis; noiseless exact readout; reset cost zero; positive operator costs',
            completeness='all experiment partitions of cost at most the finite witness incumbent, followed by exact minimax recursion over proper subsets')

    def summary(self):return {k:self.packet[k] for k in ('status','complete') if k in self.packet}|{k:self.packet[k] for k in ('worst_case_cost','incumbent_cost','experiment_partitions','relative_states','dp_subsets') if k in self.packet}
    def evidence(self):return deepcopy(self.packet)
    def step(self,node,value):
        if type(node) is not int or node not in self.nodes:raise ValueError('valid diagnostic node required')
        current=self.nodes[node]
        if current['kind']=='leaf':raise ValueError('a leaf needs no readout')
        value=_q(value)
        for branch in current['branches']:
            if branch['value']==value:return deepcopy(self.nodes[branch['node']])
        raise ValueError('readout outside the model hypotheses')
    def run(self,hypothesis):
        if hypothesis not in self.names:raise ValueError('known model hypothesis required')
        if self.packet['status']!='OPTIMAL_RESETTABLE_DIAGNOSTIC':raise ValueError('hypotheses cannot be individually identified')
        state=self.states[self.names.index(hypothesis)];node=self.nodes[self.packet['root']];trace=[];total=Q(0)
        while node['kind']!='leaf':
            current=state
            for context in node['word']:current=E.apply(self.machine['operators_minimal'][context],current)
            value=E.apply([self.machine['readouts_minimal'][node['readout']]],current)[0];total+=node['cost']
            trace.append(dict(node=node['id'],word=node['word'],readout=node['name'],value=value,cost=node['cost']))
            node=self.step(node['id'],value)
        return dict(hypothesis=hypothesis,identified=node['identified'],total_cost=total,trace=trace)
