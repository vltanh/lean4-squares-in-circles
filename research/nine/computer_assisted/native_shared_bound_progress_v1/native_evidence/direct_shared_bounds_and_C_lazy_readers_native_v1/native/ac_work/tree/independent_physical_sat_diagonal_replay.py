#!/usr/bin/env python3
"""Exact arithmetic and complete physical SAT-cover replay.

This module imports no producer, optimizer, or numerical package. A geometry
adapter independently reconstructs each printed necessary row and supplies the
proved absolute bounds. The adapter contract is documented in ADAPTER_CONTRACT.
No original-cell or mask conclusion follows without an externally replayed
initial physical state and a complete cover assembled by the caller.
"""
from copy import deepcopy
from fractions import Fraction as F
from itertools import combinations,product

if not __debug__:
    raise RuntimeError('Exact replay requires assertions.')

DENOMINATOR=1<<40
GRID=1<<20
ADAPTER_CONTRACT="""
adapter.rebuild(state, printed_rows) -> (rows_by_index, absolute_bounds,
    propagated_state). Reconstruct all printed rows independently from the
    physical state, including all original frame/containment/SAT constraints;
    return a mapping from precisely the printed integer indices to validated
    (coefficients, rhs, name) tuples. Every absolute bound is nonnegative and
    proved for the same variables, including any physical SAT auxiliaries.
adapter.infer_angles(angles, scalar) -> (new_angles, terminal, identities).
    This is an independently justified exact physical unit-frame inference.
adapter.analytic(angles) -> 36 proved physical scalar intervals.
adapter.choices(path) -> the reconstructed original physical path choices.
adapter.verify_early_terminal(state, terminal) -> True only after an exact
    independent contradiction proof (e.g. incompatible inherited intervals).
The adapter must preserve the caller's original id, all nine physical frames,
every inherited restriction, and every closed boundary face. The numerical
point, LP phase, best-pair order, timing, and solver diagnostics are ignored.
"""

def box_view(box):return [[str(a),str(b)]for a,b in box]
def diff_view(differences):
    return [dict(pair=list(p),intervals=box_view(v))for p,v in sorted(differences.items())]
def state_view(state):
    out=dict(id=state['id'],path=state['path'],angles=box_view(state['angles']),
        positions=box_view(state['positions']),scalar=box_view(state['scalar']),
        differences=diff_view(state['differences']))
    if 'diagonal'in state:out['diagonal']=diff_view(state['diagonal'])
    return out

def valid_state(state):
    assert len(state['angles'])==9 and len(state['positions'])==18 and len(state['scalar'])==36
    for field in ('angles','positions','scalar'):
        assert all(len(ab)==2 and ab[0]<=ab[1] for ab in state[field]),field
    pairs=set(combinations(range(9),2))
    for field in ('differences','diagonal'):
        if field in state:
            assert set(state[field])<=pairs
            assert all(len(ds)==2 and all(len(ab)==2 and ab[0]<=ab[1]for ab in ds)for ds in state[field].values())

def canonical(row,n):
    coefficients,rhs,name=row;collected={}
    for k,v in coefficients:
        assert type(k)is int and 0<=k<n
        collected[k]=collected.get(k,F(0))+F(v)
    return tuple((k,v)for k,v in sorted(collected.items())if v),F(rhs),name

def validated_rows(adapter,state,printed):
    indices=[entry['index']for entry in printed]
    assert all(type(k)is int and k>=0 for k in indices)
    assert len(indices)==len(set(indices))
    rows,bounds,propagated=adapter.rebuild(deepcopy(state),printed)
    assert set(rows)==set(indices),'Adapter must validate exactly the printed rows.'
    bounds=tuple(map(F,bounds));assert len(bounds)>=54 and all(b>=0 for b in bounds)
    valid_state(propagated)
    assert propagated['id']==state['id'] and propagated['path']==state['path']
    assert propagated['angles']==state['angles']
    for entry in printed:
        literal=(entry['coefficients'],entry['rhs'],entry['name'])
        assert canonical(rows[entry['index']],len(bounds))==canonical(literal,len(bounds)),entry['name']
    return {k:canonical(row,len(bounds))for k,row in rows.items()},bounds,propagated

def exact_sum(rows,bounds,weights):
    assert isinstance(weights,list)
    indices=[item[0]for item in weights]
    assert len(indices)==len(set(indices))
    co=[F(0)]*len(bounds);rhs=F(0)
    for item in weights:
        assert len(item)==2
        k,weight=item
        assert type(k)is int and k in rows
        assert type(weight)is int and weight>0
        q=F(weight,DENOMINATOR);terms,b,_=rows[k];rhs+=q*b
        for index,c in terms:co[index]+=q*c
    return co,rhs

def ceiling_grid(value):
    value=F(value)*GRID
    return F(-((-value.numerator)//value.denominator),GRID)

def first_interval_terminal(positions,scalar,differences,diagonal=None):
    for k,(lo,hi)in enumerate(positions+scalar):
        if lo>hi:return dict(kind='proved_empty_scalar',index=k,lower=str(lo),upper=str(hi))
    # The producer intentionally checks every pair, retaining the last bad
    # pair's first bad axis. Reproduce that printed witness, and prove it.
    terminal=None
    for pair,ds in differences.items():
        for ax,(lo,hi)in enumerate(ds):
            if lo>hi:
                terminal=dict(kind='proved_empty_difference',pair=list(pair),axis=ax,lower=str(lo),upper=str(hi));break
    if terminal is None and diagonal is not None:
        for pair,ds in diagonal.items():
            for ax,(lo,hi)in enumerate(ds):
                if lo>hi:
                    terminal=dict(kind='proved_empty_diagonal',pair=list(pair),axis=ax,lower=str(lo),upper=str(hi));break
    return terminal

def replay_round(adapter,state,record):
    assert record['before']==state_view(state)
    rows,bounds,propagated=validated_rows(adapter,state,record['printed_rows'])
    assert record['propagated']==state_view(propagated)
    assert record['absolute_variable_bounds']==list(map(str,bounds))
    positions=[list(ab)for ab in propagated['positions']]
    scalar=[list(ab)for ab in propagated['scalar']]
    differences={p:[list(ab)for ab in ds]for p,ds in propagated['differences'].items()}
    diagonal={p:[list(ab)for ab in ds]for p,ds in propagated['diagonal'].items()}
    used=set();objectives=set()
    for p in record['proposals']:
        sign,key=p['sign'],p['key'];assert type(sign)is int and sign in(-1,1)
        if p['kind']=='scalar':
            assert type(key)is int and 0<=key<54
            objective=[(key,sign)];target=positions[key]if key<18 else scalar[key-18]
        else:
            assert p['kind']in('difference','diagonal') and isinstance(key,list)and len(key)==3
            i,j,axis=key
            assert all(type(k)is int for k in key)and 0<=i<j<9 and axis in(0,1)
            if p['kind']=='difference':
                objective=[(2*j+axis,sign),(2*i+axis,-sign)];target=differences[i,j][axis]
            else:
                sy=1 if axis==0 else -1
                objective=[(2*j,sign),(2*i,-sign),(2*j+1,sign*sy),(2*i+1,-sign*sy)]
                target=diagonal[i,j][axis]
        assert p['objective']==[list(t)for t in objective]
        objective_key=tuple(objective);assert objective_key not in objectives;objectives.add(objective_key)
        coefficients,rhs=exact_sum(rows,bounds,p['weights'])
        for k,v in objective:coefficients[k]-=v
        correction=sum(b*abs(c)for b,c in zip(bounds,coefficients))
        proved=rhs+correction;upper=F(p['upper'])
        assert F(p['summed_rhs'])==rhs
        assert p['residual_coefficients']==[[k,str(c)]for k,c in enumerate(coefficients)if c]
        assert F(p['residual_correction'])==correction
        assert F(p['proved_upper'])==proved and upper==ceiling_grid(proved)
        assert upper>=proved
        if sign==1:target[1]=min(target[1],upper)
        else:target[0]=max(target[0],-upper)
        used.update(k for k,w in p['weights'])
    assert used==set(rows),'Every printed row must be used, and every used row checked.'
    positions=tuple(map(tuple,positions));scalar=tuple(map(tuple,scalar))
    differences={p:tuple(map(tuple,ds))for p,ds in differences.items()}
    diagonal={p:tuple(map(tuple,ds))for p,ds in diagonal.items()}
    terminal=first_interval_terminal(positions,scalar,differences,diagonal)
    if terminal is not None:
        assert 'after'not in record and 'physical_frame_inferences'not in record
        return None,terminal,len(rows),len(record['proposals'])
    angles,terminal,identities=adapter.infer_angles(state['angles'],scalar)
    assert record['physical_frame_inferences']==identities
    if terminal is not None:
        assert 'after'not in record
        return None,dict(kind='proved_frame_contradiction',label=terminal),len(rows),len(record['proposals'])
    analytic=adapter.analytic(angles);assert len(analytic)==36
    scalar=tuple((max(a,c),min(b,d))for(a,b),(c,d)in zip(scalar,analytic))
    for k,(lo,hi)in enumerate(scalar):
        if lo>hi:
            assert 'after'not in record
            return None,dict(kind='proved_empty_analytic_frame',index=k,lower=str(lo),upper=str(hi)),len(rows),len(record['proposals'])
    # Install exactly the independently certified diagonal objective bounds.
    after=dict(deepcopy(state),positions=positions,scalar=scalar,differences=differences,diagonal=diagonal,angles=angles)
    valid_state(after);assert record['after']==state_view(after)
    return after,None,len(rows),len(record['proposals'])

def replay_reserve(adapter,state,terminal):
    assert terminal['kind']=='positive_exact_reserve'
    rows,bounds,propagated=validated_rows(adapter,state,terminal['rows'])
    assert terminal['absolute_variable_bounds']==list(map(str,bounds))
    coefficients,rhs=exact_sum(rows,bounds,terminal['weights'])
    assert {k for k,w in terminal['weights']}==set(rows)
    correction=sum(b*abs(c)for b,c in zip(bounds,coefficients))
    reserve=-rhs-correction
    assert reserve>0 and F(terminal['reserve'])==reserve
    assert terminal['weighted_coefficients']==list(map(str,coefficients))
    assert F(terminal['weighted_rhs'])==rhs
    return len(rows),reserve

def check_record(record,initial_state,adapter):
    """Return (audit, certified final state or None for an excluded domain)."""
    valid_state(initial_state);state=deepcopy(initial_state)
    assert record['initial']==state_view(state)
    assert record['status']in('OPEN','CANDIDATE_CLOSED')
    assert isinstance(record['rounds'],list)
    printed=deductions=0;terminal=None
    for index,rr in enumerate(record['rounds']):
        after,terminal,count,number=replay_round(adapter,state,rr)
        printed+=count;deductions+=number
        if terminal is not None:
            assert index==len(record['rounds'])-1
            assert record['status']=='CANDIDATE_CLOSED'and record['terminal']==terminal
            assert 'final'not in record
            state=None;break
        state=after
    reserve=None
    if state is not None and record['status']=='CANDIDATE_CLOSED':
        terminal=record['terminal']
        if terminal['kind']=='positive_exact_reserve':
            assert record['terminal_state']==state_view(state)
            count,reserve=replay_reserve(adapter,state,terminal);printed+=count
        else:
            assert adapter.verify_early_terminal(deepcopy(state),terminal)is True
        assert 'final'not in record;state=None
    elif state is not None:
        assert 'terminal'not in record and record['final']==state_view(state)
    return dict(status='PASS_EXCLUDED_PHYSICAL_DOMAIN'if state is None else'PASS_CERTIFIED_PHYSICAL_STATE_OPEN',
        rounds=len(record['rounds']),deductions=deductions,printed_rows_checked=printed,
        reserve=str(reserve)if reserve is not None else None,
        numerical_discovery_fields_used=False,whole_original_credit=0,whole_mask_credit=0),state

def sat_child(parent,pair,choice,adapter):
    pair=tuple(pair);choice=tuple(choice)
    assert len(pair)==2 and all(type(i)is int for i in pair)and 0<=pair[0]<pair[1]<9
    assert len(choice)==3 and all(type(i)is int for i in choice)
    assert choice[0]in pair and choice[1]in(0,1)and choice[2]in(-1,1)
    path=deepcopy(parent['path'])+[['sat',list(pair),list(choice)]]
    child=deepcopy(parent);child['path']=path;child['choices']=adapter.choices(path)
    valid_state(child);return child

def check_complete_cover(parent,pair,children,adapter):
    """children is a list of (choice, record) covering exactly all eight SAT cases."""
    expected=set(product(tuple(pair),(0,1),(-1,1)))
    actual=[tuple(choice)for choice,record in children]
    assert len(actual)==8 and len(set(actual))==8 and set(actual)==expected
    reports=[];open_states=[]
    for choice,record in children:
        report,state=check_record(record,sat_child(parent,pair,choice,adapter),adapter)
        reports.append(dict(choice=list(choice),audit=report))
        if state is not None:open_states.append((tuple(choice),state))
    return dict(status='PASS_COMPLETE_PHYSICAL_SAT_COVER'if not open_states else'PASS_PARTIAL_PHYSICAL_SAT_COVER',
        pair=list(pair),all_eight_physical_alternatives=True,closed_faces_retained=True,
        excluded_alternatives=8-len(open_states),children=reports,
        whole_original_credit=0,whole_mask_credit=0),open_states
