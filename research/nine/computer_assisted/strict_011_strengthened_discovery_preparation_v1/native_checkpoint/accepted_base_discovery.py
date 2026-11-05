#!/usr/bin/env python3
"""Standalone LP proposals for the freshly justified representative 011 root.

Every accepted certificate is checked with the frozen independent arithmetic.
Records are immutable and content-addressed; an atomic manifest is the only
mutable proof pointer. Numerical imports occur only when a real LP is requested.
No legacy original-cell context, V, K, or inherited normalization is loaded.
"""
if not __debug__:
    raise RuntimeError('Discovery certificate checks require assertions.')

import argparse
from copy import deepcopy
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import combinations, product
import json
from math import hypot, isfinite
import os
from pathlib import Path
import subprocess
import sys
import time

CHECKPOINT_SHA = 'ac389f6184af6503294a13fb30c1da82e38d052a5d579bf43ccd4a0017b0485b'
ATOMIC_SHA = '2f17219f8689b343f7f1c29e7a314272bd5ace8d25fbee11f58cd20b44543eb3'
MODEL_NAME = 'strict_011_representative_root_v1'
COVER_NAME = 'strict_011_representative_cover_v1'
DENOMINATOR = 1 << 40

def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()

def load(name, path, expected):
    assert digest(path) == expected, str(path)
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def bootstrap(checkpoint):
    checkpoint = Path(checkpoint).resolve()
    assert digest(checkpoint/'CHECKPOINT_MANIFEST.json') == CHECKPOINT_SHA
    inventory = json.loads((checkpoint/'CHECKPOINT_MANIFEST.json').read_text())
    assert inventory['original_cell_credit'] == inventory['whole_mask_credit'] == 0
    for rel, entry in inventory['files'].items():
        path = (checkpoint/rel).resolve()
        assert path.is_relative_to(checkpoint) and path.is_file()
        assert path.stat().st_size == entry['bytes'] and digest(path) == entry['sha256']
    def member(module, rel):
        return load(module, checkpoint/rel, inventory['files'][rel]['sha256'])
    P = member('fresh011_discovery_row_factory', MODEL_NAME+'/representative_strict_011_root.py')
    I = member('fresh011_discovery_independent_attachment', MODEL_NAME+'/independent_strict_011_adapter.py')
    T = member('fresh011_discovery_full_cover', COVER_NAME+'/verify_strict_011_complete_tree.py')
    G = member('fresh011_discovery_exact_arithmetic', 'dependencies/workspace/b_work/independent_physical_sat_replay.py')
    X = member('fresh011_discovery_exact_proxy', 'dependencies/workspace/b_work/independent_physical_proxy_cover.py')
    A = load('fresh011_discovery_atomic_checkpoint', Path(__file__).resolve().with_name('atomic_json_checkpoint.py'), ATOMIC_SHA)
    document = json.loads((checkpoint/MODEL_NAME/'snapshots/ROOT_DOCUMENT.json').read_text())
    assert I.verify_root(document) == P.fresh_state()
    return dict(checkpoint=checkpoint, inventory=inventory, P=P, I=I, T=T, G=G, X=X, A=A)

def literal(rows, indices):
    return [dict(index=k, name=rows[k][2], coefficients=[[j,str(v)] for j,v in rows[k][0]],
                 rhs=str(rows[k][1])) for k in sorted(indices)]

def weights_from_dual(dual):
    result = []
    for k, value in enumerate(dual):
        value = float(value)
        assert isfinite(value)
        weight = int(round(max(0.0, -value)*DENOMINATOR))
        if weight:
            result.append([k,weight])
    return result

def rational_sum(rows, bounds, weights):
    coefficients = [F(0)]*len(bounds)
    rhs = F(0)
    assert len({k for k,w in weights}) == len(weights)
    for k, weight in weights:
        assert type(k) is int and 0 <= k < len(rows) and type(weight) is int and weight > 0
        factor = F(weight,DENOMINATOR)
        terms, bound, _ = rows[k]
        rhs += factor*bound
        for column, value in terms:
            coefficients[column] += factor*value
    return coefficients, rhs

def reserve_from_weights(rows, bounds, weights):
    if not weights:
        return None
    coefficients, rhs = rational_sum(rows,bounds,weights)
    reserve = -rhs-sum(bound*abs(c) for bound,c in zip(bounds,coefficients))
    if reserve <= 0:
        return None
    return dict(kind='positive_exact_reserve', weights=weights,
        rows=literal(rows,{k for k,w in weights}), absolute_variable_bounds=list(map(str,bounds)),
        weighted_coefficients=list(map(str,coefficients)),weighted_rhs=str(rhs),reserve=str(reserve))

class NumericalLP:
    """Only floating-point proposals; no LP status is a proof conclusion."""
    def __init__(self, rows, bounds, seconds):
        for key in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):
            assert os.environ.get(key) == '1', 'Single-thread environment required before numeric import.'
        import numpy as np
        from scipy.optimize import linprog
        from scipy.sparse import csr_matrix, hstack
        self.np, self.linprog = np, linprog
        rr,cc,vv = [],[],[]
        for k,(terms,rhs,name) in enumerate(rows):
            for column,value in terms:
                rr.append(k);cc.append(column);vv.append(float(value))
        self.n = len(bounds)
        self.matrix = csr_matrix((vv,(rr,cc)),shape=(len(rows),self.n))
        self.rhs = np.array([float(row[1]) for row in rows])
        self.phase_matrix = hstack((self.matrix,csr_matrix(-np.ones((len(rows),1)))),format='csr')
        self.options = dict(time_limit=float(seconds),primal_feasibility_tolerance=1e-9,
                            dual_feasibility_tolerance=1e-9, threads=1)

    def phase(self):
        np = self.np
        result = self.linprog(np.r_[np.zeros(self.n),1.0],A_ub=self.phase_matrix,b_ub=self.rhs,
            bounds=[(None,None)]*self.n+[(0,None)],method='highs',options=self.options)
        if result.status != 0:
            return dict(optimal=False,status=int(result.status),message=str(result.message))
        point = list(map(float,result.x[:-1])); phase = float(result.x[-1])
        assert all(map(isfinite,point)) and isfinite(phase)
        return dict(optimal=True,status=0,phase=phase,point=point,
                    dual=list(map(float,result.ineqlin.marginals)))

    def maximum(self, objective):
        c = self.np.zeros(self.n)
        for column,value in objective:
            c[column] = -float(value)
        result = self.linprog(c,A_ub=self.matrix,b_ub=self.rhs,bounds=[(None,None)]*self.n,
                             method='highs',options=self.options)
        if result.status != 0:
            return None
        return list(map(float,result.ineqlin.marginals))

def objectives(state, limit, round_number):
    candidates = []
    for k in range(54):
        for sign in (-1,1):
            candidates.append(('scalar',k,sign,[(k,sign)]))
    for pair in combinations(range(9),2):
        for axis,sign in product((0,1),(-1,1)):
            i,j = pair
            candidates.append(('difference',[i,j,axis],sign,[(2*j+axis,sign),(2*i+axis,-sign)]))
    assert len(candidates) == 252
    if limit >= len(candidates):
        return candidates
    offset = (round_number*limit)%len(candidates)
    return (candidates[offset:]+candidates[:offset])[:limit]

def bound_round(bundle, state, rows, bounds, propagated, solver, limit, round_number):
    P,I,G = bundle['P'],bundle['I'],bundle['G']
    proposals, used = [],set()
    for kind,key,sign,objective in objectives(propagated,limit,round_number):
        dual = solver.maximum(objective)
        if dual is None:
            continue
        weights = weights_from_dual(dual)
        coefficients,rhs = rational_sum(rows,bounds,weights)
        for column,value in objective:
            coefficients[column] -= value
        correction = sum(bound*abs(c) for bound,c in zip(bounds,coefficients))
        proved = rhs+correction
        upper = G.ceiling_grid(proved)
        if kind == 'scalar':
            interval = (propagated['positions']+propagated['scalar'])[key]
        else:
            i,j,axis = key; interval = propagated['differences'][i,j][axis]
        previous = interval[1] if sign == 1 else -interval[0]
        if upper >= previous:
            continue
        assert weights
        proposals.append(dict(kind=kind,key=key,sign=sign,objective=[list(t) for t in objective],
            weights=weights,summed_rhs=str(rhs),residual_coefficients=[[k,str(c)] for k,c in enumerate(coefficients) if c],
            residual_correction=str(correction),proved_upper=str(proved),upper=str(upper)))
        used.update(k for k,w in weights)
    if not proposals:
        return None,state,None
    positions = [list(ab) for ab in propagated['positions']]
    scalars = [list(ab) for ab in propagated['scalar']]
    differences = {pair:[list(ab) for ab in rectangle] for pair,rectangle in propagated['differences'].items()}
    for proposal in proposals:
        key,sign,upper = proposal['key'],proposal['sign'],F(proposal['upper'])
        if proposal['kind'] == 'scalar':
            target = positions[key] if key < 18 else scalars[key-18]
        else:
            i,j,axis = key; target = differences[i,j][axis]
        if sign == 1:
            target[1] = min(target[1],upper)
        else:
            target[0] = max(target[0],-upper)
    positions,scalars = tuple(map(tuple,positions)),tuple(map(tuple,scalars))
    differences = {pair:tuple(map(tuple,ds)) for pair,ds in differences.items()}
    terminal = G.first_interval_terminal(positions,scalars,differences)
    record = dict(before=P.state_view(state),propagated=P.state_view(propagated),
        printed_rows=literal(rows,used),absolute_variable_bounds=list(map(str,bounds)),proposals=proposals)
    if terminal is None:
        analytic = I.analytic(state['angles'])
        scalars = tuple((max(a,c),min(b,d)) for (a,b),(c,d) in zip(scalars,analytic))
        for k,(lo,hi) in enumerate(scalars):
            if lo > hi:
                terminal = dict(kind='proved_empty_analytic_frame',index=k,lower=str(lo),upper=str(hi))
                break
        record['physical_frame_inferences'] = []
        if terminal is None:
            after = dict(deepcopy(state),positions=positions,scalar=scalars,differences=differences)
            record['after'] = P.state_view(after)
    checked,independent_terminal,count,number = G.replay_round(I.Adapter(),state,record)
    assert independent_terminal == terminal and number == len(proposals) and count == len(used)
    return record,checked,terminal

class Store:
    """Every installed manifest points only to already durable immutable records."""
    def __init__(self, bundle, folder, manifest):
        self.bundle,self.folder,self.manifest = bundle,Path(folder),deepcopy(manifest)

    def record(self,node):
        entry = next(e for e in self.manifest['nodes'] if e['id'] == node)
        path = self.folder/entry['file']
        assert digest(path) == entry['sha256']
        return json.loads(path.read_text())

    def put_immutable(self,node,record):
        data = (json.dumps(record,indent=2)+'\n').encode()
        value = sha256(data).hexdigest()
        relative = f'nodes/node_{node:06d}_{value}.json'
        path = self.folder/relative
        if path.exists():
            assert not path.is_symlink() and path.read_bytes() == data
        else:
            self.bundle['A'].write_json(path,record)
        assert digest(path) == value
        return dict(id=node,file=relative,sha256=value)

    def install(self,manifest):
        # No record bytes change when this proof pointer is replaced.
        for entry in manifest['nodes']:
            assert digest(self.folder/entry['file']) == entry['sha256']
        self.bundle['A'].write_json(self.folder/'manifest.json',manifest)
        self.manifest = deepcopy(manifest)

    def update_record(self,node,record):
        old = self.record(node)
        assert record['initial'] == old['initial']
        initial = self.bundle['P'].parse_state(old['initial'])
        audit,state = self.bundle['G'].check_record(record,initial,self.bundle['I'].Adapter())
        entry = self.put_immutable(node,record)
        manifest = deepcopy(self.manifest)
        old_entry = next(e for e in manifest['nodes'] if e['id'] == node)
        assert 'split' not in old_entry
        old_entry.update(entry)
        self.install(manifest)
        return audit,state

    def split(self,node,kind,argument,cut=None):
        P,I,G,X = [self.bundle[k] for k in ('P','I','G','X')]
        record = self.record(node)
        audit,parent = G.check_record(record,P.parse_state(record['initial']),I.Adapter())
        assert parent is not None
        current = next(e for e in self.manifest['nodes'] if e['id'] == node)
        assert 'split' not in current
        if kind == 'angle':
            choices = [0,1]
            states = [I.angle_child(parent,argument,cut,side) for side in choices]
            split = dict(kind=kind,original=argument,cut=str(F(cut)),children=[])
        else:
            assert kind in ('sat','proxy')
            pair = tuple(argument)
            choices = list(product(pair,(0,1),(-1,1))) if kind == 'sat' else list(product((0,1),(-1,1)))
            states = [(G.sat_child(parent,pair,ch,I.Adapter()) if kind == 'sat'
                       else X.proxy_child(parent,pair,ch,I.Adapter())) for ch in choices]
            assert all(state == P.physical_child(parent,kind,pair,ch) for ch,state in zip(choices,states))
            split = dict(kind=kind,pair=list(pair),children=[])
        first = max(e['id'] for e in self.manifest['nodes'])+1
        entries = []
        for offset,(choice,state) in enumerate(zip(choices,states)):
            child_id = first+offset
            I.validate_state(state)
            child = dict(status='OPEN',initial=P.state_view(state),rounds=[],final=P.state_view(state))
            entries.append(self.put_immutable(child_id,child))
            split['children'].append(dict(node=child_id,**({'side':choice} if kind == 'angle' else {'choice':list(choice)})))
        manifest = deepcopy(self.manifest)
        next(e for e in manifest['nodes'] if e['id'] == node)['split'] = split
        manifest['nodes'].extend(entries)
        self.install(manifest)  # All closed alternatives enter in one pointer update.
        return [e['id'] for e in entries]

def initialize(bundle,source,output):
    source,output = Path(source).resolve(),Path(output).resolve()
    assert not output.exists()
    before = digest(source)
    report = bundle['T'].verify(source,bundle['checkpoint']/'dependencies/workspace',
                                bundle['checkpoint']/MODEL_NAME)
    assert digest(source) == before and report['root_id'] == bundle['P'].ROOT_ID
    assert report['mask'] == '011/00' and report['radius_mode'] == 'strict'
    manifest = json.loads(source.read_text())
    output.mkdir(parents=True,exist_ok=False); (output/'nodes').mkdir()
    document = source.parent/manifest['root_document']['file']
    data = document.read_bytes(); assert sha256(data).hexdigest() == manifest['root_document']['sha256']
    with (output/'root_document.json').open('xb') as f:
        f.write(data);f.flush();os.fsync(f.fileno())
    store = Store(bundle,output,dict(schema=manifest['schema'],root_document=dict(
        file='root_document.json',sha256=sha256(data).hexdigest()),root=manifest['root'],nodes=[]))
    installed = deepcopy(store.manifest)
    for entry in manifest['nodes']:
        path = source.parent/entry['file'];assert digest(path) == entry['sha256']
        item = store.put_immutable(entry['id'],json.loads(path.read_text()))
        if 'split' in entry:
            item['split'] = deepcopy(entry['split'])
        installed['nodes'].append(item)
    assert digest(source) == before
    store.install(installed)
    bundle['A'].write_json(output/'INPUT_EXACT_REPLAY.json',report)
    bundle['A'].write_json(output/'DISCOVERY_SOURCE_BINDING.json',dict(
        source_manifest=str(source),source_manifest_sha256=before,checkpoint_sha256=CHECKPOINT_SHA,
        driver_sha256=digest(Path(__file__)),atomic_helper_sha256=ATOMIC_SHA,
        root_id=bundle['P'].ROOT_ID,mask='011/00',radius_mode='strict',
        physical_originals=9,original_corners=36,original_pairs=36,marked_cones=5,
        legacy_geometry_context_imported=False,new_row_families=False,
        numerical_results_are_only_proposals=True,original_cell_credit=0,whole_mask_credit=0))
    return store,report

def choose_split(state,point):
    assert len(point) >= 54 and all(map(isfinite,point))
    selected_sat = {p for p,kind,ch in state['choices'] if kind == 'sat'}
    selected_proxy = {p for p,kind,ch in state['choices'] if kind == 'proxy'}
    pairs=[]
    for i,j in combinations(range(9),2):
        dx,dy = point[2*j]-point[2*i],point[2*j+1]-point[2*i+1]
        a,b,c,d = point[18+i],point[27+i],point[18+j],point[27+j]
        ni,nj = hypot(a,b),hypot(c,d)
        if ni and nj:
            a,b,c,d = a/ni,b/ni,c/nj,d/nj
        required=(1+abs(a*c+b*d)+abs(a*d-b*c))/2
        projected=max(abs(a*dx+b*dy),abs(-b*dx+a*dy),abs(c*dx+d*dy),abs(-d*dx+c*dy))
        pairs.append((projected-required,(i,j)))
    pairs.sort()
    if len(selected_proxy) < 5:
        for gap,pair in pairs:
            if pair not in selected_proxy:
                return 'proxy',pair,None
    defect,original=max((1-point[18+i]**2-point[27+i]**2,i) for i in range(9)
                        if state['angles'][i][0] < state['angles'][i][1])
    if len(selected_sat) >= 2 and defect > 0.02:
        lo,hi=state['angles'][original];cut=F(0) if lo < 0 < hi else (lo+hi)/2
        return 'angle',original,cut
    for gap,pair in pairs:
        if pair not in selected_sat:
            return 'sat',pair,None
    lo,hi=state['angles'][original];cut=F(0) if lo < 0 < hi else (lo+hi)/2
    return 'angle',original,cut

def search_node(bundle,store,node,args,backend=NumericalLP):
    P,I,G=[bundle[k] for k in ('P','I','G')]
    record=store.record(node)
    initial=P.parse_state(record['initial'])
    audit,state=G.check_record(record,initial,I.Adapter())
    assert state is not None
    point=None
    for extra in range(args.rounds+1):
        rows,bounds,propagated,terminal=P.collect(state)
        if terminal is not None:
            assert I.Adapter.verify_early_terminal(state,terminal)
            record=dict(record,status='CANDIDATE_CLOSED',terminal=terminal)
            record.pop('final',None)
            store.update_record(node,record)
            return None,None
        solver=backend(rows,bounds,args.lp_seconds)
        phase=solver.phase()
        if not phase['optimal']:
            print(json.dumps(dict(node=node,event='LP_NO_CONCLUSION',status=phase)),flush=True)
            return state,None
        point=phase['point']
        certificate=reserve_from_weights(rows,bounds,weights_from_dual(phase['dual']))
        if certificate is not None:
            G.replay_reserve(I.Adapter(),state,certificate)
            record=dict(record,status='CANDIDATE_CLOSED',terminal_state=P.state_view(state),terminal=certificate)
            record.pop('final',None)
            store.update_record(node,record)
            print(json.dumps(dict(node=node,event='EXACT_CONDITIONAL_EXCLUSION',reserve=certificate['reserve'])),flush=True)
            return None,None
        if extra == args.rounds:
            break
        rr,after,terminal=bound_round(bundle,state,rows,bounds,propagated,solver,args.objectives,len(record['rounds']))
        if rr is None:
            break
        record=deepcopy(record);record['rounds'].append(rr)
        if terminal is not None:
            record.update(status='CANDIDATE_CLOSED',terminal=terminal);record.pop('final',None)
        else:
            record['final']=P.state_view(after)
        store.update_record(node,record)
        print(json.dumps(dict(node=node,event='EXACT_BOUND_ROUND',proposals=len(rr['proposals']),
                              rows=len(rr['printed_rows']),rounds=len(record['rounds']))),flush=True)
        if terminal is not None:
            return None,None
        state=after
    return state,point

def run(args,backend=NumericalLP):
    bundle=bootstrap(args.checkpoint)
    store,input_report=initialize(bundle,args.input,args.output)
    started=time.monotonic()
    if args.pilot_ab_negative:
        assert input_report['nodes']==1 and input_report['open_leaves']==1
        root=store.manifest['root'];record=store.record(root)
        assert record==dict(status='OPEN',initial=bundle['P'].state_view(bundle['P'].fresh_state()),
                            rounds=[],final=bundle['P'].state_view(bundle['P'].fresh_state()))
        children=store.split(root,'proxy',(0,1))
        target=children[0]
        assert store.record(target)['initial']['path'][-1]==['proxy',[0,1],[0,-1]]
        state,point=search_node(bundle,store,target,args,backend)
        assert state is None,'Actual LP pilot did not produce an independently checked exclusion.'
    else:
        frontier=list(input_report['open_leaf_ids'])
        while frontier:
            node=frontier.pop(0)
            state,point=search_node(bundle,store,node,args,backend)
            if state is None or point is None:
                continue
            depth=len(state['path'])
            if depth >= args.max_depth:
                continue
            kind,argument,cut=choose_split(state,point)
            count=2 if kind=='angle' else 4 if kind=='proxy' else 8
            if len(store.manifest['nodes'])+count > args.max_nodes:
                continue
            children=store.split(node,kind,argument,cut)
            frontier=children+frontier
            print(json.dumps(dict(event='COMPLETE_CLOSED_SPLIT',node=node,kind=kind,
                                  children=children,nodes=len(store.manifest['nodes']))),flush=True)
    # The final proof gate runs in a fresh interpreter without numerical imports.
    output=Path(args.output).resolve()
    command=[sys.executable,'-B','-S',str(bundle['checkpoint']/COVER_NAME/'verify_strict_011_complete_tree.py'),
        str(output/'manifest.json'),str(output/'EXACT_REPLAY.json'),'--workspace',
        str(bundle['checkpoint']/'dependencies/workspace'),'--model-folder',str(bundle['checkpoint']/MODEL_NAME)]
    result=subprocess.run(command,check=True,capture_output=True,text=True)
    report=json.loads((output/'EXACT_REPLAY.json').read_text())
    if args.pilot_ab_negative:
        assert report['nodes']==5 and report['excluded_leaves']==1 and report['open_leaves']==3
        assert not report['whole_mask_proved']
    summary=dict(status='PASS_FRESH_EXACT_DISCOVERY_CHECKPOINT',root_id=bundle['P'].ROOT_ID,
        mode='AB_NEGATIVE_PROXY_PILOT' if args.pilot_ab_negative else 'BOUNDED_WHOLE_ROOT',
        nodes=report['nodes'],excluded_leaves=report['excluded_leaves'],open_leaves=report['open_leaves'],
        whole_mask_proved_by_exact_tree=report['whole_mask_proved'],automatic_mask_credit=0,
        exact_report_sha256=digest(output/'EXACT_REPLAY.json'),
        manifest_sha256=digest(output/'manifest.json'),seconds=time.monotonic()-started)
    bundle['A'].write_json(output/'DISCOVERY_COMPLETION.json',summary)
    print(json.dumps(summary),flush=True)
    return summary

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--checkpoint',type=Path,required=True)
    p.add_argument('--input',type=Path,required=True,help='Frozen complete representative-tree manifest')
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--pilot-ab-negative',action='store_true')
    p.add_argument('--rounds',type=int,default=1)
    p.add_argument('--objectives',type=int,default=54)
    p.add_argument('--max-nodes',type=int,default=33)
    p.add_argument('--max-depth',type=int,default=8)
    p.add_argument('--lp-seconds',type=float,default=10)
    args=p.parse_args()
    assert 0<=args.rounds<=20 and 1<=args.objectives<=252
    assert args.max_nodes>=1 and args.max_depth>=0 and args.lp_seconds>0
    run(args)

if __name__=='__main__':
    main()
