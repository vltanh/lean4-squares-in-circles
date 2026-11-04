#!/usr/bin/env python3
"""Numerical discovery with exact rational guards for full physical SAT covers.

This does not declare any original cell closed. Every child retains one of
the eight original owner/axis/sign separating alternatives; a tree conclusion
requires all siblings and an independent initial-state and arithmetic replay.
"""
import os
for _key in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):
    os.environ[_key]='1'
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations,product
from copy import deepcopy
import hashlib,importlib.util,json,sys,time
import numpy as np
from scipy.sparse import csr_matrix
from scipy.optimize._highspy import _core as H

SCALE=1<<40
GRID=1<<20
ACTIVE=None

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def box(value):return tuple(tuple(map(F,ab))for ab in value)
def view(value):return [[str(a),str(b)]for a,b in value]
def diffview(value):return [{'pair':list(k),'intervals':view(v)}for k,v in sorted(value.items())]
def stateview(state):
    return dict(id=state['id'],path=state['path'],angles=view(state['angles']),
        positions=view(state['positions']),scalar=view(state['scalar']),differences=diffview(state['differences']))
def ceil_grid(x):
    x=F(x)*GRID
    return F(-((-x.numerator)//x.denominator),GRID)
def terms(dual):return [[i,int(round(-float(v)*SCALE))]for i,v in enumerate(dual)if int(round(-float(v)*SCALE))>0]
def sum_rows(rows,bounds,weights):
    c=[F(0)]*len(bounds);b=F(0)
    for i,w in weights:
        assert w>0
        co,rhs,_=rows[i];q=F(w,SCALE);b+=q*rhs
        for k,a in co:c[k]+=q*a
    return c,b
def printed(rows,used):
    return [dict(index=i,name=rows[i][2],coefficients=[[k,str(v)]for k,v in rows[i][0]],rhs=str(rows[i][1]))for i in sorted(used)]

class Context:
    def __init__(self,packet):
        self.packet=Path(packet).resolve();sys.path.insert(0,str(self.packet))
        import b_replay_context
        self.J,self.locate=b_replay_context.install(self.packet/'ancestry')
        self.K=self.J.K;self.V=self.K.V
        self.sources={str(Path(b_replay_context.__file__).resolve()):sha(b_replay_context.__file__)}
        source=self.packet/'ancestry/provenance'
        def load(stem):
            paths=sorted(source.glob('*_'+stem+'.py'));assert paths,(stem,source)
            p=paths[0];self.sources[str(p)]=sha(p)
            spec=importlib.util.spec_from_file_location('satmath_'+stem,p)
            m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
        self.A=load('altitude_capacity_v2');self.D=load('point_disk_rows')
        self.S=load('sharp_strip_rows');self.P=load('frame_perspective_rows')
        self.Hh=load('support_height_rows');self.Dh=load('directional_support_rows')
        self.FC=load('planar_four_center_rows');self.AR=load('square_area_moment_rows')
        self.TE=load('b_three_square_energy_rows')
        self.R=load('review_guarded_frame_bounds_independent')
        self.AH=load('b_active_highs_checked_warning_discovery')
        global ACTIVE
        ACTIVE=self.AH
        self.default_matrices=list(self.AR.axes_matrices())+[
            ((F(1),F(1)),(F(-1),F(1))),((F(2),F(1)),(F(0),F(1))),
            ((F(2),F(-1)),(F(0),F(1))),((F(1),F(0)),(F(1),F(2))),
            ((F(1),F(0)),(F(-1),F(2)))]

    def raw_state(self,record):
        assert record['status']=='OPEN'and'terminal'not in record
        for name in ('angles','positions','scalar','differences'):
            assert record['final_'+name]==record['final_test'][name+'_before']
        path=record['path'];choices=self.V.reconstruct(path)[2]
        self.AH.add_seed_record(record)
        return dict(id=record['id'],path=deepcopy(path),angles=box(record['final_angles']),
            positions=box(record['final_positions']),scalar=box(record['final_scalar']),choices=choices,
            differences={tuple(e['pair']):box(e['intervals'])for e in record['final_differences']})

    def collect(self,state):
        """Physical baseline plus accepted same-original affine consequences."""
        K,V=self.K,self.V
        path=state['path'];angles=state['angles'];choices=state['choices']
        effective,term=V.effective_boxes(angles,choices,K.LEGACY)
        if term:return None,None,None,dict(kind='accepted_effective_angle_terminal',label=term)
        pos,hs,gs,term=V.center_bounds(effective,state['positions'],choices,K.LEGACY)
        if term:return None,None,None,dict(kind='accepted_center_interval_terminal',label=term)
        analytic=K.analytic(effective)
        scalar=tuple((max(a,c),min(b,d))for(a,b),(c,d)in zip(state['scalar'],analytic))
        bad=[(i,a,b)for i,(a,b)in enumerate(scalar)if a>b]
        if bad:return None,None,None,dict(kind='empty_analytic_scalar',witness=[str(x)for x in bad[0]])
        for pair in combinations(range(9),2):
            ds=V.difference_bounds(pair,pos,gs,K.LEGACY)
            if pair in state['differences']:
                ds=tuple((max(a,c),min(b,d))for(a,b),(c,d)in zip(ds,state['differences'][pair]))
            for ax,(a,b)in enumerate(ds):
                if a>b:return None,None,None,dict(kind='empty_difference',pair=list(pair),axis=ax,lower=str(a),upper=str(b))
        rows,bounds,pos,scalar,diffs,guards=K.rebuild(path,angles,state['positions'],choices,state['scalar'],state['differences'])
        extra,g=self.A.generate_rows(diffs);rows+=extra
        rows+=self.D.generate_rows(scalar,diffs)
        extra,g=self.S.rotated_three_square_rows(diffs);rows+=extra
        rows+=self.P.rows(angles,scalar)
        rows+=self.Hh.rows(scalar,diffs)
        rows+=self.Dh.rows(scalar,diffs)
        rows+=self.FC.rows(diffs)
        rows+=self.AR.generate_linear(diffs,matrices=self.default_matrices)
        rows+=self.TE.linear_rows(diffs)
        propagated=dict(state,positions=pos,scalar=scalar,differences=diffs)
        return rows,bounds,propagated,None

    def child(self,parent,pair,choice):
        pair=list(pair);choice=list(choice)
        assert choice[0]in pair and choice[1]in(0,1)and choice[2]in(-1,1)
        path=deepcopy(parent['path'])+[['sat',pair,choice]]
        choices=self.V.reconstruct(path)[2]
        return dict(deepcopy(parent),path=path,choices=choices)

def _full_highs(rows,n,phase=True):
    rr=[];cc=[];vv=[];bb=[]
    for i,(co,b,name)in enumerate(rows):
        for k,v in co:rr.append(i);cc.append(k);vv.append(float(v))
        rr.append(i);cc.append(n);vv.append(-1.);bb.append(float(b))
    mat=csr_matrix((vv,(rr,cc)),shape=(len(rows),n+1))
    lp=H.HighsLp();lp.num_col_=n+1;lp.num_row_=len(rows)
    lp.col_cost_=np.r_[np.zeros(n),1. if phase else 0.]
    lp.col_lower_=np.r_[np.full(n,-np.inf),-1. if phase else 0.]
    lp.col_upper_=np.r_[np.full(n,np.inf),np.inf if phase else 0.]
    lp.row_lower_=np.full(len(rows),-np.inf);lp.row_upper_=np.array(bb)
    lp.a_matrix_.format_=H.MatrixFormat.kRowwise;lp.a_matrix_.start_=mat.indptr
    lp.a_matrix_.index_=mat.indices;lp.a_matrix_.value_=mat.data
    h=H._Highs();h.setOptionValue('output_flag',False);h.setOptionValue('threads',1)
    h.setOptionValue('time_limit',30.);h.passModel(lp)
    return h

def make_highs(rows,n,phase=True):
    if ACTIVE is not None and phase:
        return ACTIVE.ActiveHighs(rows,n,lambda rs,nn:_full_highs(rs,nn,True),H)
    return _full_highs(rows,n,phase)

def phase_solve(rows,bounds):
    h=make_highs(rows,len(bounds));h.run()
    if h.getModelStatus()!=H.HighsModelStatus.kOptimal:
        return h,None,None,dict(kind='solver_no_conclusion',status=str(h.getModelStatus()))
    sol=h.getSolution();phase=float(sol.col_value[-1]);point=list(map(float,sol.col_value[:-1]))
    if phase>1e-9:
        weights=terms(sol.row_dual);co,rhs=sum_rows(rows,bounds,weights)
        correction=sum(m*abs(v)for m,v in zip(bounds,co));reserve=-rhs-correction
        if reserve>0:
            return h,phase,point,dict(kind='positive_exact_reserve',weights=weights,
                rows=printed(rows,{i for i,w in weights}),absolute_variable_bounds=list(map(str,bounds)),
                weighted_coefficients=list(map(str,co)),weighted_rhs=str(rhs),reserve=str(reserve))
    return h,phase,point,None

def best_pairs(state,point,limit=8):
    selected={tuple(pair)for pair,kind,ch in state['choices']if kind=='sat'}
    result=[]
    for i,j in combinations(range(9),2):
        if(i,j)in selected:continue
        dx=point[2*j]-point[2*i];dy=point[2*j+1]-point[2*i+1]
        a,b=point[18+i],point[27+i];c,d=point[18+j],point[27+j]
        required=(1+abs(a*c+b*d)+abs(a*d-b*c))/2
        maximum=max(abs(a*dx+b*dy),abs(-b*dx+a*dy),abs(c*dx+d*dy),abs(-d*dx+c*dy))
        result.append((maximum-required,(i,j)))
    result.sort()
    return result[:limit]

def bound_round(context,state,rows,bounds,propagated,h,eps=F(1,2000),objective_limit=None):
    n=len(bounds);h.changeColCost(n,0.);h.changeColBounds(n,0.,0.)
    targets=[]
    for k,(lo,hi)in enumerate(propagated['positions']+propagated['scalar']):
        for sign in(-1,1):targets.append(('scalar',k,sign,[(k,sign)],hi if sign==1 else-lo))
    for(i,j),ds in sorted(propagated['differences'].items()):
        for ax,(lo,hi)in enumerate(ds):
            for sign in(-1,1):targets.append(('difference',(i,j,ax),sign,[(2*j+ax,sign),(2*i+ax,-sign)],hi if sign==1 else-lo))
    if objective_limit is not None:targets=targets[:objective_limit]
    pos=[list(ab)for ab in propagated['positions']];scalar=[list(ab)for ab in propagated['scalar']]
    diffs={p:[list(ab)for ab in ds]for p,ds in propagated['differences'].items()}
    previous=[];proposals=[];used=set();failures=0
    for kind,key,sign,objective,old in targets:
        for k,c in previous:h.changeColCost(k,0.)
        for k,c in objective:h.changeColCost(k,-float(c))
        previous=objective;h.setOptionValue('time_limit',h.getRunTime()+4.);h.run()
        if h.getModelStatus()!=H.HighsModelStatus.kOptimal:
            failures+=1;continue
        if float(old)+h.getObjectiveValue()<float(eps):continue
        weights=terms(h.getSolution().row_dual);co,rhs=sum_rows(rows,bounds,weights)
        for k,c in objective:co[k]-=c
        correction=sum(m*abs(v)for m,v in zip(bounds,co));proved=rhs+correction;upper=ceil_grid(proved)
        if old-upper<eps:continue
        proposals.append(dict(kind=kind,key=list(key)if isinstance(key,tuple)else key,sign=sign,
            objective=[list(x)for x in objective],upper=str(upper),proved_upper=str(proved),
            weights=weights,summed_rhs=str(rhs),residual_coefficients=[[k,str(v)]for k,v in enumerate(co)if v],
            residual_correction=str(correction)))
        used.update(i for i,w in weights)
        target=(pos[key]if key<18 else scalar[key-18])if kind=='scalar'else diffs[key[0],key[1]][key[2]]
        if sign==1:target[1]=min(target[1],upper)
        else:target[0]=max(target[0],-upper)
    record=dict(before=stateview(state),propagated=stateview(propagated),proposals=proposals,
        printed_rows=printed(rows,used),absolute_variable_bounds=list(map(str,bounds)),numeric_failures=failures)
    terminal=None
    for k,(lo,hi)in enumerate(pos+scalar):
        if lo>hi:terminal=dict(kind='proved_empty_scalar',index=k,lower=str(lo),upper=str(hi));break
    if terminal is None:
        for pair,ds in diffs.items():
            for ax,(lo,hi)in enumerate(ds):
                if lo>hi:terminal=dict(kind='proved_empty_difference',pair=list(pair),axis=ax,lower=str(lo),upper=str(hi));break
    pos=tuple(map(tuple,pos));scalar=tuple(map(tuple,scalar));diffs={p:tuple(map(tuple,ds))for p,ds in diffs.items()}
    if terminal:return None,record,terminal
    angles,term,identities=context.R.infer_angles(state['angles'],scalar)
    record['physical_frame_inferences']=identities
    if term:return None,record,dict(kind='proved_frame_contradiction',label=term)
    analytic=context.K.analytic(angles)
    scalar=tuple((max(a,c),min(b,d))for(a,b),(c,d)in zip(scalar,analytic))
    for k,(lo,hi)in enumerate(scalar):
        if lo>hi:return None,record,dict(kind='proved_empty_analytic_frame',index=k,lower=str(lo),upper=str(hi))
    after=dict(state,positions=pos,scalar=scalar,differences=diffs,angles=angles)
    record['after']=stateview(after)
    return after,record,None

def search_node(context,state,rounds=0,checkpoint=None):
    initial=stateview(state);round_records=[];started=time.monotonic()
    for ri in range(rounds+1):
        rows,bounds,propagated,term=context.collect(state)
        if term:return dict(status='CANDIDATE_CLOSED',initial=initial,rounds=round_records,terminal=term,seconds=time.monotonic()-started),None,None
        h,phase,point,term=phase_solve(rows,bounds)
        if term and term['kind']!='solver_no_conclusion':
            return dict(status='CANDIDATE_CLOSED',initial=initial,rounds=round_records,terminal_state=stateview(state),terminal=term,seconds=time.monotonic()-started),None,None
        if term:return dict(status='NO_NUMERICAL_CONCLUSION',initial=initial,rounds=round_records,diagnostic=term,seconds=time.monotonic()-started),state,None
        if ri==rounds:
            return dict(status='OPEN',initial=initial,rounds=round_records,final=stateview(state),phase=phase,best_pairs=best_pairs(state,point),point=point,seconds=time.monotonic()-started),state,point
        after,record,term=bound_round(context,state,rows,bounds,propagated,h)
        record['phase']=phase;round_records.append(record)
        context.AH.SEED_NAMES.update(x['name']for x in record['printed_rows'])
        print('BOUND_ROUND',ri,'deductions',len(record['proposals']),'seconds',round(time.monotonic()-started,2),flush=True)
        if checkpoint is not None:
            checkpoint(dict(status='RUNNING',initial=initial,rounds=round_records,terminal=term,
                latest=stateview(after)if after is not None else None,seconds=time.monotonic()-started))
        if term:return dict(status='CANDIDATE_CLOSED',initial=initial,rounds=round_records,terminal=term,seconds=time.monotonic()-started),None,None
        state=after
    raise AssertionError('unreachable')

def main():
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('packet',type=Path);ap.add_argument('parent',type=Path)
    ap.add_argument('output',type=Path);ap.add_argument('--rounds',type=int,default=0)
    ap.add_argument('--pair',type=int,nargs=2);ap.add_argument('--cover',action='store_true')
    args=ap.parse_args();args.output.mkdir(parents=True,exist_ok=True)
    context=Context(args.packet);raw=args.parent.read_bytes();source=json.loads(raw)
    state=context.raw_state(source)
    before,updated,point=search_node(context,state,args.rounds)
    before.update(parent=dict(path=str(args.parent.resolve()),sha256=hashlib.sha256(raw).hexdigest()),sources=context.sources,
        no_original_cell_or_mask_credit=True,acceptance_status='INDEPENDENT_REPLAY_PENDING')
    (args.output/'root.json').write_text(json.dumps(before,indent=2)+'\n')
    print('ROOT',before['status'],before.get('phase'),before.get('best_pairs'),before['seconds'],flush=True)
    if not args.cover or before['status']!='OPEN':return
    pair=tuple(args.pair)if args.pair else tuple(before['best_pairs'][0][1]);children=[]
    for owner,axis,sign in product(pair,(0,1),(-1,1)):
        choice=(owner,axis,sign);child=context.child(updated,pair,choice)
        result,_,_=search_node(context,child,args.rounds)
        name=f'child_{owner}_{axis}_{sign}.json'
        (args.output/name).write_text(json.dumps(result,indent=2)+'\n')
        children.append(dict(choice=list(choice),file=name,sha256=sha(args.output/name),status=result['status']))
        print('CHILD',pair,choice,result['status'],result.get('phase'),result['seconds'],flush=True)
    cover=dict(schema='complete_physical_sat_owner_axis_sign_cover_discovery_v1',pair=list(pair),parent=sha(args.output/'root.json'),
        children=children,complete_eight_alternatives=True,closed_children=sum(c['status']=='CANDIDATE_CLOSED'for c in children),
        acceptance_status='INDEPENDENT_REPLAY_PENDING',no_original_cell_or_mask_credit=True)
    (args.output/'cover.json').write_text(json.dumps(cover,indent=2)+'\n')

if __name__=='__main__':main()
