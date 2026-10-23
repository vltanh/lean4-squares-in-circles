#!/usr/bin/env python3
"""Exact finite regressions for CY.TWO; not a universal proof or Lean check."""
from __future__ import annotations
from fractions import Fraction as F
from dataclasses import dataclass
from itertools import combinations, product
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import json
import platform
import subprocess

V = tuple[F, F]
ZERO: V = (F(0), F(0))
EX: V = (F(1), F(0))
EY: V = (F(0), F(1))
HALF = F(1, 2)
Q0 = F(17, 4)
COUNTS: dict[str, int] = {}

def check(test: bool, category: str) -> None:
    if not test:
        raise AssertionError(category)
    COUNTS[category] = COUNTS.get(category, 0) + 1

def add(x: V, y: V) -> V:
    return (x[0] + y[0], x[1] + y[1])
def sub(x: V, y: V) -> V:
    return (x[0] - y[0], x[1] - y[1])
def scale(t: F | int, x: V) -> V:
    return (t*x[0], t*x[1])
def dot(x: V, y: V) -> F:
    return x[0]*y[0] + x[1]*y[1]
def J(x: V) -> V:
    return (-x[1], x[0])
def P(x: V) -> V:
    return (F(0), x[1])
def orient(t: F) -> V:
    return ((1-t*t)/(1+t*t), 2*t/(1+t*t))
def omega(u: V) -> F:
    a,b=u
    return -a*b*(a*a-b*b)
def B(u: V, r: V) -> V:
    return sub(P(r), scale(omega(u), J(r)))

@dataclass(frozen=True)
class Square:
    c: V
    u: V = EX
    @property
    def v(self) -> V:
        return J(self.u)
    def corners(self) -> list[V]:
        return [add(self.c, add(scale(F(s,2), self.u), scale(F(t,2), self.v)))
                for s,t in product((-1,1),repeat=2)]
    def support(self, n: V) -> F:
        return (abs(dot(n,self.u))+abs(dot(n,self.v)))/2
    def contains(self, p: V) -> bool:
        r=sub(p,self.c)
        return abs(dot(r,self.u)) <= HALF and abs(dot(r,self.v)) <= HALF
    def velocity(self, p: V) -> V:
        return add(P(self.c),scale(omega(self.u),J(sub(p,self.c))))

def check_one_square_algebra() -> None:
    for k in range(0,61):
        a,b=orient(F(k,150))
        for u in ((a,b),(a,-b),(-b,a),(b,a),(-a,-b)):
            a1,b1=u; v=J(u)
            om=omega(u)
            check(omega(v)==om,'quarter_turn_invariance')
            check(dot(u,B(u,u))==b1*b1,'support_matrix')
            check(dot(u,B(u,v))==2*a1*b1**3,'support_matrix')
            check(dot(v,B(u,u))==2*a1**3*b1,'support_matrix')
            check(dot(v,B(u,v))==a1*a1,'support_matrix')
            check(b1*b1-abs(2*a1*b1**3)==b1*b1*(1-2*abs(a1*b1)), 'diagonal_dominance_identity')
            check(a1*a1-abs(2*a1**3*b1)==a1*a1*(1-2*abs(a1*b1)), 'diagonal_dominance_identity')
            generic=a1*b1!=0 and 2*abs(a1*b1)<1
            for axis,tangent in ((u,v),(v,u)):
                for sign in (-1,1):
                    n=scale(sign,axis)
                    for y in (F(-1,2),F(-1,3),F(0),F(1,4),F(1,2)):
                        r=add(scale(F(sign,2),axis),scale(y,tangent))
                        value=dot(n,B(u,r))
                        check(value>=0,'outward_face_nonnegative')
                        if generic:
                            check(value>0,'generic_face_strict')
            for s,t in product((-1,1), repeat=2):
                r=add(scale(F(s,2),u),scale(F(t,2),v))
                for w in (F(1,3),F(1),F(5,2)):
                    n=add(scale(s,u),scale(t*w,v))
                    value=dot(n,B(u,r))
                    check(value>=0,'outward_corner_nonnegative')
                    if generic:
                        check(value>0,'generic_corner_strict')
    # At the diagonal exceptional frame, the own-coordinate matrix is exact.
    for s,t in product((-1,1),repeat=2):
        r=(F(s,2),F(t,2))
        image=((r[0]+r[1])/2,(r[0]+r[1])/2)
        check((image==ZERO)==(s==-t),'diagonal_zero_vertices')

def check_circle_signs() -> None:
    for k in range(1,101):
        u=orient(F(k,250)); a,b=u
        if 2*b>=HALF:
            c=(F(2)-(a+b)/2,(a-b)/2)
            sq=Square(c,u);z=(F(2),F(0))
            check(all(dot(p,p)<=4 for p in sq.corners()),'single_loaded_corner_containment')
            check(z in sq.corners(),'actual_circle_corner')
            power=2*dot(z,sq.velocity(z))
            check(power==2*omega(u)*z[0]*c[1],'circle_work_identity')
            check(power<0,'single_corner_strict_sign')
            # Physical half-turn and reflection preserve the power sign.
            for inv,reflect in product((-1,1),repeat=2):
                tf=lambda p:(inv*p[0],inv*reflect*p[1])
                ss=Square(tf(c),tf(u));zz=tf(z)
                check(2*dot(zz,ss.velocity(zz))==power,'circle_symmetry_sign')
        # Two adjacent outer circle vertices at q=17/4, horizontal weighted load.
        T=F(2);eta=-T*b/a
        if abs(eta)<=HALF:
            sq=Square(scale(T-HALF,u),u)
            zs=[add(scale(T,u),scale(HALF,sq.v)),add(scale(T,u),scale(-HALF,sq.v))]
            weights=[HALF+eta,HALF-eta]
            m=add(scale(weights[0],zs[0]),scale(weights[1],zs[1]))
            check(m[1]==0 and m[0]>0,'adjacent_horizontal_load')
            check(all(dot(z,z)==Q0 for z in zs),'adjacent_circle_corners')
            power=2*sum(w*dot(z,sq.velocity(z)) for w,z in zip(weights,zs))
            check(power==2*omega(u)*m[0]*sq.c[1], 'circle_work_identity')
            check(power<0,'adjacent_circle_strict_sign')
    # Necessary negative control: a vertical load need not have nonpositive work.
    sq=Square((F(0),F(3,2)))
    zs=[(HALF,F(2)),(-HALF,F(2))]
    power=sum(dot(z,sq.velocity(z)) for z in zs)
    check(power==6 and power>0,'nonparallel_load_negative_control')

def check_contacts() -> None:
    for k in range(1,50):
        u=orient(F(k,130));v=J(u)
        p=(F(1,3),F(-2,5))
        # Parallel squares touching along an entire side; offset application point.
        for h in (F(-1,3),F(0),F(2,5)):
            s=Square(sub(p,add(scale(HALF,u),scale(h,v))),u)
            t=Square(add(s.c,u),u)
            vi=s.velocity(p);vj=t.velocity(p)
            val=dot(u,sub(vi,vj))
            check(s.contains(p) and t.contains(p),'contact_membership')
            check(val==-u[1]*u[1]<0,'same_frame_contact_power')
        # Axis side versus tilted left vertex, common point fixed at p.
        a,b=u;hh=(a+b)/2;kk=(a-b)/2
        s=Square(sub(p,(HALF,F(0))))
        t=Square(add(p,(hh,-kk)),u)
        val=dot(EX,sub(s.velocity(p),t.velocity(p)))
        check(s.contains(p) and t.contains(p),'contact_membership')
        check(dot(EX,sub(p,s.c))==s.support(EX),'support_point')
        check(dot(EX,sub(p,t.c))==-t.support(EX),'support_point')
        check(val<0,'mixed_frame_contact_strict')

# All physical examples below are exact, with collinear circle loads and
# positive-length side contact. They demonstrate feasibility of every one
# of the four surviving core topologies, NOT nine-square completion.
def check_physical(name: str, squares: list[Square], edges: list[tuple[int,int,V,F]], endpoint_force: F, require_strict_contacts: bool = True) -> dict:
    n=len(squares)
    for sq in squares:
        check(dot(sq.u,sq.u)==1,'physical_unit_frame')
        for p in sq.corners():check(dot(p,p)<=Q0,'physical_corner_containment')
    for s,t in combinations(squares,2):
        delta=sub(t.c,s.c)
        check(any(abs(dot(delta,e))>=s.support(e)+t.support(e) for e in (s.u,s.v,t.u,t.v)), 'physical_SAT')
    loads=[ZERO for _ in squares];force=[ZERO for _ in squares];moment=[F(0) for _ in squares]
    total_circle_weight=endpoint_force/2
    circle_atoms=[]
    for i,x in ((0,F(-2)),(1,F(2))):
        for y in (-HALF,HALF):
            circle_atoms.append((i,(x,y),endpoint_force/F(8)/total_circle_weight))
    total_power=F(0)
    for i,z,w in circle_atoms:
        check(z in squares[i].corners() and dot(z,z)==Q0,'physical_circle_atom')
        loads[i]=add(loads[i],scale(w,z))
        force[i]=add(force[i],scale(2*w,z))
        moment[i]+=2*w*dot(z,J(sub(z,squares[i].c)))
        total_power+=2*w*dot(z,squares[i].velocity(z))
    graph=[set() for _ in squares]
    for i,j,p,raw_mu in edges:
        mu=raw_mu/total_circle_weight
        check(mu>0,'physical_positive_edge')
        check(squares[i].contains(p) and squares[j].contains(p),'physical_contact_membership')
        check(dot(EX,sub(p,squares[i].c))==HALF and dot(EX,sub(p,squares[j].c))==-HALF,'physical_contact_support')
        # Actual overlap segment is positive length (strict-normal selection safe).
        yi,yj=squares[i].c[1],squares[j].c[1]
        check(abs(yi-yj)<=1,'nonempty_contact_interval')
        if require_strict_contacts:
            check(abs(yi-yj)<1,'positive_length_contact')
        for body,sign in ((i,1),(j,-1)):
            force[body]=add(force[body],scale(sign*mu,EX))
            moment[body]+=sign*mu*dot(EX,J(sub(p,squares[body].c)))
        graph[i].add(j);graph[j].add(i)
        edge_power=mu*dot(EX,sub(squares[i].velocity(p),squares[j].velocity(p)))
        check(edge_power==0,'physical_virtual_edge_zero')
        total_power+=edge_power
    check(all(f==ZERO for f in force),'physical_force_balance')
    check(all(m==0 for m in moment),'physical_torque_balance')
    check(total_power==0,'physical_virtual_identity')
    check(sum(w for _,_,w in circle_atoms)==1,'circle_normalization')
    check(sum(m!=ZERO for m in loads)==2 and add(loads[0],loads[1])==ZERO,'exact_two_loads')
    return {'name':name,'bodies':n,'positive_edges':len(edges),'circle_atoms':len(circle_atoms),
            'physical_pairs':n*(n-1)//2,'q':'17/4','all_force_torque_virtual_residuals_zero':True,
            'requires_strict_point_contact_selection':require_strict_contacts,
            'adjacency':[sorted(g) for g in graph]}

def examples() -> list[dict]:
    L=Square((F(-3,2),F(0)));R=Square((F(3,2),F(0)))
    out=[]
    out.append(check_physical('P4_staggered_two_loaded',
        [L,R,Square((-HALF,F(1,3))),Square((HALF,F(-2,5)))],
        [(0,2,(F(-1),F(0)),F(2)),(2,3,ZERO,F(2)),(3,1,(F(1),F(0)),F(2))],F(2)))
    out.append(check_physical('five_body_four_cycle_plus_bridge',
        [L,R,Square((-HALF,F(0))),Square((HALF,F(-3,5))),Square((HALF,F(3,5)))],
        [(0,2,(F(-1),F(0)),F(2)),(2,3,(F(0),F(-3,10)),F(1)),
         (2,4,(F(0),F(3,10)),F(1)),(3,1,(F(1),F(-3,10)),F(1)),
         (4,1,(F(1),F(3,10)),F(1))],F(2)))
    sqs=[L,R,Square((-HALF,-HALF)),Square((-HALF,HALF)),Square((HALF,-HALF)),Square((HALF,HALF))]
    ed=[]
    for li,ri,y in ((2,4,F(-1,4)),(3,5,F(1,4))):
        ed.extend([(0,li,(F(-1),y),F(1)),(li,ri,(F(0),y),F(1)),(ri,1,(F(1),y),F(1))])
    out.append(check_physical('simple_six_cycle',sqs,ed,F(2)))
    sqs=[L,R,Square((-HALF,F(-2,5))),Square((-HALF,F(3,5))),Square((HALF,F(-3,5))),Square((HALF,F(2,5)))]
    ed=[(0,2,(F(-1),F(-3,20)),F(2)),(0,3,(F(-1),F(3,10)),F(1)),
        (2,4,(F(0),F(-3,10)),F(1)),(2,5,ZERO,F(1)),(3,5,(F(0),F(3,10)),F(1)),
        (4,1,(F(1),F(-3,10)),F(1)),(5,1,(F(1),F(3,20)),F(2))]
    out.append(check_physical('six_body_seven_edge_component',sqs,ed,F(3)))
    # Eight-body negative control: arbitrary physical equilibrium can use
    # horizontal normals at point-only corner contacts. It is excluded by
    # the selected STRICT-normal premise, not by the general CY.TWO theorem.
    sqs=[L,R]
    ed=[]
    for y,h in ((F(-1),-HALF),(F(0),F(0)),(F(1),HALF)):
        li=len(sqs);ri=li+1
        sqs.extend([Square((-HALF,y)),Square((HALF,y))])
        ed.extend([(0,li,(F(-1),h),F(1)),(li,ri,(F(0),h),F(1)),(ri,1,(F(1),h),F(1))])
    out.append(check_physical('negative_control_eight_body_nonstrict_contact_stress',sqs,ed,F(3),False))
    return out

def connected(n: int, edges: set[tuple[int,int]], keep: set[int]|None=None) -> bool:
    keep=set(range(n)) if keep is None else keep
    if not keep:return True
    seen=set();todo=[next(iter(keep))]
    while todo:
        u=todo.pop()
        if u in seen:continue
        seen.add(u)
        todo.extend(v if u==w else w for w,v in edges if (u==w or u==v) and w in keep and v in keep)
    return seen==keep

def bipartite(n: int, edges:set[tuple[int,int]]) -> bool:
    color={}
    for root in range(n):
        if root in color:continue
        color[root]=0;todo=[root]
        while todo:
            u=todo.pop()
            for a,b in edges:
                if u not in (a,b):continue
                v=b if u==a else a
                if v in color:
                    if color[v]==color[u]:return False
                else:color[v]=1-color[u];todo.append(v)
    return True

def finite_graph_checks() -> dict:
    all_edges=list(combinations(range(4),2));by_count={4:0,5:0,6:0};residual=[]
    for mask in range(1<<6):
        edges={e for k,e in enumerate(all_edges) if mask>>k&1}
        if not connected(4,edges) or not all(connected(4,edges,set(range(4))-{v}) for v in range(4)):continue
        check(len(edges) in (4,5,6),'four_body_complete_adjacency_classification')
        by_count[len(edges)]+=1
        for loaded_mask in range(1,16):
            ls=[v for v in range(4) if loaded_mask>>v&1]
            if len(ls)<2:continue
            ne={(i,j) for i,j in combinations(range(len(ls)),2) if tuple(sorted((ls[i],ls[j]))) not in edges}
            if not connected(len(ls),ne):continue
            # Acute-load rule leaves only opposite two-loaded C4 and diamond tips.
            check(len(ls)==2,'loaded_noncontact_test')
            if len(edges)==5:
                check(not bipartite(4,edges),'diamond_two_loaded_contradiction')
            elif len(edges)==4:
                # New layered cover has no cyclic four-body graph: two interiors
                # force one body per column and exactly a three-edge path.
                check(bipartite(4,edges),'C4_sanity')
            else:
                raise AssertionError('K4 cannot pass loaded noncontact test')
            residual.append({'edges':len(edges),'loaded':ls})
    check(by_count=={4:3,5:6,6:1},'four_body_labelled_graph_counts')
    # Layered positive-contact covers: strict interval order forbids both crossing edges.
    cases=[]
    for p,q in product((1,2),repeat=2):
        poss=list(product(range(p),range(q)))
        for mask in range(1<<len(poss)):
            es={e for k,e in enumerate(poss) if mask>>k&1}
            if any(not any(i==a for a,b in es) for i in range(p)):continue
            if any(not any(j==b for a,b in es) for j in range(q)):continue
            if p==q==2 and {(0,1),(1,0)}<=es:continue
            cases.append((p,q,len(es)))
    check(set(cases)=={(1,1,1),(1,2,2),(2,1,2),(2,2,2),(2,2,3)},'two_loaded_finite_layer_inventory')
    return {'biconnected_labelled_four_body_graphs_by_edge_count':by_count,
            'acute_rule_survivor_loadings_checked':len(residual),
            'layer_inventory_up_to_reflection':['P4','C4 plus pendant bridge','C6','six vertices seven edges'],
            'scope':'All labelled four-body graph/load subsets checked; their physical exclusions rely on the analytic theorems, not graph sampling.'}

def radius_comparisons() -> None:
    lo=F(79,40);Q=F(1105,256)
    check(lo*lo-F(1,4)>F(19,10)**2,'radius_window')
    check(Q-F(1,4)<F(101,50)**2,'radius_window')
    check(F(57,40)**2>2,'radius_window')
    check(lo-F(57,40)==F(11,20),'radius_window')
    check(Q<F(21,10)**2 and F(7,5)**2<2,'radius_window')
    check(F(29,20)**2>2,'discrete_width_gaps')
    check(F(43,25)<2,'discrete_width_gaps')
    check(F(9,5)**2>2,'discrete_width_gaps')
    check(F(51,25)-1>0 and (F(51,25)-1)**2<2,'discrete_width_gaps')
    check(F(17,4)<Q,'candidate_gap')

def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit',default='LOCAL_UNCOMMITTED')
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    start=datetime.now(timezone.utc).isoformat()
    check_one_square_algebra();check_circle_signs();check_contacts();radius_comparisons()
    witnesses=examples();graphs=finite_graph_checks()
    raw=Path(__file__).read_bytes()
    report={'status':'PASS','started_utc':start,'finished_utc':datetime.now(timezone.utc).isoformat(),
      'python':platform.python_version(),'source_commit':args.source_commit,
      'source_sha256':hashlib.sha256(raw).hexdigest(),
      'source_git_blob_sha1':hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest(),
      'exact_assertions':sum(COUNTS.values()),'assertions_by_category':COUNTS,
      'physical_surviving_topology_witnesses':witnesses,'finite_graph_checks':graphs,
      'verification_scope':'Exact finite regressions; NOT a universal proof, independent full audit, Lean compilation or GitHub CI.'}
    text=json.dumps(report,indent=2)+'\n'
    if args.output:args.output.write_text(text,encoding='utf-8')
    print(text,end='')
if __name__=='__main__':main()
