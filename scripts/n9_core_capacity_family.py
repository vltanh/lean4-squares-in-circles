#!/usr/bin/env python3
"""Exact rational core/remaining-center capacity certificates.

This is a separate generalization of n9_five_core_capacity.py.  No production
five-core input is changed.  A successful certificate is conditional on the
listed actual unit-square vertices, in order, satisfying its neighborhood
premise or the direct coordinate-interval premise.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as F
import json
from math import lcm
from pathlib import Path


def need(test, message):
    if not test:
        raise ValueError(message)


def rational(value):
    need(isinstance(value, list) and len(value) == 2, "expected rational pair")
    need(all(isinstance(v, (int, str)) for v in value), "nonexact rational")
    return F(*map(int, value))


def split(box):
    a, b, c, d = box
    x, y = (a + b) / 2, (c + d) / 2
    return ((a, x, c, y), (x, b, c, y), (a, x, y, d), (x, b, y, d))


def minnorm(box):
    a, b, c, d = box
    x, y = max(a, 0, -b), max(c, 0, -d)
    return x*x + y*y


def maxdist(box, point):
    a, b, c, d = box
    x, y = point
    return max(abs(a-x), abs(b-x))**2 + max(abs(c-y), abs(d-y))**2


def inputs(data):
    need(data['version'] == 1 and data['kind'] == 'core_center_capacity',
         'unsupported certificate')
    M = rational(data['center_bound'])
    Q = rational(data['radius_squared_upper'])
    eps = rational(data['vertex_error_bound'])
    grid = data['witness_grid']
    need(M > 0 and Q > 0 and M*M + M + F(1,2) > Q,
         'center radius is not proved')
    need(0 < eps < F(1,2), 'invalid perturbation bound')
    need(isinstance(grid,int) and 1 <= grid <= 64, 'invalid witness grid')
    den = data['reference_denominator']
    need(isinstance(den,int) and den > 0, 'invalid reference denominator')
    raw = data['reference_vertices']
    need(isinstance(raw,list) and len(raw) > 0, 'empty core')
    need(len(data['reference_names']) == len(raw), 'bad core labels')
    need(all(len(row)==4 and all(len(p)==2 and all(isinstance(z,int) for z in p)
         for p in row) for row in raw), 'bad reference vertices')
    rows = [[tuple(F(z,den) for z in p) for p in row] for row in raw]
    caps = []
    for disk in data['capacity_disks']:
        need(len(disk['center'])==2, 'bad disk center')
        center = tuple(rational(z) for z in disk['center'])
        radius = rational(disk['radius'])
        need(0 < radius < F(1,2), 'disk diameter must be less than one')
        caps.append((center,radius))
    need(data['maximum_total_units']==len(rows)+len(caps), 'bad cardinality')
    return M,Q,eps,grid,rows,caps


def witnesses(rows,grid):
    result={}
    for k,row in enumerate(rows):
        for i in range(grid+1):
            for j in range(grid+1):
                u,v=F(i,grid),F(j,grid)
                w=((1-u)*(1-v),u*(1-v),u*v,(1-u)*v)
                result[k,i,j]=tuple(sum(wt*p[d] for wt,p in zip(w,row))
                                    for d in (0,1))
    return result


def verify(data):
    M,Q,eps,grid,rows,caps=inputs(data)
    points=witnesses(rows,grid)
    nodes=data['nodes'];seen=set();counts=Counter();depthmax=0;reserve=None
    need(isinstance(nodes,list) and nodes and data['root']==0,'bad root')
    def walk(index,box,depth):
        nonlocal depthmax,reserve
        need(isinstance(index,int) and 0<=index<len(nodes) and index not in seen,
             'cycle, repeated child, or bad index')
        seen.add(index);depthmax=max(depthmax,depth)
        node=nodes[index];need(isinstance(node,list) and node,'bad node')
        tag=node[0];counts[tag]+=1
        if tag=='split':
            need(len(node)==5,'split must retain all four closed children')
            for child,part in zip(node[1:],split(box)):walk(child,part,depth+1)
        elif tag=='outside':
            need(len(node)==1 and minnorm(box)>=M*M,'unproved disk exclusion')
        elif tag=='cap':
            need(len(node)==2 and isinstance(node[1],int) and 0<=node[1]<len(caps),
                 'bad cap index')
            center,radius=caps[node[1]]
            need(maxdist(box,center)<=radius*radius,'unproved cap containment')
        elif tag=='core':
            key=tuple(node[1:]);need(len(node)==4 and key in points,'bad core witness')
            r=(F(1,2)-eps)**2-maxdist(box,points[key])
            need(r>0,'unproved core exclusion')
            reserve=r if reserve is None else min(reserve,r)
        else:raise ValueError('unknown node tag')
    walk(0,(-M,M,-M,M),0)
    need(len(seen)==len(nodes),'unreachable certificate nodes')
    return {'status':'EXACT CONDITIONAL CORE CAPACITY VERIFIED','nodes':len(nodes),
            'leaves':len(nodes)-counts['split'],'max_depth':depthmax,
            'node_counts':dict(sorted(counts.items())),
            'minimum_core_squared_reserve':str(reserve),
            'core_squares':len(rows),'maximum_other_units':len(caps),
            'maximum_total_units':len(rows)+len(caps),
            'original_row_closed':False,'Lean_verification_claimed':False}


def regenerate(data,max_depth=15):
    M,Q,eps,grid,rows,caps=inputs(data)
    points=witnesses(rows,grid);nodes=[]
    def visit(box,depth):
        index=len(nodes);nodes.append(None)
        cap=next((i for i,(c,r) in enumerate(caps) if maxdist(box,c)<=r*r),None)
        if cap is not None:nodes[index]=['cap',cap]
        elif minnorm(box)>=M*M:nodes[index]=['outside']
        else:
            key=min(points,key=lambda k:maxdist(box,points[k]))
            if maxdist(box,points[key])<(F(1,2)-eps)**2:nodes[index]=['core',*key]
            else:
                need(depth<max_depth,'unresolved spatial cell at depth limit')
                nodes[index]=['split',*(visit(b,depth+1) for b in split(box))]
        return index
    visit((-M,M,-M,M),0)
    result=dict(data,nodes=nodes,root=0)
    verify(result)
    return result


_CACHE={}


def verify_actual_vertex_dyadic_boxes(data,vertex_boxes,precision_bits=44):
    """Check all actual witnesses, with integer arithmetic in the hot loop.

    Raw endpoints z represent z/2**precision_bits.  The caller proves actual
    vertex membership; a false return means only that this entry was unproved.
    """
    need(isinstance(precision_bits,int) and 1<=precision_bits<=256,'bad precision')
    key=(json.dumps(data,sort_keys=True,separators=(',',':')),precision_bits)
    if key not in _CACHE:
        verify(data)
        M,Q,eps,grid,rows,caps=inputs(data);leaves=[]
        def walk(index,box):
            node=data['nodes'][index]
            if node[0]=='split':
                for child,part in zip(node[1:],split(box)):walk(child,part)
            elif node[0]=='core':
                k,i,j=node[1:];weights=((grid-i)*(grid-j),i*(grid-j),i*j,(grid-i)*j)
                den=(1<<precision_bits)*grid*grid
                D=lcm(den,*(z.denominator for z in box))
                leaves.append((index,k,weights,D//den,tuple(int(z*D) for z in box),D))
        walk(0,(-M,M,-M,M))
        _CACHE[key]=(len(rows),leaves)
    n,leaves=_CACHE[key]
    need(len(vertex_boxes)==n and all(len(row)==4 for row in vertex_boxes),
         'wrong actual core shape')
    need(all(len(p)==2 and all(len(z)==2 and all(isinstance(t,int) for t in z)
         and z[0]<=z[1] for z in p) for row in vertex_boxes for p in row),
         'invalid actual vertex dyadic intervals')
    minimum=None
    for index,k,weights,factor,box,D in leaves:
        lows=[factor*sum(w*p[d][0] for w,p in zip(weights,vertex_boxes[k])) for d in (0,1)]
        highs=[factor*sum(w*p[d][1] for w,p in zip(weights,vertex_boxes[k])) for d in (0,1)]
        a,b,c,d=box
        dx=max(abs(a-highs[0]),abs(b-lows[0]))
        dy=max(abs(c-highs[1]),abs(d-lows[1]))
        margin=D*D-4*(dx*dx+dy*dy)
        if margin<=0:return {'verified':False,'first_failing_core_leaf':index}
        minimum=margin if minimum is None else min(minimum,margin)
    return {'verified':True,'checked_core_leaves':len(leaves),
            'minimum_positive_scaled_reserve':minimum}


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('certificate',type=Path)
    ap.add_argument('--regenerate',action='store_true')
    args=ap.parse_args();data=json.loads(args.certificate.read_text())
    if args.regenerate:data=regenerate(data)
    print(json.dumps(verify(data),indent=2))
