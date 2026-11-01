#!/usr/bin/env python3
"""Independent standard-library checker for the ten-row three-cell hand table.

No producer or pose-graph module is imported. Reconstruct every polygon using
feasible line intersections, every necessary separator alternative from tangent
linear equations, and every nonnegative dual identity using Fraction arithmetic.
"""
from fractions import Fraction as F
from itertools import combinations,product
from math import gcd,isqrt,lcm
from pathlib import Path
import argparse,copy,hashlib,json
HERE=Path(__file__).resolve().parent


def need(ok,message):
    if not ok:raise ValueError(message)
def below(x):return x.numerator//x.denominator
def above(x):return -((-x.numerator)//x.denominator)
def ceiling_root(x):
    r=isqrt(x.numerator//x.denominator)
    if r*r*x.denominator<x.numerator:r+=1
    need(r*r*x.denominator>=x.numerator and (r==0 or (r-1)**2*x.denominator<x.numerator),'root bound')
    return r


def independent_support(normals,k,d):
    ends=[(F(1)-F(2*i*i,k*k+i*i),F(2*k*i,k*k+i*i)) for i in range(k+1)]
    table=[]
    for i in range(k):
        row=[]
        for x,y in normals:
            n2=x*x+y*y;candidates=[]
            for a,b in ends[i:i+2]:
                projections=sorted((abs(a*x+b*y),abs(a*y-b*x)))
                small,large=projections
                if F(1105,64)*small*small<=n2:
                    z=ceiling_root(F(1041,256)*(large*d)**2)-below(large*d/2)
                else:z=ceiling_root(F(1105,256)*n2*d*d)-below((large+small)*d/2)
                candidates.append(z)
            X,Y=x,y
            while X<0 or Y<0:X,Y=-Y,X
            a,b=ends[i];A,B=ends[i+1]
            if b*X<=a*Y and A*Y<=B*X:
                candidates.append(ceiling_root(F(1041,256)*n2*d*d)-isqrt(n2*d*d//4))
            row.append(max(candidates))
        table.append(row)
    return ends,table


def supporting_lines(points):
    lines=set()
    for p,q in combinations(points,2):
        a,b=q[1]-p[1],p[0]-q[0]
        if a==b==0:continue
        v=a*p[0]+b*p[1];dots=[a*x+b*y for x,y in points];g=gcd(abs(a),abs(b))
        if max(dots)<=v:lines.add((a//g,b//g,F(v,g)))
        if min(dots)>=v:lines.add((-a//g,-b//g,F(-v,g)))
    return sorted(lines)


def vertices(lines):
    out=set()
    for (a,b,c),(u,v,w) in combinations(lines,2):
        det=a*v-u*b
        if not det:continue
        X=(c*v-w*b)/det;Y=(a*w-u*c)/det
        if all(A*X+B*Y<=C for A,B,C in lines):out.add((X,Y))
    return sorted(out)


def independent_domains(normals,bounds,k,d):
    axial={0:(-2,0),3:(-1,-1),7:(0,-2)}
    hexv=sorted((x,y) for x in range(-2,3) for y in range(-1,2)
                if (abs(x)==2 and y==0) or (abs(x)==abs(y)==1))
    low,high=F(433,250),F(1733,1000)
    need(low*low<3<high*high,'sqrt3 range')
    domains={}
    for c,(q,r) in axial.items():
        points=set()
        for x,y in hexv:
            X=F(49*d,200)*(3*q+x)
            Y=F(49*d,200)*(q+2*r+y)
            l,h=sorted((Y*low,Y*high))
            points.update(product((below(X),above(X)),(below(l),above(h))))
        initial=supporting_lines(sorted(points))
        for i in range(k):
            lines=sorted(set(initial+[(a,b,F(z)) for (a,b),z in zip(normals,bounds[i])]))
            pts=vertices(lines);need(pts,'empty domain unsupported in this certificate')
            domains[c,i]=(lines,pts)
    return domains


def independent_alternatives(i,neighbor,domains,ends,k,d):
    merged={}
    for j in range(k):
        P=domains[neighbor,j][1]
        for owner,partner in ((i,j),(j,i)):
            u,v=ends[owner:owner+2];det=u[0]*v[1]-u[1]*v[0]
            need(det>0,'nonempty angle arc')
            tangent=((v[1]-u[1])/det,(u[0]-v[0])/det)
            for z in (u,tangent,v):
                if owner==partner:H=F(2)
                else:
                    vals=[]
                    for w in ends[partner:partner+2]:
                        dot=z[0]*w[0]+z[1]*w[1];sine=z[0]*w[1]-z[1]*w[0]
                        vals.append(1+dot+(sine if owner<partner else -sine))
                    H=min(vals)
                for nx,ny in (z,(-z[1],z[0])):
                    for sign in (-1,1):
                        x,y=sign*nx,sign*ny
                        B=d*H/2+min(x*X+y*Y for X,Y in P)
                        den=lcm(x.denominator,y.denominator)
                        a,b=int(x*den),int(y*den);div=gcd(abs(a),abs(b))
                        a//=div;b//=div;B*=F(den,div)
                        merged[a,b]=min(B,merged.get((a,b),B))
    return [(a,b,B) for (a,b),B in sorted(merged.items())]


def check_dual(proof,lines,objective,bound,strict):
    need(set(proof)=={'terms','weighted_bound'},'dual fields')
    need(1<=len(proof['terms'])<=2,'dual size')
    seen=set();X=Y=Z=F(0)
    for index,weight in proof['terms']:
        need(type(index) is int and 0<=index<len(lines) and index not in seen,'dual line index')
        seen.add(index);w=F(weight);need(w>=0,'negative multiplier')
        a,b,c=lines[index];X+=w*a;Y+=w*b;Z+=w*c
    need((X,Y)==tuple(objective),'wrong combined dual normal')
    need(Z==F(proof['weighted_bound']),'wrong weighted constant')
    need(Z<bound if strict else Z<=bound,'dual bound does not imply claimed inequality')


def verify(cert):
    need(cert['schema']=='n9_three_cell_rational_table_v1' and cert['target_q']=='1105/256'
         and cert['scope']=='q<=Q','theorem scope')
    need(cert['cells']==[0,3,7] and cert['scale']==1000 and cert['angle_intervals']==10,'complete domains')
    need(cert['sqrt3_enclosure']==['433/250','1733/1000'],'algebraic enclosure')
    normals=((-2,-1),(-1,-2),(-1,0),(1,-3));k=10;d=1000
    need(cert['normals']==[list(n) for n in normals],'support directions')
    ends,bounds=independent_support(normals,k,d);need(bounds==cert['support_bounds'],'support table wrong')
    domains=independent_domains(normals,bounds,k,d)
    need(len(cert['domains'])==30,'missing center domain')
    for row,(key,(lines,pts)) in zip(cert['domains'],domains.items()):
        c,i=key;need((row['cell'],row['arc'])==(c,i),'domain identity/order')
        need(row['lines']==[[a,b,str(v)] for a,b,v in lines],'incorrect domain inequalities')
        need([[F(x),F(y)] for x,y in row['vertices']]==[list(p) for p in pts],'polygon reconstruction mismatch')
    need(len(cert['rows'])==k,'missing orientation interval')
    totals=Counter();summary=[]
    for i,row in enumerate(cert['rows']):
        need(row['arc']==i and set(row['branches'])=={'0','7'},'row cover')
        e=tuple(row['direction']);need(len(e)==2 and all(type(x) is int for x in e) and any(e),'table direction')
        U,L=row['upper_left'],row['lower_right'];need(type(U) is int and type(L) is int and U<L,'no strict table gap')
        lines,C=domains[3,i]
        counts=[]
        for neighbor in (0,7):
            alternatives=independent_alternatives(i,neighbor,domains,ends,k,d)
            proofs=row['branches'][str(neighbor)]
            need(len(proofs)==len(alternatives),'missing separator alternative')
            actual_extreme=None;reachable=0
            for proof,(a,b,B) in zip(proofs,alternatives):
                need(proof['normal']==[a,b] and F(proof['rhs'])==B,'separator branch identity')
                if proof['kind']=='impossible':
                    check_dual(proof['dual'],lines,(a,b),B,True);totals['impossible_duals']+=1
                elif proof['kind']=='bound':
                    all_lines=lines+[(-a,-b,-B)];pts=vertices(all_lines)
                    need(pts,'bound branch is empty or incorrectly retained')
                    obj=e if neighbor==0 else (-e[0],-e[1]);target=U if neighbor==0 else -L
                    check_dual(proof['dual'],all_lines,obj,F(target),False);totals['bound_duals']+=1;reachable+=1
                    value=max(e[0]*x+e[1]*y for x,y in pts) if neighbor==0 else min(e[0]*x+e[1]*y for x,y in pts)
                    if actual_extreme is None:actual_extreme=value
                    else:actual_extreme=max(actual_extreme,value) if neighbor==0 else min(actual_extreme,value)
                else:raise ValueError('unsupported branch status')
            field='exact_upper_left' if neighbor==0 else 'exact_lower_right'
            need(actual_extreme is not None and actual_extreme==F(row[field]),'wrong exact table endpoint')
            counts.append(reachable)
        summary.append({'arc':i,'direction':list(e),'upper_left':U,'lower_right':L,'strict_gap':L-U,
                        'reachable_left_branches':counts[0],'reachable_right_branches':counts[1]})
    need(cert['global_lower_bound_proved'] is False,'unsupported global flag')
    return summary,dict(totals)


from collections import Counter

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--directory',type=Path,default=HERE)
    ap.add_argument('--negative-controls',action='store_true');args=ap.parse_args();d=args.directory
    raw=(d/'three_cell_rational_table.json').read_bytes();cert=json.loads(raw)
    rows,totals=verify(cert);rejected=[]
    def reject(name,fun):
        try:fun()
        except (ValueError,IndexError,KeyError):rejected.append(name)
        else:raise ValueError('mutation accepted: '+name)
    if args.negative_controls:
        bad=copy.deepcopy(cert);bad['support_bounds'][0][0]-=1
        reject('too-small center support',lambda:verify(bad))
        bad=copy.deepcopy(cert);bad['rows'].pop()
        reject('missing orientation interval',lambda:verify(bad))
        bad=copy.deepcopy(cert);bad['rows'][0]['branches']['0'].pop()
        reject('omitted separator alternative',lambda:verify(bad))
        bad=copy.deepcopy(cert);bad['rows'][0]['upper_left']=bad['rows'][0]['lower_right']
        reject('nonpositive table gap',lambda:verify(bad))
        bad=copy.deepcopy(cert);bad['rows'][0]['branches']['0'][0]['dual']['terms'][0][1]='-1'
        reject('negative dual multiplier',lambda:verify(bad))
        bad=copy.deepcopy(cert);bad['rows'][0]['branches']['0'][0]['rhs']='9999999'
        reject('changed physical separator threshold',lambda:verify(bad))
    base=json.loads((d/'hex_root_manifest.json').read_text());old=json.loads((d/'disk_support_root_manifest.json').read_text())
    masks={sum(1<<p[c] for c in (0,3,7)) for p in base['symmetries']}
    covered=[r for r in old['roots'] if any(r['mask']&m==m for m in masks)]
    report={'result':'PASS','arithmetic':'Fraction and Python integers only; no graph or numerical optimizer',
        'theorem':'No q<=1105/256 physical triple in cells 0,3,7','angle_arcs':10,'support_normals':4,
        'position_mesh_used':False,'table_rows':rows,**totals,'dual_rows':sum(totals.values()),
        'minimum_scaled_gap':min(r['strict_gap'] for r in rows),'scale':1000,
        'symmetry_images':len(masks),'roots_covered':len(covered),
        'new_vs_3c88e21':sum(r['status']=='OPEN' for r in covered),
        'negative_controls_rejected':rejected,'certificate_sha256':hashlib.sha256(raw).hexdigest(),
        'source_sha256':{p:hashlib.sha256((HERE/p).read_bytes()).hexdigest() for p in ['make_three_cell_table.py','verify_three_cell_table.py']},
        'global_lower_bound_proved':False,'full_equality_classified':False,'separate_human_review_performed':False,'lean_or_ci_run':False}
    (d/'three_cell_table_verification_report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
