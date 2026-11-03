#!/usr/bin/env python3
"""Independent rational leaf replay for the full-nine bulk LP discovery.

This file imports neither a producer nor a numerical optimizer.  Every angle
and position interval is reconstructed from its split path.  Physical rows are
then regenerated with directed rational bounds.  A successful sample replay
does NOT assert complete coverage; the discovery frontier is reported.
"""
from fractions import Fraction as F
from functools import lru_cache
from math import gcd, isqrt
from pathlib import Path
import argparse, hashlib, json, time

Q=F(1105,256); RHO=F(91,60); A=F(46); B=F(27,2)
BITS=48; DEN=1<<BITS
DIRS=tuple((x,y) for x in range(-3,4) for y in range(-3,4)
           if (x or y) and gcd(x,y)==1)
EDGES=((0,1,0),(1,2,0),(2,3,1),(4,5,0),(5,6,0))
AL=lambda i:18+i
BE=lambda i:27+i
AB=lambda i:36+i
GI=lambda i:45+i
DENSE_HALF_TANGENTS=(0,1609,3220,4834,6455,8083,9721,11372,13036,14717,
    16416,18136,19880,21650,23449,25280,27146,29050,30996,32988,
    35030,37126,39281,41500,43790,46156,48605,51145,53784,56532,59398,62395)
def dense_directions():
    scale=1<<16;out=[]
    for turn in range(4):
        for num in DENSE_HALF_TANGENTS:
            den=scale*scale+num*num
            p=F(scale*scale-num*num,den);q=F(2*scale*num,den)
            for _ in range(turn):p,q=-q,p
            assert p*p+q*q==1;out.append((p,q))
    assert len(out)==len(set(out))==128
    return tuple(out)
DENSE_DIRS=dense_directions()

def down(x):
    x=F(x); return F((x*DEN).numerator//(x*DEN).denominator,DEN)
def up(x): return -down(-F(x))
@lru_cache(maxsize=20000)
def roots(x):
    x=F(x); assert x>=0
    n=isqrt((x.numerator<<(2*BITS))//x.denominator)
    lo=F(n,DEN); return lo,lo if lo*lo==x else F(n+1,DEN)
def quotient(n,d):
    lo,hi=roots(d); assert n>=0 and lo>0
    return down(n/hi),up(n/lo)
@lru_cache(maxsize=20000)
def h_bounds(T):
    l,u=T; vv=[quotient(1+abs(t),1+t*t) for t in (l,u)]
    return (F(1,2) if l<=0<=u else min(z[0]/2 for z in vv)),max(z[1]/2 for z in vv)
@lru_cache(maxsize=20000)
def normal_bounds(T,axis=0,sg=1):
    l,u=T; small=F(0) if l<=0<=u else min(abs(l),abs(u)); big=max(abs(l),abs(u))
    aa=(quotient(1,1+big*big)[0],quotient(1,1+small*small)[1])
    def sine(t):
        lo,hi=quotient(abs(t),1+t*t)
        return (lo,hi) if t>=0 else (-hi,-lo)
    bb=(sine(l)[0],sine(u)[1])
    if axis: aa,bb=(-bb[1],-bb[0]),aa
    if sg<0: aa,bb=(-aa[1],-aa[0]),(-bb[1],-bb[0])
    return aa,bb
@lru_cache(maxsize=20000)
def support_lower(T,U):
    if max(T[0],U[0])<=min(T[1],U[1]): return F(1)
    vv=[quotient(1+t*u+abs(t-u),(1+t*t)*(1+u*u))[0]
        for t,u in ((T[0],U[1]),(T[1],U[0]))]
    return (1+min(vv))/2
def beta_lower(T):
    l,u=T; m=F(0) if l<=0<=u else min(abs(l),abs(u))
    return quotient(m,1+m*m)[0]
def mulup(U,V): return max(u*v for u in U for v in V)

def reconstruct(path):
    box=[(F(-1),F(1)) for _ in range(9)]
    pos=[(-RHO,RHO) for _ in range(18)]; choices=[]; seen=set()
    for step in path:
        kind=step[0]
        if kind in ('angle','position'):
            assert len(step)==3
            k,side=step[1:]; assert type(k) is int and type(side) is int and side in (0,1)
            target=box if kind=='angle' else pos; assert 0<=k<len(target)
            l,u=target[k];m=(l+u)/2;target[k]=(l,m) if side==0 else (m,u)
        else:
            assert kind in ('proxy','sat') and len(step)==3
            pair=tuple(step[1]); choice=tuple(step[2]); assert len(pair)==2
            i,j=pair; assert 0<=i<j<9 and (pair,kind) not in seen
            seen.add((pair,kind))
            if kind=='proxy': assert choice in ((0,-1),(0,1),(1,-1),(1,1))
            else: assert len(choice)==3 and choice[0] in pair and choice[1] in (0,1) and choice[2] in (-1,1)
            choices.append((pair,kind,choice))
    return tuple(box),tuple(pos),tuple(choices)

def effective_boxes(box,choices,version=None):
    box=list(box)
    assert version in (None,'left_angles_7_40_v1')
    if version is not None:
        # Actual A-B-C spans plus the C-D inset give h_A+h_B<=R-1.
        # R<133/64, each h>=1/2, and h(7/40)>37/64.
        assert F(133,64)**2>Q and 1504**2-37**2*1649==4535>0
        for owner in (0,1):
            l,u=box[owner];ll=max(l,-F(7,40));uu=min(u,F(7,40))
            if ll>uu:return None,'accepted original A/B angle bound'
            box[owner]=(ll,uu)
    for pair,kind,ch in choices:
        if kind!='sat': continue
        owner,axis,sg=ch
        if pair==(2,3):
            if sg<0: return None,'strict weak cone excludes backward/downward steep normal'
            if box[3][0]>=0 and owner==2:
                if axis==1:return None,'accepted positive-D excludes a steep C-owned normal'
                if box[2][1]<=0:return None,'accepted positive-D excludes a downward/horizontal C-owned normal'
            if axis==1:
                l,u=box[owner]
                if l>=0: return None,'strict weak cone upward steep normal requires negative tilt'
                box[owner]=(l,min(u,F(0)))
        if pair==(3,6):
            if axis==1 and sg<0: return None,'accepted D/G separator has positive vertical component'
            if axis==0:
                l,u=box[owner]
                if sg>0:
                    if u<=0: return None,'accepted D/G separator has positive vertical component'
                    box[owner]=(max(l,F(0)),u)
                else:
                    if l>=0: return None,'accepted D/G separator has positive vertical component'
                    box[owner]=(l,min(u,F(0)))
    return tuple(box),None

def center_bounds(box,pos,choices):
    hs=tuple(h_bounds(T) for T in box); gs=tuple(down(F(1,4)/h[1]) for h in hs)
    X=[list(pos[2*i]) for i in range(9)];Y=[list(pos[2*i+1]) for i in range(9)]
    X[2][0]=max(X[2][0],hs[2][0]-F(1,60));X[3][0]=max(X[3][0],F(4,3))
    X[2][1]=min(X[2][1],hs[2][1]+F(5,64));X[6][0]=max(X[6][0],hs[6][0]+F(101,432))
    def empty(): return any(l>u for l,u in X+Y)
    for _ in range(16):
        for i,j,bit in EDGES:
            g=gs[i]+gs[j] if bit else hs[i][0]+hs[j][0]
            X[j][0]=max(X[j][0],X[i][0]+g);X[i][1]=min(X[i][1],X[j][1]-g)
        X[7][1]=min(X[7][1],X[8][1]);X[8][0]=max(X[8][0],X[7][0])
        for pair,kind,ch in choices:
            if kind!='proxy':continue
            i,j=pair;axis,sg=ch;coords=(X,Y)[axis]
            if sg<0:i,j=j,i
            g=gs[i]+gs[j]
            coords[j][0]=max(coords[j][0],coords[i][0]+g);coords[i][1]=min(coords[i][1],coords[j][1]-g)
        if empty(): return None,hs,gs,'empty propagated original center interval'
        for axis in (0,1):
            along,across=(X,Y) if axis==0 else (Y,X)
            for i in range(9):
                hlo,hhi=hs[i];klo=roots(max(F(0),F(1,2)-hhi*hhi))[0];xl,xu=along[i]
                xlo=F(0) if xl<=0<=xu else min(abs(xl),abs(xu))
                aa=Q-(xlo+hlo)**2;bb=Q-(xlo+klo)**2;cc=RHO*RHO-xlo*xlo
                if aa<0 or bb<0 or cc<0:
                    return None,hs,gs,'original circle/center-radius envelope has negative square reserve'
                cap=min(max(roots(aa)[1]-klo,roots(bb)[1]-hlo),roots(cc)[1])
                across[i][0]=max(across[i][0],-cap);across[i][1]=min(across[i][1],cap)
        Y[3][0]=max(Y[3][0],Y[2][0]+F(5,8));Y[2][1]=min(Y[2][1],Y[3][1]-F(5,8))
        dg=F(8,15)+F(7,8)*(hs[3][0]+hs[6][0]-1)
        Y[6][0]=max(Y[6][0],Y[3][0]+dg);Y[3][1]=min(Y[3][1],Y[6][1]-dg)
        for i,j,bit in EDGES:
            dxhi=X[j][1]-X[i][0]
            Y[j][0]=max(Y[j][0],Y[i][0]-dxhi);Y[j][1]=min(Y[j][1],Y[i][1]+dxhi)
            Y[i][0]=max(Y[i][0],Y[j][0]-dxhi);Y[i][1]=min(Y[i][1],Y[j][1]+dxhi)
        if empty():return None,hs,gs,'empty propagated original center interval'
    return tuple(tuple(v) for i in range(9) for v in (X[i],Y[i])),hs,gs,None

def difference_bounds(pair,cb,gs):
    i,j=pair;dr=[]
    for xy in (0,1):
        lo=cb[2*j+xy][0]-cb[2*i+xy][1];hi=cb[2*j+xy][1]-cb[2*i+xy][0]
        if pair==(2,3):lo=max(lo,gs[2]+gs[3] if xy==0 else F(5,8));hi=min(hi,F(31,30))
        if pair==(3,6) and xy==0:lo=max(lo,-F(1459,1728));hi=min(hi,F(1459,1728))
        if pair==(3,6) and xy==1:lo=max(lo,F(0))
        dr.append((lo,hi))
    return dr

def replay_leaf(leaf):
    box,pos,choices=reconstruct(leaf['path']);box,terminal=effective_boxes(box,choices,leaf.get('context_version'))
    if terminal:return None,terminal
    cb,hs,gs,terminal=center_bounds(box,pos,choices)
    if terminal:return None,terminal
    for pair,kind,ch in choices:
        if kind=='sat' and any(l>u for l,u in difference_bounds(pair,cb,gs)):
            return None,'empty original center-difference interval before any bilinear row'
    weights={}
    assert leaf['power']==40
    for index,weight in leaf['weights']:
        assert type(index) is int and index>=0 and type(weight) is int and weight>0 and index not in weights
        weights[index]=weight
    n=54+6*sum(kind=='sat' for _,kind,_ in choices)
    rr=[F(0)]*n;bb=F(0);index=0;used=[]
    def add(entries,rhs,name):
        nonlocal index,bb
        if index in weights:
            w=weights[index];bb+=w*F(rhs);used.append(name)
            for k,c in entries:rr[k]+=w*F(c)
        index+=1
    def product_rows(z,U,V,UB,VB,name):
        ul,uu=UB;vl,vu=VB
        def scale(E,c):return [(i,c*v) for i,v in E]
        add([(z,-1)]+scale(V,ul)+scale(U,vl),ul*vl,name+'_lower_ll')
        add([(z,-1)]+scale(V,uu)+scale(U,vu),uu*vu,name+'_lower_uu')
        add([(z,1)]+scale(V,-uu)+scale(U,-vl),-uu*vl,name+'_upper_ul')
        add([(z,1)]+scale(V,-ul)+scale(U,-vu),-ul*vu,name+'_upper_lu')
    for k,(l,u) in enumerate(cb):add([(k,1)],u,'bound_up_'+str(k));add([(k,-1)],-l,'bound_lo_'+str(k))
    for i,(tl,tu) in enumerate(box):
        aa,be=normal_bounds(box[i]);abl=(beta_lower(box[i]),max(abs(be[0]),abs(be[1])))
        for var,bd in ((AL(i),aa),(BE(i),be),(AB(i),abl),(GI(i),(gs[i],up(F(1,4)/hs[i][0])))):
            add([(var,1)],bd[1],'pose_up_'+str(var));add([(var,-1)],-bd[0],'pose_lo_'+str(var))
        add([(AL(i),-1),(AB(i),-1)],-2*hs[i][0],'width_lower')
        add([(AL(i),1),(AB(i),1)],2*hs[i][1],'width_upper')
        add([(AB(i),1),(AL(i),-1)],0,'fold_order')
        for ax in (0,1):
            for sg in (-1,1):add([(2*i+ax,sg),(AL(i),F(1,2)),(AB(i),F(1,2))],roots(Q)[1],'axis_support_shared_width')
        add([(BE(i),1),(AB(i),-1)],0,'abs_pos');add([(BE(i),-1),(AB(i),-1)],0,'abs_neg')
        if tl>=0:add([(AB(i),1),(BE(i),-1)],0,'abs_equal_pos')
        elif tu<=0:add([(AB(i),1),(BE(i),1)],0,'abs_equal_neg')
        else:
            bl,bu=be;slope=(bu+bl)/(bu-bl);intercept=-2*bu*bl/(bu-bl)
            add([(AB(i),1),(BE(i),-slope)],intercept,'abs_chord')
        for p,q in DIRS:add([(AL(i),p),(BE(i),q)],roots(p*p+q*q)[1],'unit_disk')
        left=normal_bounds((tl,tl));right=normal_bounds((tu,tu))
        nm=[F(round((sum(left[k])+sum(right[k]))/2*(1<<30)),1<<30) for k in (0,1)]
        assert nm[0]>0 and nm[0]>=abs(nm[1])
        low=min(sum(min(nm[k]*z for z in endpoint[k]) for k in (0,1)) for endpoint in (left,right))
        add([(AL(i),-nm[0]),(BE(i),-nm[1])],-low,'arc_chord')
        for ss in (F(1),F(9,8),F(5,4),F(11,8),F(3,2)):
            co=-1/(2*ss*ss);add([(GI(i),-1),(AL(i),co),(AB(i),co)],-1/ss,'inset_tangent')
        for p,q in DIRS:
            bound=roots(Q*(p*p+q*q))[1]
            for s in (-1,1):
                for t in (-1,1):add([(2*i,p),(2*i+1,q),(AL(i),F(s*p+t*q,2)),(BE(i),F(s*q-t*p,2))],bound,'corner_support')
    for i,j,bit in EDGES:
        for sy in (-1,1):add([(2*i,1),(2*j,-1),(2*i+1,sy),(2*j+1,-sy)],0,'cone')
        widths=[(GI(i),1),(GI(j),1)] if bit else [(AL(i),F(1,2)),(AB(i),F(1,2)),(AL(j),F(1,2)),(AB(j),F(1,2))]
        add([(2*i,1),(2*j,-1)]+widths,0,'chain')
    add([(6,1),(4,-1),(AL(2),-F(1,2)),(AB(2),-F(1,2)),(AL(3),-F(1,2)),(AB(3),-F(1,2))],0,'CD_weak')
    add([(5,1),(7,-1)],-F(5,8),'CD_big_transverse')
    add([(7,1),(13,-1)],0,'accepted_G_above_D')
    add([(7,1),(13,-1),(AL(3),F(7,16)),(AB(3),F(7,16)),(AL(6),F(7,16)),(AB(6),F(7,16))],F(41,120),'DG_width_clearance')
    add([(12,-1),(AL(6),F(1,2)),(AB(6),F(1,2))],-F(101,432),'accepted_G_edge')
    add([(4,1),(AL(2),-F(1,2)),(AB(2),-F(1,2))],F(5,64),'accepted_C_edge')
    add([(14,1),(16,-1)],0,'extras_x_order')
    add([(4,-A),(12,-B),(AL(2),A/2),(AB(2),A/2),(AL(6),B/2),(AB(6),B/2)],-F(27,4),'left_cap_and_chains')
    add([(6,1),(12,-1)],F(1459,1728),'DG_horizontal_cap')
    add([(6,-1),(12,1)],F(1459,1728),'DG_horizontal_cap_other')
    for i in range(9):
        for j in range(9):
            if i==j:continue
            pose=[(AL(i),-A/2),(AB(i),-A/2+4),(AL(j),-B/2),(AB(j),-B/2)]
            for axis in (0,1):
                for sg in (-1,1):add([(2*i+axis,sg*A),(2*j+axis,sg*B)]+pose,F(211,4),'all_pair_cap')
    budget=[(AL(1),A),(AB(1),A),(AL(2),A/2),(AB(2),A/2),(GI(2),A),(AL(5),B),(AB(5),B),(AB(0),4),(AB(3),4),(AL(3),-A/2),(AB(3),-A/2),(GI(3),A)]
    add(budget,2*A+B,'orientation_budget')
    if box[3][0]>=0:
        k=F(207,16)
        add([(6,A),(12,B),(AL(3),A/2),(BE(3),A/2-k),(AL(6),-B/2),(AB(6),-B/2)],F(211,4)+A,'signed_right_cap')
        add(budget+[(AB(3),-4),(AL(3),A),(BE(3),A-k)],3*A+B,'signed_orientation_budget')
    cursor=54
    for pair,kind,ch in choices:
        i,j=pair
        if kind=='proxy':
            ax,sg=ch;add([(2*i+ax,sg),(2*j+ax,-sg),(GI(i),1),(GI(j),1)],0,'proxy')
            continue
        owner,ax,sg=ch;nn=normal_bounds(box[owner],ax,sg)
        nm=[F(round((l+u)/2*(1<<30)),1<<30) for l,u in nn]
        dr=difference_bounds(pair,cb,gs);assert all(l<=u for l,u in dr)
        d0=[F(round((l+u)/2*(1<<30)),1<<30) for l,u in dr]
        add([],sum(mulup(nn[k],dr[k]) for k in (0,1))-support_lower(box[i],box[j]),'sep_projection_upper')
        error=sum(mulup((nn[k][0]-nm[k],nn[k][1]-nm[k]),(dr[k][0]-d0[k],dr[k][1]-d0[k])) for k in (0,1))
        pose=[(AL(owner),-sg*d0[0]),(BE(owner),-sg*d0[1])] if ax==0 else [(BE(owner),sg*d0[0]),(AL(owner),-sg*d0[1])]
        if pair==(3,6):add([(BE(owner),-sg)] if ax==0 else [(AL(owner),-sg)],0,'accepted_DG_normal_up')
        add([(2*i,nm[0]),(2*i+1,nm[1]),(2*j,-nm[0]),(2*j+1,-nm[1])]+pose,-support_lower(box[i],box[j])+error-sum(d0[k]*nm[k] for k in (0,1)),'sep')
        z=list(range(cursor,cursor+6));cursor+=6
        normal=[[(AL(owner),sg)],[(BE(owner),sg)]] if ax==0 else [[(BE(owner),-sg)],[(AL(owner),sg)]]
        for xy in (0,1):product_rows(z[xy],normal[xy],[(2*j+xy,1),(2*i+xy,-1)],nn[xy],dr[xy],'product_nd')
        ai,bi=normal_bounds(box[i]);aj,bj=normal_bounds(box[j])
        for target,U,V,UB,VB in ((z[2],AL(i),AL(j),ai,aj),(z[3],BE(i),BE(j),bi,bj),(z[4],AL(i),BE(j),ai,bj),(z[5],BE(i),AL(j),bi,aj)):
            product_rows(target,[(U,1)],[(V,1)],UB,VB,'product_frame')
        for signed in (-1,1):add([(z[0],-2),(z[1],-2),(z[2],1),(z[3],1),(z[4],signed),(z[5],-signed)],-1,'full_physical_sep')
        add([(z[0],-1),(z[1],-1)],-support_lower(box[i],box[j]),'full_physical_sep_req')
        add([(z[2],-1),(z[3],-1)],0,'relative_cos_nonnegative')
        add([(z[2],1),(z[3],1)],1,'relative_cos_upper')
        for signed in (-1,1):add([(z[4],signed),(z[5],-signed)],1,'relative_sin_bound')
    # Appended folded-arc hull rows are necessary for the same original frame.
    assert F(17,12)**2>2
    for i in range(9):
        add([(AL(i),-1),(AB(i),-F(5,12))],-1,'folded_rational_chord')
        for p,q in DIRS:
            if p>=0 and q>=0:add([(AL(i),p),(AB(i),q)],roots(p*p+q*q)[1],'folded_unit_support')
    add([(1,1),(GI(0),-1)],-F(3,40),'left_main_inset_barrier_up')
    add([(1,-1),(GI(0),-1)],-F(3,40),'left_main_inset_barrier_down')
    for i in range(9):
        for p,q in DIRS:add([(2*i,p),(2*i+1,q)],RHO*roots(p*p+q*q)[1],'original_center_disk')
        for j in range(i+1,9):
            ll,uu=cb[2*j][0]-cb[2*i][1],cb[2*j][1]-cb[2*i][0]
            vv,ww=cb[2*j+1][0]-cb[2*i+1][1],cb[2*j+1][1]-cb[2*i+1][0]
            assert ll<=uu and vv<=ww
            add([(2*i,ll+uu),(2*j,-ll-uu),(2*i+1,vv+ww),(2*j+1,-vv-ww)],-1-ll*uu-vv*ww,'original_center_distance_secant')
    add([(7,1),(13,-1),(GI(3),1),(GI(6),1)],0,'DG_original_inset_clearance')
    # Explicit caller of the remaining bulk after both low-gap extensions.
    add([(5,1),(7,-1)],-F(2,3),'remaining_bulk_transverse_two_thirds')
    if box[3][0]>=0 and any(pair==(2,3) and kind=='sat' and ch==(2,0,1) for pair,kind,ch in choices):
        add([(BE(2),-1)],0,'positive_D_C_owned_normal_upward')
        add([(AB(2),1),(BE(2),-1)],0,'positive_D_C_owned_abs_sign')
    # Reconstruct only dense rows that actually carry a nonzero multiplier.
    # The explicit quotient/remainder formula is the producer's i,dir,s,t
    # loop order; skipping unused rows does not change any row index.
    dense_start=index;dense_stop=index+9*len(DENSE_DIRS)*4
    for row_index,weight in weights.items():
        if not dense_start<=row_index<dense_stop:continue
        i,rest=divmod(row_index-dense_start,len(DENSE_DIRS)*4)
        direction,corner=divmod(rest,4);ss,tt=divmod(corner,2)
        s=-1 if ss==0 else 1;t=-1 if tt==0 else 1;p,q=DENSE_DIRS[direction]
        bb+=weight*roots(Q)[1]
        for k,co in ((2*i,p),(2*i+1,q),(AL(i),(s*p+t*q)/2),(BE(i),(s*q-t*p)/2)):
            rr[k]+=weight*co
        used.append('dense_original_corner')
    index=dense_stop
    assert all(j<index for j in weights)
    bounds=[RHO]*18+[F(1)]*36+([2*RHO,2*RHO,F(1),F(1),F(1),F(1)]*((n-54)//6))
    reserve=(-bb-sum(c*abs(r) for c,r in zip(bounds,rr)))/(1<<40)
    assert reserve>0,('nonpositive exact rational leaf',str(reserve),leaf['path'],used)
    return reserve,None

def verify_partition(data,root_side=None):
    """Check that proved leaves plus recorded frontier cover the requested root.

    Frontier terminals remain explicitly unproved.  This is a coverage audit,
    not a replacement for their missing contradictions.
    """
    tree={};prefix=[] if root_side is None else [['angle',3,root_side]]
    for kind,items in (('leaf',data['leaves']),('frontier',data['frontier'])):
        for item in items:
            path=item['path'];assert path[:len(prefix)]==prefix
            cur=tree
            for step in path[len(prefix):]:
                assert 'terminal' not in cur
                action=step[0];keypart=step[1]
                query=(action,keypart if type(keypart) is int else tuple(keypart))
                if 'query' in cur:assert cur['query']==query
                else:cur['query']=query;cur['children']={}
                key=step[2] if type(step[2]) is int else tuple(step[2])
                cur=cur['children'].setdefault(key,{})
            assert not cur,'Duplicate terminal or a terminal overlaps a descendant.'
            cur['terminal']=kind
    counts={'nodes':0,'leaves':0,'frontier':0}
    def visit(node):
        counts['nodes']+=1
        if 'terminal' in node:
            assert set(node)=={'terminal'}
            counts['leaves' if node['terminal']=='leaf' else 'frontier']+=1
            return
        action,k=node['query']
        if action in ('angle','position'):expected={0,1}
        elif action=='proxy':expected={(axis,sg) for axis in (0,1) for sg in (-1,1)}
        else:
            assert action=='sat';expected={(owner,axis,sg) for owner in k for axis in (0,1) for sg in (-1,1)}
        assert set(node['children'])==expected,('uncovered branch',node['query'],set(node['children']),expected)
        for child in node['children'].values():visit(child)
    visit(tree);return counts

def main():
    ap=argparse.ArgumentParser();ap.add_argument('discovery',type=Path)
    ap.add_argument('--limit',type=int);ap.add_argument('--stride',type=int,default=1);ap.add_argument('--report',type=Path)
    ap.add_argument('--root-side',type=int,choices=(0,1))
    args=ap.parse_args();data=json.loads(args.discovery.read_text());start=time.time()
    partition=verify_partition(data,args.root_side)
    indices=list(range(0,len(data['leaves']),args.stride))
    if args.limit is not None:indices=indices[:args.limit]
    least=None;terminals={};checked=0
    for i in indices:
        reserve,terminal=replay_leaf(data['leaves'][i]);checked+=1
        if terminal:terminals[terminal]=terminals.get(terminal,0)+1
        else:least=reserve if least is None else min(least,reserve)
        if checked%100==0:print('exact leaf samples',checked,'seconds',round(time.time()-start,2),flush=True)
    out={'schema':'weak-outer-bulk-independent-leaf-replay-v1','status':'PASS','target_transverse':'2/3','checked_leaves':checked,'available_leaves':len(data['leaves']),'frontier':len(data['frontier']),'whole_mask_closed':False,'coverage_verified':True,'coverage_includes_unproved_frontier':True,'partition':partition,'root_side':args.root_side,'direct_terminals':terminals,'minimum_rational_reserve':str(least),'seconds':time.time()-start,'discovery_sha256':hashlib.sha256(args.discovery.read_bytes()).hexdigest()}
    if args.report:args.report.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
