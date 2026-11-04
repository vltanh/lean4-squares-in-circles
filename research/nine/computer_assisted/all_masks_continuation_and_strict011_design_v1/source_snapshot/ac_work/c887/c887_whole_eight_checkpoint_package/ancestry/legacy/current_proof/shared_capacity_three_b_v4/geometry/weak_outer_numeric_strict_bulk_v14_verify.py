#!/usr/bin/env python3
"""Independent rational replay for the versioned STRICT full-nine caller.

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
LOCAL_ETA=F(1,64)
LOCAL_CENTERS=(F(-3,2),F(-1,16),F(-1,2),F(-17,16),F(1,2),F(-17,16),F(3,2),F(-1,16),F(-1),F(15,16),F(0),F(15,16),F(1),F(15,16),F(-1,2),F(-1,16),F(1,2),F(-1,16))
LOCAL_COORDS=tuple(k for k in range(18) if k not in (10,11))
DEEP_CERT_SHA256='0a64c08f0e7845a4bf6aa5d5ce43bcb80167a847101b36f903d10554e53a290c'
DEEP_VERIFIER_SHA256='08d913b7e9adc174e66e2225fe0a05e732cd6fa6fbacb794f39b23f61c6e2aef'

@lru_cache(maxsize=1)
def replay_deep_boundary_dependency():
    import weak_outer_deep_boundary_verify as deep
    root=Path(__file__).resolve().parent
    verifier=root/'weak_outer_deep_boundary_verify.py'
    certificate=root/'weak_outer_deep_boundary_angle_certificate.json'
    assert Path(deep.__file__).resolve()==verifier
    assert hashlib.sha256(verifier.read_bytes()).hexdigest()==DEEP_VERIFIER_SHA256
    assert hashlib.sha256(certificate.read_bytes()).hexdigest()==DEEP_CERT_SHA256
    result=deep.verify(json.loads(certificate.read_text()))
    assert result['cases']==8 and result['signed_angle_identities']==144
    assert result['contraction_gap']=='91/2208'
    return result
@lru_cache(maxsize=1)
def replay_large_deep_dependency():
    import weak_outer_numeric_positive_deep_cylinder_arithmetic as large
    expected='8e52f7619c9d0c9a93a28d66b1e8a92202b75e50ec845f50e388b01b101f3882'
    path=Path(__file__).resolve().with_name('weak_outer_numeric_positive_deep_cylinder_arithmetic.py')
    assert Path(large.__file__).resolve()==path
    assert hashlib.sha256(path.read_bytes()).hexdigest()==expected
    result=large.verify()
    assert result['signed_angle_identities']==108 and result['distinct_case_count']==6
    assert result['contraction_gap']=='4619/158976'
    return result

CONTACT_DIRS=tuple(sorted({(sx*p,sy*q) for p,q in ((32,9),(9,32),(24,23),(23,24)) for sx in (-1,1) for sy in (-1,1)}))
assert len(CONTACT_DIRS)==16 and all(p*p+q*q==1105 for p,q in CONTACT_DIRS)

@lru_cache(maxsize=1)
def replay_small_row_dependency():
    import contextlib,importlib.util,io
    path=Path(__file__).with_name('weak_outer_all_sign_small_row_arithmetic.py')
    assert hashlib.sha256(path.read_bytes()).hexdigest()=='6559438b9d9e4ab9e24f561d8dbe63d0d49ececcf2ce768f7245935b1e865ca5'
    spec=importlib.util.spec_from_file_location('accepted_small_row_arithmetic',path)
    module=importlib.util.module_from_spec(spec)
    with contextlib.redirect_stdout(io.StringIO()):spec.loader.exec_module(module)
    assert module.report['status']=='PASS' and module.report['check_count']==70
    return module.report

@lru_cache(maxsize=1)
def replay_correlated_row_dependency():
    import weak_outer_correlated_corner_row_arithmetic as accepted
    path=Path(__file__).with_name('weak_outer_correlated_corner_row_arithmetic.py')
    assert Path(accepted.__file__).resolve()==path.resolve()
    assert hashlib.sha256(path.read_bytes()).hexdigest()=='b67785b140fbdd448bd43d720299491c96649be3fe76c08a4e73fe5725431c4e'
    result=accepted.standard_report()
    assert result['status']=='PASS' and result['check_count']==108
    return result

@lru_cache(maxsize=1)
def replay_cap_dependency():
    endpoints=(F(1,2),F(23,40),F(3,5),F(5,8),F(13,20),F(17,24))
    assert F(133,64)**2>Q and F(17,24)**2>F(1,2)
    reserves=[]
    for lower,upper in zip(endpoints,endpoints[1:]):
        g=F(1,4)/upper;cap=min(RHO,F(133,64)-lower)
        reserve=F(1,4)-max(F(0),F(29,60)-g)**2-max(F(0),cap-F(3,5)-g)**2
        assert reserve>0;reserves.append(reserve)
    assert len(reserves)==5
    return tuple(reserves)

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
        if kind in ('angle','position','angle_cut','position_cut'):
            assert len(step)==3
            key,side=step[1:]; assert type(side) is int and side in (0,1)
            k=key if kind in ('angle','position') else key[0]
            assert type(k) is int
            target=box if kind in ('angle','angle_cut') else pos; assert 0<=k<len(target)
            l,u=target[k]
            if kind in ('angle','position'):m=(l+u)/2
            else:
                assert len(key)==2 and type(key[1]) is str
                m=F(key[1]);assert l<m<u
            target[k]=(l,m) if side==0 else (m,u)
        else:
            assert kind in ('proxy','sat','row_escape','lower_escape','asymmetric_escape','positive_row_escape','inward_row_escape','alternate_four_escape','general_alternate_escape','f_side_escape','small_row_escape','cap_y_pos_escape','cap_y_neg_escape','cap_x_pos_escape','cap_x_neg_escape','correlated_row50_escape','correlated_row30_escape','column_x_escape','column_y_escape') and len(step)==3
            pair=tuple(step[1]); choice=tuple(step[2]); assert len(pair)==2
            i,j=pair
            assert (pair,kind) not in seen
            if kind=='general_alternate_escape':
                assert i==0 and type(j) is int and 1<=j<=105
            elif kind in COLUMN_KINDS:
                assert i==0 and type(j) is int and 1<=j<=len(COLUMN_CHAINS)
            else:assert 0<=i<j<9
            seen.add((pair,kind))
            if kind=='proxy': assert choice in ((0,-1),(0,1),(1,-1),(1,1))
            elif kind=='sat': assert len(choice)==3 and choice[0] in pair and choice[1] in (0,1) and choice[2] in (-1,1)
            elif kind=='inward_row_escape':
                assert pair==(7,8) and box[0][1]<=0 and box[3][0]>=0
                assert len(choice)==1 and type(choice[0]) is int and 0<=choice[0]<10
            elif kind in CORRELATED_KINDS:
                eta,variation=correlated_parameters(kind,F(1))
                assert pair==(7,8) and small_row_guard(box,eta)
                assert len(choice)==1 and type(choice[0]) is int and 0<=choice[0]<8
                replay_correlated_row_dependency()
            elif kind in COLUMN_KINDS:
                specs=column_specs(pair,kind,F(1))
                assert len(choice)==1 and type(choice[0]) is int and 0<=choice[0]<len(specs)
                assert F(3,5)**2+F(4,5)**2==1
            elif kind=='small_row_escape':
                assert pair==(7,8) and small_row_guard(box,F(1,50))
                assert len(choice)==1 and type(choice[0]) is int and 0<=choice[0]<8
                replay_small_row_dependency()
            elif kind in CAP_KINDS:
                assert len(choice)==1 and type(choice[0]) is int and 0<=choice[0]<4
                replay_cap_dependency()
            elif kind=='f_side_escape':
                assert pair in ((5,7),(5,8))
                assert len(choice)==1 and type(choice[0]) is int and 0<=choice[0]<8
            elif kind=='general_alternate_escape':
                general_alternate_specs(pair,F(1,2))
                assert len(choice)==1 and type(choice[0]) is int and 0<=choice[0]<8
            elif kind=='alternate_four_escape':
                alternate_chain(pair)
                assert len(choice)==1 and type(choice[0]) is int and 0<=choice[0]<8
            else:
                assert pair in ((2,7),(2,8)) if kind=='lower_escape' else pair in ((1,7),(1,8))
                assert len(choice)==1 and type(choice[0]) is int and 0<=choice[0]<(2 if kind=='lower_escape' else 6)
                if kind=='positive_row_escape':assert box[3][0]>=0
            choices.append((pair,kind,choice))
    return tuple(box),tuple(pos),tuple(choices)

def effective_boxes(box,choices,version=None):
    box=list(box)
    if version=='strict_bulk_2026_11_03_v14':
        for pair,kind,ch in choices:
            if kind=='inward_row_escape' and ch[0] in (0,1):
                return None,('accepted unique A leftmost' if ch[0]==0 else 'accepted no extra right of D')
            if kind in ('row_escape','positive_row_escape','asymmetric_escape') and ch[0]==1:
                return None,'accepted no extra right of D'
    assert version in ('strict_bulk_2026_11_03_v1','strict_bulk_2026_11_03_v2','strict_bulk_2026_11_03_v3','strict_bulk_2026_11_03_v4','strict_bulk_2026_11_03_v5','strict_bulk_2026_11_03_v6','strict_bulk_2026_11_03_v7','strict_bulk_2026_11_03_v14')
    if version not in ('strict_bulk_2026_11_03_v3','strict_bulk_2026_11_03_v4','strict_bulk_2026_11_03_v5','strict_bulk_2026_11_03_v6','strict_bulk_2026_11_03_v7','strict_bulk_2026_11_03_v14'):assert all(kind not in ('asymmetric_escape','positive_row_escape') for _,kind,_ in choices)
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
            if axis==0:
                l,u=box[owner]
                if u<=0:return None,'accepted all-tilts C/D normal points upward'
                box[owner]=(max(l,F(0)),u)
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
        if version in ('strict_bulk_2026_11_03_v6','strict_bulk_2026_11_03_v7','strict_bulk_2026_11_03_v14') and pair in ((1,5),(2,5)):
            if axis==1 and sg<0:return None,'accepted B/F or C/F separator has positive vertical component'
            if axis==0:
                l,u=box[owner]
                if sg>0:
                    if u<=0:return None,'accepted B/F or C/F separator has positive vertical component'
                    box[owner]=(max(l,F(0)),u)
                else:
                    if l>=0:return None,'accepted B/F or C/F separator has positive vertical component'
                    box[owner]=(l,min(u,F(0)))
        if version=='strict_bulk_2026_11_03_v14' and pair==(0,4):
            if axis==1 and sg<0:return None,'accepted A/E separator has positive vertical component'
            if axis==0:
                l,u=box[owner]
                if sg>0:
                    if u<=0:return None,'accepted A/E separator has positive vertical component'
                    box[owner]=(max(l,F(0)),u)
                else:
                    if l>=0:return None,'accepted A/E separator has positive vertical component'
                    box[owner]=(l,min(u,F(0)))
    return tuple(box),None

def center_bounds(box,pos,choices,version=None):
    hs=tuple(h_bounds(T) for T in box); gs=tuple(down(F(1,4)/h[1]) for h in hs)
    X=[list(pos[2*i]) for i in range(9)];Y=[list(pos[2*i+1]) for i in range(9)]
    X[2][0]=max(X[2][0],hs[2][0]-F(1,60));X[3][0]=max(X[3][0],F(4,3))
    X[2][1]=min(X[2][1],hs[2][1]+F(5,64));X[6][0]=max(X[6][0],hs[6][0]+F(101,432))
    if version in ('strict_bulk_2026_11_03_v6','strict_bulk_2026_11_03_v7','strict_bulk_2026_11_03_v14'):
        X[6][1]=min(X[6][1],hs[6][1]+F(49,64))
        X[4][1]=min(X[4][1],-F(15,64)-hs[4][0])
        X[5][0]=max(X[5][0],-F(115,432))
        X[5][1]=min(X[5][1],F(49,64)-hs[5][0])
    if version=='strict_bulk_2026_11_03_v14':
        Y[4][0]=max(Y[4][0],gs[4]+F(3,40),F(17,40))
        Y[6][0]=max(Y[6][0],gs[6]+F(3,40),F(17,40))
        for original in (7,8):X[original][1]=min(X[original][1],F(5,4))
    def empty(): return any(l>u for l,u in X+Y)
    center_rows=[]
    if version=='strict_bulk_2026_11_03_v14':
        for pair,kind,ch in choices:
            if kind=='f_side_escape':center_rows.extend(f_side_escape_rows(pair,ch[0],F(3,5)));continue
            if kind=='inward_row_escape':specs=inward_escape_specs(F(11,30))
            elif kind=='small_row_escape':specs=small_row_specs(F(1,12))
            elif kind in CAP_KINDS:specs=cap_escape_specs(pair,kind,F(3,5),F(29,60))
            elif kind in CORRELATED_KINDS:specs=small_row_specs(correlated_parameters(kind,F(1))[1])
            elif kind in COLUMN_KINDS:specs=column_specs(pair,kind,F(1))
            else:continue
            center_rows.append(specs[ch[0]])
            for earlier in range(ch[0]):
                row,rval=specs[earlier];center_rows.append(([(k,-c) for k,c in row],-rval))
    for _ in range(16):
        interval_row_propagation(X,Y,center_rows,F(0))
        if empty():return None,hs,gs,'empty interval after analytic center-row propagation'
        if version=='strict_bulk_2026_11_03_v14':
            Y[6][0]=max(Y[6][0],Y[1][0]+F(13,480))
            Y[1][1]=min(Y[1][1],Y[6][1]-F(13,480))
            for original in range(1,9):
                X[original][0]=max(X[original][0],X[0][0]);X[0][1]=min(X[0][1],X[original][1])
            for original in (7,8):
                X[original][1]=min(X[original][1],X[3][1]);X[3][0]=max(X[3][0],X[original][0])
        if version=='strict_bulk_2026_11_03_v14':
            ae_clearance=gs[0]+gs[4]
            Y[4][0]=max(Y[4][0],Y[0][0]+ae_clearance,Y[1][0]+F(13,480))
            Y[0][1]=min(Y[0][1],Y[4][1]-ae_clearance)
            Y[1][1]=min(Y[1][1],Y[4][1]-F(13,480))
        if version in ('strict_bulk_2026_11_03_v6','strict_bulk_2026_11_03_v7','strict_bulk_2026_11_03_v14'):
            bf=gs[1]+gs[5]
            Y[5][0]=max(Y[5][0],Y[1][0]+bf);Y[1][1]=min(Y[1][1],Y[5][1]-bf)
            X[5][0]=max(X[5][0],X[1][0]+F(269,1728))
            X[1][1]=min(X[1][1],X[5][1]-F(269,1728))
            X[5][1]=min(X[5][1],X[1][1]+F(751,960))
            X[1][0]=max(X[1][0],X[5][0]-F(751,960))
            ae=F(1,4)/hs[0][0]+F(1,4)/hs[4][0]-F(3,20)
            X[4][1]=min(X[4][1],X[0][1]+ae);X[0][0]=max(X[0][0],X[4][0]-ae)
            X[0][1]=min(X[0][1],X[4][1]+ae);X[4][0]=max(X[4][0],X[0][0]-ae)
        for i,j,bit in EDGES:
            g=gs[i]+gs[j] if bit else hs[i][0]+hs[j][0]
            X[j][0]=max(X[j][0],X[i][0]+g);X[i][1]=min(X[i][1],X[j][1]-g)
        X[7][1]=min(X[7][1],X[8][1]);X[8][0]=max(X[8][0],X[7][0])
        for pair,kind,ch in choices:
            if kind=='asymmetric_escape':
                original=pair[1];branch=ch[0]
                if branch<2:
                    i,j=(original,1) if branch==0 else (3,original)
                    X[i][1]=min(X[i][1],X[j][1]);X[j][0]=max(X[j][0],X[i][0])
                else:
                    i,j,gap=((original,1,F(0)),(1,original,F(1,3)),(3,original,F(1,16)),(original,3,F(1,16)))[branch-2]
                    Y[i][1]=min(Y[i][1],Y[j][1]-gap);Y[j][0]=max(Y[j][0],Y[i][0]+gap)
                continue
            if kind=='positive_row_escape':
                original=pair[1];branch=ch[0]
                if branch<2:
                    i,j=(original,1) if branch==0 else (3,original)
                    X[i][1]=min(X[i][1],X[j][1]);X[j][0]=max(X[j][0],X[i][0])
                elif branch<4:
                    i,j=(1,3) if branch==2 else (3,1)
                    Y[i][1]=min(Y[i][1],Y[j][1]-F(1,2));Y[j][0]=max(Y[j][0],Y[i][0]+F(1,2))
                elif branch==4:Y[original][0]=max(Y[original][0],(Y[1][0]+Y[3][0]+F(1,2))/2)
                else:Y[original][1]=min(Y[original][1],(Y[1][1]+Y[3][1]-F(1,2))/2)
                continue
            if kind=='row_escape':
                original=pair[1];branch=ch[0]
                if branch<2:
                    i,j=(original,1) if branch==0 else (3,original)
                    X[i][1]=min(X[i][1],X[j][1]);X[j][0]=max(X[j][0],X[i][0])
                else:
                    i,j=((original,1),(1,original),(3,original),(original,3))[branch-2]
                    Y[i][1]=min(Y[i][1],Y[j][1]-F(1,8));Y[j][0]=max(Y[j][0],Y[i][0]+F(1,8))
                continue
            if kind=='lower_escape':
                original=pair[1]
                if ch[0]==0:X[original][1]=min(X[original][1],F(0))
                else:
                    Y[2][1]=min(Y[2][1],Y[original][1]);Y[original][0]=max(Y[original][0],Y[2][0])
                continue
            if kind!='proxy':continue
            i,j=pair;axis,sg=ch;coords=(X,Y)[axis]
            if sg<0:i,j=j,i
            g=gs[i]+gs[j]
            coords[j][0]=max(coords[j][0],coords[i][0]+g);coords[i][1]=min(coords[i][1],coords[j][1]-g)
        if empty(): return None,hs,gs,'empty propagated original center interval'
        if version in ('strict_bulk_2026_11_03_v7','strict_bulk_2026_11_03_v14'):
            # A physical pair's original contained insets must satisfy at
            # least one of these four gap inequalities. The positive exact
            # margin is only conservative: it retains additional options.
            eps=F(1,10**9)
            for i in range(9):
                for j in range(i+1,9):
                    gap=gs[i]+gs[j];possible=[]
                    for axis,coords in ((0,X),(1,Y)):
                        if coords[j][1]-coords[i][0]+eps>=gap:possible.append((i,j,axis))
                        if coords[i][1]-coords[j][0]+eps>=gap:possible.append((j,i,axis))
                    if not possible:
                        return None,hs,gs,'all four original inset separation options impossible: '+str((i,j))
                    if len(possible)==1:
                        left,right,axis=possible[0];coords=(X,Y)[axis]
                        coords[right][0]=max(coords[right][0],coords[left][0]+gap)
                        coords[left][1]=min(coords[left][1],coords[right][1]-gap)
            if empty():return None,hs,gs,'empty interval after forced original inset separation'
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
        Y[3][0]=max(Y[3][0],Y[2][0]+F(2,3));Y[2][1]=min(Y[2][1],Y[3][1]-F(2,3))
        dg=max(gs[3]+gs[6],F(8,15)+F(7,8)*(hs[3][0]+hs[6][0]-1))
        Y[6][0]=max(Y[6][0],Y[3][0]+dg);Y[3][1]=min(Y[3][1],Y[6][1]-dg)
        cg=hs[2][0]+hs[6][0]+F(97,4480)
        Y[6][0]=max(Y[6][0],Y[2][0]+cg);Y[2][1]=min(Y[2][1],Y[6][1]-cg)
        Y[2][1]=min(Y[2][1],-F(7,32)-F(7,8)*X[2][0])
        X[2][1]=min(X[2][1],(-F(7,32)-Y[2][0])*F(8,7))
        if version in ('strict_bulk_2026_11_03_v3','strict_bulk_2026_11_03_v4','strict_bulk_2026_11_03_v5','strict_bulk_2026_11_03_v6','strict_bulk_2026_11_03_v7','strict_bulk_2026_11_03_v14'):
            cf=gs[2]+gs[5]
            Y[5][0]=max(Y[5][0],Y[2][0]+cf);Y[2][1]=min(Y[2][1],Y[5][1]-cf)
        for i,j,bit in EDGES:
            dxhi=X[j][1]-X[i][0]
            Y[j][0]=max(Y[j][0],Y[i][0]-dxhi);Y[j][1]=min(Y[j][1],Y[i][1]+dxhi)
            Y[i][0]=max(Y[i][0],Y[j][0]-dxhi);Y[i][1]=min(Y[i][1],Y[j][1]+dxhi)
        if empty():return None,hs,gs,'empty propagated original center interval'
    return tuple(tuple(v) for i in range(9) for v in (X[i],Y[i])),hs,gs,None

def difference_bounds(pair,cb,gs,version=None):
    i,j=pair;dr=[]
    for xy in (0,1):
        lo=cb[2*j+xy][0]-cb[2*i+xy][1];hi=cb[2*j+xy][1]-cb[2*i+xy][0]
        if pair==(2,3):lo=max(lo,gs[2]+gs[3] if xy==0 else F(5,8));hi=min(hi,F(31,30))
        if pair==(3,6) and xy==0:lo=max(lo,-F(1459,1728));hi=min(hi,F(1459,1728))
        if pair==(3,6) and xy==1:lo=max(lo,F(0))
        if version in ('strict_bulk_2026_11_03_v6','strict_bulk_2026_11_03_v7','strict_bulk_2026_11_03_v14'):
            if pair==(1,5):
                lo=max(lo,F(269,1728) if xy==0 else gs[1]+gs[5])
                if xy==0:hi=min(hi,F(751,960))
            if pair==(2,5) and xy==1:lo=max(lo,gs[2]+gs[5])
        if version=='strict_bulk_2026_11_03_v14' and pair==(0,4):
            if xy==0:lo=max(lo,-F(17,20));hi=min(hi,F(17,20))
            else:lo=max(lo,gs[0]+gs[4])
        dr.append((lo,hi))
    return dr

from itertools import permutations
GENERAL_SELECTORS=tuple(chain for chain in permutations((0,1,2,3,7,8),4)
                        if tuple(i for i in chain if i<4)==tuple(sorted(i for i in chain if i<4)))
assert len(GENERAL_SELECTORS)==105 and len(set(GENERAL_SELECTORS))==105

def general_alternate_specs(marker,half):
    assert len(marker)==2 and marker[0]==0 and 1<=marker[1]<=105
    chain=GENERAL_SELECTORS[marker[1]-1];rows=[]
    for i,j in zip(chain,chain[1:]):
        for sign in (-1,1):
            rows.append(([(2*j,1),(2*i,-1),(2*j+1,sign),(2*i+1,-sign)],0))
    for i,j in ((chain[0],chain[1]),(chain[2],chain[3])):
        rows.append(([(2*j,1),(2*i,-1),(18+i,-half),(36+i,-half),
                      (18+j,-half),(36+j,-half)],0))
    return rows

def f_side_escape_rows(pair,branch,threshold):
    assert pair in ((5,7),(5,8)) and type(branch) is int and 0<=branch<8
    x=pair[1];side,local=divmod(branch,4)
    left,right=(0,5) if side==0 else (5,3)
    signs=((-1,-1),(-1,1),(1,-1),(1,1))
    def height_row(k):
        s,t=signs[k]
        return [(2*left+1,s),(2*x+1,t-s),(2*right+1,-t)],-threshold
    horizontal=([(2*x,1),(10,-1)],0) if side==0 else ([(10,1),(2*x,-1)],0)
    out=[horizontal,height_row(local)]
    for earlier in range(local):
        row,rhs=height_row(earlier)
        out.append(([(k,-c) for k,c in row],-rhs))
    return out

SMALL_ROW_ORIGINALS=(0,3,4,5,6,7,8)
CAP_KINDS={'cap_y_pos_escape':(1,1),'cap_y_neg_escape':(1,-1),
           'cap_x_pos_escape':(0,1),'cap_x_neg_escape':(0,-1)}

def small_row_guard(box,eta):
    return all(-eta<=box[i][0]<=box[i][1]<=eta for i in SMALL_ROW_ORIGINALS)

def small_row_specs(threshold):
    return inward_escape_specs(threshold)[2:]

def cap_escape_specs(pair,kind,threshold,gap):
    assert kind in CAP_KINDS
    i,j=pair;axis,sign=CAP_KINDS[kind];across=1-axis
    return [([(2*i+axis,sign)],threshold),([(2*j+axis,sign)],threshold),
            ([(2*i+across,1),(2*j+across,-1)],-gap),
            ([(2*j+across,1),(2*i+across,-1)],-gap)]

def gap_secant(lo,hi,g):
    assert lo<=hi and g>=0
    ff=lambda t:max(abs(t)-g,0)**2
    if lo==hi:return 0,ff(lo)
    fl,fu=ff(lo),ff(hi)
    return (fu-fl)/(hi-lo),(hi*fl-lo*fu)/(hi-lo)

def interval_row_propagation(X,Y,rows,eps):
    for entries,rval in rows:
        merged={}
        for k,c in entries:merged[k]=merged.get(k,0)+c
        merged={k:c for k,c in merged.items() if c}
        for k,c in merged.items():
            other=0
            for j,d in merged.items():
                if j==k:continue
                interval=(Y if j%2 else X)[j//2]
                other+=d*interval[0 if d>0 else 1]
            interval=(Y if k%2 else X)[k//2];bound=(rval-other)/c
            if c>0:interval[1]=min(interval[1],bound+eps)
            else:interval[0]=max(interval[0],bound-eps)

CORRELATED_KINDS=('correlated_row50_escape','correlated_row30_escape')
COLUMN_KINDS={'column_x_escape':0,'column_y_escape':1}
COLUMN_CHAINS=tuple(permutations(range(9),3))+tuple(permutations(range(9),4))
assert len(COLUMN_CHAINS)==3528
COLUMN_INDEX={chain:index+1 for index,chain in enumerate(COLUMN_CHAINS)}

def correlated_parameters(kind,one):
    assert kind in CORRELATED_KINDS
    return (one/50,one*9/20) if kind=='correlated_row50_escape' else (one/30,one*11/30)

def column_specs(marker,kind,one):
    assert kind in COLUMN_KINDS and marker[0]==0 and 1<=marker[1]<=len(COLUMN_CHAINS)
    chain=COLUMN_CHAINS[marker[1]-1];axis=COLUMN_KINDS[kind];across=1-axis
    rows=[([(2*j+axis,1),(2*i+axis,-1)],0) for i,j in zip(chain,chain[1:])]
    rows.append(([(2*chain[0]+axis,1),(2*chain[-1]+axis,-1)],-one*(len(chain)-2)-one*4/5))
    from itertools import product
    for signs in product((-1,1),repeat=len(chain)-1):
        row=[]
        for (i,j),sg in zip(zip(chain,chain[1:]),signs):row.extend(((2*i+across,sg),(2*j+across,-sg)))
        rows.append((row,-one*3/5))
    assert len(rows)==(7 if len(chain)==3 else 12)
    return rows

def alternate_chain(pair):
    options={(1,7):(0,1,7,3),(1,8):(0,1,8,3),(2,7):(0,2,7,3),
             (2,8):(0,2,8,3),(7,8):(0,7,8,3)}
    assert pair in options
    return options[pair]

def alternate_escape_specs(pair,half):
    chain=alternate_chain(pair);rows=[]
    for i,j in zip(chain,chain[1:]):
        for sign in (-1,1):
            rows.append(([(2*j,1),(2*i,-1),(2*j+1,sign),(2*i+1,-sign)],0))
    for i,j in ((chain[0],chain[1]),(chain[2],chain[3])):
        rows.append(([(2*j,1),(2*i,-1),(18+i,-half),(36+i,-half),
                      (18+j,-half),(36+j,-half)],0))
    return rows

def inward_escape_specs(threshold):
    from itertools import product
    rows=[([(14,1),(0,-1)],0), ([(6,1),(16,-1)],0)]
    for s1,s2,s3 in product((-1,1),repeat=3):
        rows.append(([(1,s1),(15,s2-s1),(17,s3-s2),(7,-s3)],-threshold))
    return rows

def replay_current_leaf(leaf):
    box,pos,choices=reconstruct(leaf['path'])
    if leaf.get('analytic_terminal')=='deep_B_cylinder_1_64_v1':
        assert leaf['context_version'] in ('strict_bulk_2026_11_03_v2','strict_bulk_2026_11_03_v3','strict_bulk_2026_11_03_v4','strict_bulk_2026_11_03_v5','strict_bulk_2026_11_03_v6','strict_bulk_2026_11_03_v7','strict_bulk_2026_11_03_v14')
        assert leaf['analytic_terminal']=='deep_B_cylinder_1_64_v1'
        assert all(-LOCAL_ETA<=l<=u<=LOCAL_ETA for l,u in box)
        assert all(LOCAL_CENTERS[k]-LOCAL_ETA<=pos[k][0]<=pos[k][1]<=LOCAL_CENTERS[k]+LOCAL_ETA for k in LOCAL_COORDS)
        # For |t|<=1/64, |atan t|<=|t| proves the theorem's angle bound.
        # The accepted144-identity contraction table and nonlinear lift are
        # explicit prerequisites of this named strict-caller terminal.
        replay_deep_boundary_dependency()
        assert F(4234,69)*LOCAL_ETA==F(2117,2208)<1
        return None,'accepted deep-B eight-center/all-nine-angle cylinder'
    box,terminal=effective_boxes(box,choices,leaf.get('context_version'))
    if terminal:return None,terminal
    cb,hs,gs,terminal=center_bounds(box,pos,choices,leaf['context_version'])
    if terminal:return None,terminal
    if leaf.get('analytic_terminal')=='all_sign_correlated_row_v1':
        assert leaf['context_version']=='strict_bulk_2026_11_03_v14'
        kind=leaf['row_guard'];eta,variation=correlated_parameters(kind,F(1))
        assert small_row_guard(box,eta)
        upper=max(sum(-c*cb[k][1 if c<0 else 0] for k,c in row) for row,_ in small_row_specs(variation))
        assert upper<=variation
        replay_correlated_row_dependency()
        return None,'accepted all-sign correlated-corner seven-original row'
    if leaf.get('analytic_terminal')=='all_sign_seven_frame_row_1_12_v1':
        assert leaf['context_version']=='strict_bulk_2026_11_03_v14'
        assert small_row_guard(box,F(1,50))
        upper=max(sum(-c*cb[k][1 if c<0 else 0] for k,c in row)
                  for row,_ in small_row_specs(F(1,12)))
        assert upper<=F(1,12)
        replay_small_row_dependency()
        return None,'accepted all-sign seven-original small-angle row'
    if 'analytic_terminal' in leaf:
        assert leaf['context_version'] in ('strict_bulk_2026_11_03_v6','strict_bulk_2026_11_03_v7','strict_bulk_2026_11_03_v14')
        assert leaf['analytic_terminal']=='deep_B_propagated_cylinder_v6'
        assert leaf['local_radius'] in ('1/32','1/64')
        radius=F(leaf['local_radius'])
        assert all(-radius<=l<=u<=radius for l,u in box)
        assert all(LOCAL_CENTERS[k]-radius<=cb[k][0]<=cb[k][1]<=LOCAL_CENTERS[k]+radius for k in LOCAL_COORDS)
        if radius==F(1,32):
            assert box[3][0]>=0 or any(pair==(2,3) and kind=='sat' and ch[1]==0 for pair,kind,ch in choices)
            replay_large_deep_dependency()
            assert 1-F(154357,4968)*radius==F(4619,158976)>0
            return None,'accepted propagated radius1/32 deep-B cylinder'
        replay_deep_boundary_dependency()
        assert 1-F(4234,69)*radius==F(91,2208)>0
        return None,'accepted propagated radius1/64 deep-B cylinder'
    for pair,kind,ch in choices:
        if kind=='sat' and any(l>u for l,u in difference_bounds(pair,cb,gs,leaf['context_version'])):
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
        if kind!='sat':continue
        owner,ax,sg=ch;nn=normal_bounds(box[owner],ax,sg)
        nm=[F(round((l+u)/2*(1<<30)),1<<30) for l,u in nn]
        dr=difference_bounds(pair,cb,gs,leaf['context_version']);assert all(l<=u for l,u in dr)
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
            g=max(gs[i],gs[j]);ax,bx=gap_secant(ll,uu,g);ay,by=gap_secant(vv,ww,g)
            add([(2*i,ax),(2*j,-ax),(2*i+1,ay),(2*j+1,-ay)],-F(1,4)+bx+by,'original_inset_disk_secant')
            aa_i=normal_bounds(box[i])[0][1];aa_j=normal_bounds(box[j])[0][1]
            p=max(F(1,2)/aa_i,F(1,2)/aa_j)
            ap,bp=gap_secant(ll+vv,uu+ww,p);am,bm=gap_secant(ll-ww,uu-vv,p)
            ax,ay=ap+am,ap-am
            add([(2*i,ax),(2*j,-ax),(2*i+1,ay),(2*j+1,-ay)],-F(1,2)+bp+bm,'original_diamond_disk_secant')
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
    add([(5,1),(4,F(7,8))],-F(7,32),'accepted_C_slant')
    add([(5,1),(13,-1),(AL(2),F(1,2)),(AB(2),F(1,2)),(AL(6),F(1,2)),(AB(6),F(1,2))],-F(97,4480),'accepted_CG_actual_vertical_clearance')
    for pair,kind,ch in choices:
        if kind=='row_escape':
            original=pair[1];xx=2*original;yy=xx+1;branch=ch[0]
            spec=(
                ([(xx,1),(2,-1)],F(0)), ([(6,1),(xx,-1)],F(0)),
                ([(yy,1),(3,-1)],-F(1,8)), ([(3,1),(yy,-1)],-F(1,8)),
                ([(7,1),(yy,-1)],-F(1,8)), ([(yy,1),(7,-1)],-F(1,8)))
            entries,rhs=spec[branch];add(entries,rhs,'accepted_replacement_row_escape')
        elif kind=='lower_escape':
            original=pair[1]
            if ch[0]==0:add([(2*original,1)],0,'accepted_right_lower_escape_left')
            else:add([(5,1),(2*original+1,-1)],0,'accepted_right_lower_escape_above')
    for i,j,sg in ((0,4,-1),(3,6,1)):
        add([(2*i,sg*A),(2*j,sg*B),(AL(i),25*A/32),(AB(i),-7*A/32),(AL(j),-B/2),(AB(j),-B/2)],F(211,4)+41*A/32,'sharp_endpoint_cap')
    if leaf['context_version'] in ('strict_bulk_2026_11_03_v2','strict_bulk_2026_11_03_v3','strict_bulk_2026_11_03_v4','strict_bulk_2026_11_03_v5','strict_bulk_2026_11_03_v6','strict_bulk_2026_11_03_v7','strict_bulk_2026_11_03_v14'):
        contact_start=index;contact_stop=index+9*len(CONTACT_DIRS)*4
        assert Q*1105==F(1105,16)**2
        for row_index,weight in weights.items():
            if not contact_start<=row_index<contact_stop:continue
            i,rest=divmod(row_index-contact_start,len(CONTACT_DIRS)*4)
            direction,corner=divmod(rest,4);ss,tt=divmod(corner,2)
            s=-1 if ss==0 else 1;t=-1 if tt==0 else 1;p,q=CONTACT_DIRS[direction]
            bb+=weight*F(1105,16)
            for k,co in ((2*i,p),(2*i+1,q),(AL(i),F(s*p+t*q,2)),(BE(i),F(s*q-t*p,2))):
                rr[k]+=weight*co
            used.append('exact_contact_corner')
        index=contact_stop
    if leaf['context_version'] in ('strict_bulk_2026_11_03_v3','strict_bulk_2026_11_03_v4','strict_bulk_2026_11_03_v5','strict_bulk_2026_11_03_v6','strict_bulk_2026_11_03_v7','strict_bulk_2026_11_03_v14'):
        add([(5,1),(11,-1),(GI(2),1),(GI(5),1)],0,'accepted_CF_vertical_insets')
        for sg in (-1,1):add([(10,sg),(4,-sg),(GI(2),-1),(GI(5),-1)],-F(1,25),'accepted_CF_horizontal_overlap')
        kk=F(92,27)
        add([(12,1),(13,-1),(5,1),(4,kk),(AL(2),-kk/2),(AB(2),-kk/2)],0,'accepted_F_order_linear_S')
        for pair,kind,ch in choices:
            if kind=='asymmetric_escape':
                original=pair[1];xx=2*original;yy=xx+1;branch=ch[0]
                spec=(
                    ([(xx,1),(2,-1)],F(0)), ([(6,1),(xx,-1)],F(0)),
                    ([(yy,1),(3,-1)],F(0)), ([(3,1),(yy,-1)],-F(1,3)),
                    ([(7,1),(yy,-1)],-F(1,16)), ([(yy,1),(7,-1)],-F(1,16)))
                entries,rval=spec[branch];add(entries,rval,'accepted_asymmetric_row_escape')
            elif kind=='positive_row_escape':
                original=pair[1];xx=2*original;yy=xx+1;branch=ch[0]
                spec=(
                    ([(xx,1),(2,-1)],F(0)), ([(6,1),(xx,-1)],F(0)),
                    ([(3,1),(7,-1)],-F(1,2)), ([(3,-1),(7,1)],-F(1,2)),
                    ([(yy,-2),(3,1),(7,1)],-F(1,2)), ([(yy,2),(3,-1),(7,-1)],-F(1,2)))
                entries,rval=spec[branch];add(entries,rval,'accepted_positive_total_variation_escape')
        def linear_interval(coef,interval):
            ll,uu=interval
            return (coef*ll,coef*uu) if coef>=0 else (coef*uu,coef*ll)
        def min_abs(interval):
            ll,uu=interval;assert ll<=uu
            return F(0) if ll<=0<=uu else min(abs(ll),abs(uu))
        for i in range(9):
            aa,be=normal_bounds(box[i])
            for s in (-1,1):
                for t in (-1,1):
                    sx=linear_interval(F(s,2),aa);tx=linear_interval(F(-t,2),be)
                    sy=linear_interval(F(s,2),be);ty=linear_interval(F(t,2),aa)
                    xx=(cb[2*i][0]+sx[0]+tx[0],cb[2*i][1]+sx[1]+tx[1])
                    yy=(cb[2*i+1][0]+sy[0]+ty[0],cb[2*i+1][1]+sy[1]+ty[1])
                    add([],Q-min_abs(xx)**2-min_abs(yy)**2,'original_corner_box_norm')
    if leaf['context_version'] in ('strict_bulk_2026_11_03_v5','strict_bulk_2026_11_03_v6','strict_bulk_2026_11_03_v7','strict_bulk_2026_11_03_v14'):
        # Each accepted linear escape union is interpreted in first-true
        # order. A point selects the first satisfied primary halfspace;
        # all earlier strict failures imply these closed complements.
        # Older leaf contexts prove supersets and remain sufficient.
        for pair,kind,ch in choices:
            if kind not in ('lower_escape','row_escape','asymmetric_escape','positive_row_escape'):continue
            original=pair[1];xx=2*original;yy=xx+1
            if kind=='lower_escape':
                spec=(([(xx,1)],F(0)), ([(5,1),(yy,-1)],F(0)))
            elif kind=='positive_row_escape':
                spec=(
                    ([(xx,1),(2,-1)],F(0)), ([(6,1),(xx,-1)],F(0)),
                    ([(3,1),(7,-1)],-F(1,2)), ([(3,-1),(7,1)],-F(1,2)),
                    ([(yy,-2),(3,1),(7,1)],-F(1,2)), ([(yy,2),(3,-1),(7,-1)],-F(1,2)))
            elif kind=='asymmetric_escape':
                spec=(
                    ([(xx,1),(2,-1)],F(0)), ([(6,1),(xx,-1)],F(0)),
                    ([(yy,1),(3,-1)],F(0)), ([(3,1),(yy,-1)],-F(1,3)),
                    ([(7,1),(yy,-1)],-F(1,16)), ([(yy,1),(7,-1)],-F(1,16)))
            else:
                spec=(
                    ([(xx,1),(2,-1)],F(0)), ([(6,1),(xx,-1)],F(0)),
                    ([(yy,1),(3,-1)],-F(1,8)), ([(3,1),(yy,-1)],-F(1,8)),
                    ([(7,1),(yy,-1)],-F(1,8)), ([(yy,1),(7,-1)],-F(1,8)))
            for previous in range(ch[0]):
                entries,rval=spec[previous]
                add([(k,-c) for k,c in entries],-rval,'ordered_escape_predecessor_complement')
    if leaf['context_version'] in ('strict_bulk_2026_11_03_v6','strict_bulk_2026_11_03_v7','strict_bulk_2026_11_03_v14'):
        add([(12,1),(AL(6),-F(1,2)),(AB(6),-F(1,2))],F(49,64),'accepted_G_edge_upper')
        add([(8,1),(AL(4),F(1,2)),(AB(4),F(1,2))],-F(15,64),'accepted_E_right_edge_upper')
        add([(10,1),(AL(5),F(1,2)),(AB(5),F(1,2))],F(49,64),'accepted_F_right_edge_upper')
        add([(10,-1)],F(115,432),'accepted_F_horizontal_lower')
        add([(3,1),(11,-1),(GI(1),1),(GI(5),1)],0,'accepted_BF_vertical_insets')
        add([(2,1),(10,-1)],-F(269,1728),'accepted_BF_horizontal_lower')
        add([(10,1),(2,-1)],F(751,960),'accepted_BF_horizontal_upper')
        for sg in (-1,1):
            add([(10,sg),(2,-sg),(GI(1),-1),(GI(5),-1)],-F(1,7104),'accepted_BF_horizontal_inset_overlap')
            add([(10,sg),(2,-sg),(3,1),(11,-1)],-F(1,7104),'accepted_BF_strict_vertical_cone')
            add([(8,sg),(0,-sg),(GI(0),-1),(GI(4),-1)],-F(3,20),'accepted_AE_horizontal_inset_overlap')
            add([(10,sg),(GI(5),-1)],-F(1,12),'accepted_F_contains_central_strip')
    if leaf['context_version']=='strict_bulk_2026_11_03_v14':
        add([(1,1),(9,-1),(GI(0),1),(GI(4),1)],0,'accepted_AE_vertical_insets')
        for sg in (-1,1):
            add([(8,sg),(0,-sg),(1,1),(9,-1)],-F(3,20),'accepted_AE_strict_vertical_cone')
        add([(9,-1),(GI(4),1)],-F(3,40),'accepted_E_inset_lower_edge')
        add([(9,-1)],-F(17,40),'accepted_E_height_lower')
        add([(3,1),(9,-1)],-F(13,480),'accepted_E_above_B')
        assert 368**2*679-9581**2==157335>0
        add([(0,-A),(8,-B),(AL(0),-F(29,2)),(AB(0),-F(29,2)),
             (AL(4),-B/2),(AB(4),-B/2)],F(245,4),'accepted_left_width_toll_cap')
        if box[0][1]<=0:
            k=F(207,16)
            add([(0,-A),(8,-B),(AL(0),A/2),(BE(0),-A/2+k),
                 (AL(4),-B/2),(AB(4),-B/2)],F(211,4)+A,'signed_left_cap')
            left_signed_budget=list(budget)+[(AB(0),-4),(AL(0),A),(BE(0),-A+k)]
            add(left_signed_budget,3*A+B,'left_signed_orientation_budget')
            if box[3][0]>=0:
                both_signed_budget=left_signed_budget+[(AB(3),-4),(AL(3),A),(BE(3),A-k)]
                add(both_signed_budget,4*A+B,'both_signed_orientation_budget')
    if leaf['context_version']=='strict_bulk_2026_11_03_v14':
        add([(13,-1),(GI(6),1)],-F(3,40),'accepted_G_inset_lower_edge')
        add([(13,-1)],-F(17,40),'accepted_G_height_lower')
        add([(3,1),(13,-1)],-F(13,480),'accepted_G_above_B')
        for original in (7,8):add([(2*original,1),(6,-1)],0,'accepted_extra_left_of_D')
        for original in (7,8):add([(2*original,1)],F(5,4),'accepted_extra_x_below_five_fourths')
        for i,(lo,hi) in enumerate(box):
            folded=max(abs(lo),abs(hi));co=min(F(5,12),folded/2)
            add([(AL(i),-1),(AB(i),-co)],-1,'adaptive_folded_chord')
            if i!=0:add([(0,1),(2*i,-1)],0,'accepted_A_leftmost')
        for pair,kind,ch in choices:
            if kind=='inward_row_escape':
                assert pair==(7,8) and box[0][1]<=0 and box[3][0]>=0
                specs=inward_escape_specs(F(11,30))
            elif kind=='alternate_four_escape':specs=alternate_escape_specs(pair,F(1,2))
            elif kind=='general_alternate_escape':specs=general_alternate_specs(pair,F(1,2))
            elif kind=='small_row_escape':specs=small_row_specs(F(1,12))
            elif kind in CAP_KINDS:specs=cap_escape_specs(pair,kind,F(3,5),F(29,60))
            elif kind in CORRELATED_KINDS:specs=small_row_specs(correlated_parameters(kind,F(1))[1])
            elif kind in COLUMN_KINDS:specs=column_specs(pair,kind,F(1))
            else:continue
            entries,rval=specs[ch[0]];add(entries,rval,kind+'_primary')
            for earlier in range(ch[0]):
                entries,rval=specs[earlier]
                add([(k,-v) for k,v in entries],-rval,kind+'_predecessor')
    if leaf['context_version']=='strict_bulk_2026_11_03_v14':
        for pair,kind,ch in choices:
            if kind=='f_side_escape':
                for row,rval in f_side_escape_rows(pair,ch[0],F(3,5)):add(row,rval,'F_side_height_routing')
    if leaf['context_version'] in ('strict_bulk_2026_11_03_v4','strict_bulk_2026_11_03_v5','strict_bulk_2026_11_03_v6','strict_bulk_2026_11_03_v7','strict_bulk_2026_11_03_v14'):
        cuts=leaf['circle_cuts'];assert type(cuts) is list and len(cuts)<=48
        seen=set()
        for cut in cuts:
            assert type(cut) is list and len(cut)==6
            original,s,t,pn,qn,power=cut
            assert all(type(z) is int for z in cut)
            assert 0<=original<9 and s in (-1,1) and t in (-1,1)
            assert power==20 and (pn or qn)
            assert abs(pn)<=1<<power and abs(qn)<=1<<power
            assert tuple(cut) not in seen;seen.add(tuple(cut))
            p=F(pn,1<<power);q=F(qn,1<<power)
            # Cauchy--Schwarz and ORIGINAL corner containment imply this
            # rational-direction support bound. The floating producer's
            # candidate point, normal accuracy and norm check are untrusted.
            rhs=roots(Q*(p*p+q*q))[1]
            add([(2*original,p),(2*original+1,q),
                 (AL(original),(s*p+t*q)/2),(BE(original),(s*q-t*p)/2)],
                rhs,'adaptive_original_corner_support')
    else:assert 'circle_cuts' not in leaf
    assert all(j<index for j in weights)
    bounds=[RHO]*18+[F(1)]*36+([2*RHO,2*RHO,F(1),F(1),F(1),F(1)]*((n-54)//6))
    reserve=(-bb-sum(c*abs(r) for c,r in zip(bounds,rr)))/(1<<40)
    assert reserve>0,('nonpositive exact rational leaf',str(reserve),leaf['path'],used)
    return reserve,None

def replay_leaf(leaf):
    if leaf.get('context_version')!='strict_bulk_2026_11_03_v14':
        import weak_outer_numeric_strict_bulk_v13_verify as previous_frozen
        return previous_frozen.replay_leaf(leaf)
    if leaf.get('context_version')=='strict_bulk_2026_11_03_v12':
        import weak_outer_numeric_strict_bulk_v12_verify as previous_v12
        return previous_v12.replay_leaf(leaf)
    if leaf.get('context_version')=='strict_bulk_2026_11_03_v11':
        import weak_outer_numeric_strict_bulk_v11_verify as previous_v11
        return previous_v11.replay_leaf(leaf)
    if leaf.get('context_version')=='strict_bulk_2026_11_03_v10':
        import weak_outer_numeric_strict_bulk_v10_verify as previous_v10
        return previous_v10.replay_leaf(leaf)
    if leaf.get('context_version')=='strict_bulk_2026_11_03_v9':
        import weak_outer_numeric_strict_bulk_v9_verify as previous
        return previous.replay_leaf(leaf)
    return replay_current_leaf(leaf)


def verify_partition(data,root_side=None):
    """Check that proved leaves plus recorded frontier cover the requested root.

    Every analytic escape node is interpreted in first-satisfied order;
    its predecessor closed complements retain the exact union. Older leaf
    contexts prove supersets of these ordered cells and remain sufficient.
    Frontier terminals remain explicitly unproved.  This is a coverage audit,
    not a replacement for their missing contradictions.
    """
    tree={};prefix=[] if root_side is None else [['angle',3,root_side]]
    for kind,items in (('leaf',data['leaves']),('frontier',data['frontier'])):
        for item in items:
            path=item['path'];assert path[:len(prefix)]==prefix
            # Validate rational thresholds and the positive-D premise even
            # on unproved frontier paths; a structural tree alone is not
            # enough to justify its stated original interval coverage.
            reconstruct(path)
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
        if action in ('angle','position','angle_cut','position_cut'):expected={0,1}
        elif action=='proxy':expected={(axis,sg) for axis in (0,1) for sg in (-1,1)}
        elif action=='inward_row_escape':
            assert k==(7,8);expected={(branch,) for branch in range(10)}
        elif action=='alternate_four_escape':
            alternate_chain(k);expected={(branch,) for branch in range(8)}
        elif action=='general_alternate_escape':
            general_alternate_specs(k,F(1,2));expected={(branch,) for branch in range(8)}
        elif action=='f_side_escape':
            assert k in ((5,7),(5,8));expected={(branch,) for branch in range(8)}
        elif action=='small_row_escape':
            assert k==(7,8);expected={(branch,) for branch in range(8)}
        elif action in CAP_KINDS:expected={(branch,) for branch in range(4)}
        elif action in CORRELATED_KINDS:
            assert k==(7,8);expected={(branch,) for branch in range(8)}
        elif action in COLUMN_KINDS:
            expected={(branch,) for branch in range(len(column_specs(k,action,F(1))))}
        elif action in ('row_escape','lower_escape','asymmetric_escape','positive_row_escape'):
            assert k in ((2,7),(2,8)) if action=='lower_escape' else k in ((1,7),(1,8))
            expected={(branch,) for branch in range(2 if action=='lower_escape' else 6)}
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
    assert data['schema'] in ('strict-bulk-2026-11-03-v1','strict-bulk-2026-11-03-v2','strict-bulk-2026-11-03-v3','strict-bulk-2026-11-03-v4','strict-bulk-2026-11-03-v5','strict-bulk-2026-11-03-v6','strict-bulk-2026-11-03-v7','strict-bulk-2026-11-03-v9','strict-bulk-2026-11-03-v10','strict-bulk-2026-11-03-v11','strict-bulk-2026-11-03-v12','strict-bulk-2026-11-03-v13','strict-bulk-2026-11-03-v14')
    assert data.get('root_side')==args.root_side
    partition=verify_partition(data,args.root_side)
    indices=list(range(0,len(data['leaves']),args.stride))
    if args.limit is not None:indices=indices[:args.limit]
    least=None;terminals={};checked=0
    for i in indices:
        reserve,terminal=replay_leaf(data['leaves'][i]);checked+=1
        if terminal:terminals[terminal]=terminals.get(terminal,0)+1
        else:least=reserve if least is None else min(least,reserve)
        if checked%100==0:print('exact leaf samples',checked,'seconds',round(time.time()-start,2),flush=True)
    complete=checked==len(data['leaves']) and not data['frontier']
    out={'schema':'strict-bulk-2026-11-03-v14-independent-replay','status':'PASS','target_transverse':'2/3','checked_leaves':checked,'available_leaves':len(data['leaves']),'frontier':len(data['frontier']),'whole_mask_closed':False,'requested_root_closed':complete,'coverage_verified':True,'escape_child_semantics':'first satisfied primary halfspace; predecessor closed complements in v5/v6/v7/v14 leaves','coverage_includes_unproved_frontier':bool(data['frontier']),'partition':partition,'root_side':args.root_side,'direct_terminals':terminals,'minimum_rational_reserve':str(least),'seconds':time.time()-start,'discovery_sha256':hashlib.sha256(args.discovery.read_bytes()).hexdigest()}
    if args.report:args.report.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
