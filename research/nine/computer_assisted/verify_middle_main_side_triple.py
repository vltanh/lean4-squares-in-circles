#!/usr/bin/env python3
"""Independent exact replay of both complete middle-main side-triple covers.

Reads only split/leaf tags from untrusted discovery. Roots, signed physical
frames, endpoint resource, owner alternatives and directed arithmetic are
reconstructed here, with integer dyadic intervals and rational midpoints.
No producer import, floating-point evaluation, external solver, Lean or CI.
"""
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
from collections import Counter
import argparse,hashlib,json,time
SCALE=1<<80

def ceildiv(a,b):return -((-a)//b)
def down(x):x=F(x);return x.numerator*SCALE//x.denominator
def up(x):x=F(x);return ceildiv(x.numerator*SCALE,x.denominator)
class I:
    __slots__=('lo','hi')
    def __init__(self,a,b=None,raw=False):
        if raw:self.lo=a;self.hi=a if b is None else b
        else:self.lo=down(a);self.hi=up(a if b is None else b)
        assert self.lo<=self.hi
    def __add__(a,b):b=iv(b);return I(a.lo+b.lo,a.hi+b.hi,True)
    __radd__=__add__
    def __neg__(a):return I(-a.hi,-a.lo,True)
    def __sub__(a,b):return a+-iv(b)
    def __rsub__(a,b):return iv(b)+-a
    def __mul__(a,b):
        b=iv(b);v=(a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi)
        return I(min(v)//SCALE,ceildiv(max(v),SCALE),True)
    __rmul__=__mul__
    def __truediv__(a,b):
        b=iv(b);assert b.lo>0
        return a*I(SCALE*SCALE//b.hi,ceildiv(SCALE*SCALE,b.lo),True)
    def __rtruediv__(a,b):return iv(b)/a
    def sq(a):
        lo=0 if a.lo<=0<=a.hi else min(a.lo*a.lo,a.hi*a.hi)
        hi=max(a.lo*a.lo,a.hi*a.hi)
        return I(lo//SCALE,ceildiv(hi,SCALE),True)
    def ab(a):return I(max(0,a.lo,-a.hi),max(abs(a.lo),abs(a.hi)),True)
    def rt(a):
        assert a.hi>=0
        lo=max(0,a.lo)*SCALE;hi=a.hi*SCALE
        l=isqrt(lo);h=isqrt(hi);h+=h*h<hi
        assert l*l<=lo and h*h>=hi
        return I(l,h,True)
def iv(x):return x if isinstance(x,I) else I(x)
def raw(x):return I(x,raw=True)

def shape(t):
    def point(z):
        z=raw(z);a=1/(1+z.sq()).rt();b=z*a
        return a,b,(a+b)/2,(a-b)/2
    lo=point(t.lo);hi=point(t.hi)
    a=I(hi[0].lo,lo[0].hi,True);b=I(lo[1].lo,hi[1].hi,True)
    h=I(lo[2].lo,hi[2].hi,True);k=I(hi[3].lo,lo[3].hi,True)
    return a,b,h,k,1/(4*h)

Q=F(1105,256);G=F(15,31);A=F(503,480);L=F(29,60);U=F(13,12);RHO=F(91,60)
NEG=-1000*SCALE;POS=1000*SCALE

def div_lower(n,den):
    # A missing axis is represented by +1000, always above retained h.
    if den.hi==0:return POS
    if n.lo>=0:return n.lo*SCALE//den.hi
    if den.lo==0:return NEG
    return n.lo*SCALE//den.lo

def corner_upper(s,X,sign):
    a,b,h,k,gg=s
    dx=(h,sign*k,-h,-sign*k);dy=(-sign*k,h,sign*k,-h)
    bound=up(RHO)
    for xx,yy in zip(dx,dy):
        rad=Q-(X+xx).sq()
        if rad.hi<0:return NEG
        bound=min(bound,rad.rt().hi-yy.lo)
    return bound

def main_clearance_lower(s,sign,D,delta,generic=False,g_floor=None,sigma_floor=None):
    a,b,h,k,gg=s
    reach=h.lo
    if generic or sign<0:reach=min(reach,div_lower(F(1,2)+delta*b,a))
    if generic or sign>0:reach=min(reach,div_lower(F(1,2)+delta*a,b))
    sigma=raw(max(down(1),(h+F(12,25)).lo) if sigma_floor is None else sigma_floor)
    rad=sigma.sq()-raw(D).sq()
    # max(0,.) is a lower bound when the actual center gap is bounded by D.
    disk=I(max(0,rad.lo),max(0,rad.hi),True).rt().lo
    return max((down(G) if g_floor is None else g_floor)+reach,disk)

def endpoint_lower(s,sign,X,base,c):
    a,b,h,k,gg=s
    edge=min(up(A),up(RHO)-c)
    if X.lo+h.lo<=edge:return base
    delta=X-raw(edge)
    def reach(ss):
        rr=div_lower(F(1,2)+delta*b,a) if ss>0 else div_lower(F(1,2)+delta*a,b)
        return min(h.lo,rr)
    wp=c+reach(sign);wm=c+reach(-sign)
    # The opposite signed vertical branch is removed only by this strict test.
    return max(base,wp) if base+wm>0 else base

def directed_pair_upper(s,ss,t,st,D,elo,ehi):
    if elo>ehi:return ehi-elo
    a,b,h,k,gg=s;aa,bb,hh,kk,GG=t;E=I(elo,ehi,True)
    cosine=a*aa+(ss*st)*b*bb
    sine=ss*b*aa-st*a*bb
    sigma=(1+cosine.ab()+sine.ab())/2
    axes=(a*D+ss*b*E,b*D-ss*a*E,aa*D+st*bb*E,bb*D-st*aa*E)
    return max(z.hi for z in axes)-max(SCALE,sigma.lo)

def physical_gap_lower(s,ss,t,st,elo,ehi):
    if elo>ehi:return POS
    E=I(elo,ehi,True)
    co=s[0]*t[0]+ss*st*s[1]*t[1];si=ss*s[1]*t[0]-st*s[0]*t[1]
    sigma=max(SCALE,((1+co.ab()+si.ab())/2).lo)
    axes=((s[0],ss*s[1]),(s[1],-ss*s[0]),(t[0],st*t[1]),(t[1],-st*t[0]))
    bound=POS
    for nx,ny in axes:
        needed=raw(sigma)-ny*E
        candidate=(POS if needed.lo>0 else NEG) if nx.hi==0 else div_lower(needed,nx)
        bound=min(bound,candidate)
    return bound

def shared_height_owner_upper(left,sl,p,sp,right,sr,dl,dr,Z,x,X,pl,yp,ll,lh,rl,rh):
    elo=max(-dl.hi,pl-lh);ehi=min(dl.hi,yp-ll)
    flo=max(-dr.hi,rl-yp);fhi=min(dr.hi,rh-pl)
    if elo>ehi or flo>fhi:return min(ehi-elo,fhi-flo)
    E=I(elo,ehi,True);V=I(flo,fhi,True)
    def owners(a,sa,b,sb):
        return ((a[0],a[1],sa),(a[1],a[0],-sa),(b[0],b[1],sb),(b[1],b[0],-sb))
    def support(a,sa,b,sb):
        co=a[0]*b[0]+sa*sb*a[1]*b[1];si=sa*a[1]*b[0]-sb*a[0]*b[1]
        return max(SCALE,((1+co.ab()+si.ab())/2).lo)
    sL=support(left,sl,p,sp);sR=support(p,sp,right,sr);answer=NEG
    for ia,(nx,mag,sign) in enumerate(owners(left,sl,p,sp)):
        for ib,(mx,mmag,msign) in enumerate(owners(p,sp,right,sr)):
            ny=sign*mag;my=msign*mmag
            one=(nx*dl+ny*E).hi-sL;two=(mx*dr+my*V).hi-sR
            ac=nx*mx;cb=mx*ny;ad=nx*my
            cross=ac*(Z+X)+(cb-ad)*I(pl,yp,True)-cb*raw(ll if sign>0 else lh)+ad*raw(rh if msign>0 else rl)-mx*raw(sL)-nx*raw(sR)
            horizontal=cross.hi
            weighted=POS
            if sign==msign:
                aa=raw(sL)-nx*dl+ny*raw(ll if sign>0 else lh)
                bb=raw(sR)-mx*dr-my*raw(rh if msign>0 else rl)
                weighted=-(mmag*aa+mag*bb).lo
                yl=ll if sign>0 else lh;yr=rh if msign>0 else rl
                expanded=mmag*raw(sL)+mag*raw(sR)-mmag*nx*Z-mag*mx*X+(mag*mx-mmag*nx)*x+sign*mag*mmag*raw(yl-yr)
                weighted=min(weighted,-expanded.lo)
                if ia==ib+2 and ib<2:
                    weighted=min(weighted,(nx*(Z+X)+ny*raw(yr-yl)).hi-sL-sR)
            answer=max(answer,min(one,two,weighted,horizontal))
    return answer

def effective_width_upper(t):
    lo=shape(raw(t.lo));hi=shape(raw(t.hi))
    linear=max((lo[0]/2+F(19,54)*lo[1]).hi,(hi[0]/2+F(19,54)*hi[1]).hi)
    if t.lo<=up(F(19,27)) and t.hi>=down(F(19,27)):
        linear=max(linear,(I(1090).rt()/54).hi)
    curve=(1-hi[0]/2+hi[1]/18).hi
    return min(linear,curve)

def contract_low_floor(left,p,right,Z,x,X,c_left,t_left,t_right):
    psL=effective_width_upper(t_left);psR=effective_width_upper(t_right)
    h_max=min(up(F(8,15)),(1/(4*raw(c_left.lo))).hi)
    hh=raw(h_max);j_left=(hh+(F(1,2)-hh.sq()).rt()).lo
    a0=min(up(F(61,60)),((Q-(1-c_left).sq()).rt()-raw(j_left)).hi)
    zcap=(F(451,810)+raw(psL)).hi;xcap=(F(451,810)+raw(psR)).hi
    total=(1+raw(psL)+raw(psR)).hi
    adaptive=(raw(psR)+F(92,27)*(raw(a0)-F(157,184))).hi
    for unused in range(3):
        x.lo=max(x.lo,down(F(-1,5)),down(F(23,150))-p[4].hi,p[4].lo+left[4].lo-Z.hi,X.lo-p[2].hi-right[2].hi)
        x.hi=min(x.hi,left[2].hi+p[2].hi-Z.lo,X.hi-p[4].lo-right[4].lo)
        Z.lo=max(Z.lo,left[4].lo+p[4].lo-x.hi)
        X.lo=max(X.lo,x.lo+p[4].lo+right[4].lo)
        Z.hi=min(Z.hi,left[2].hi+p[2].hi-x.lo,zcap,total-X.lo)
        X.hi=min(X.hi,x.hi+p[2].hi+right[2].hi,xcap,total-Z.lo,adaptive)
        if x.lo>x.hi or Z.lo>Z.hi or X.lo>X.hi:return None
    return Z,x,X

def low_floor_upper(left,p,right,Z,x,X,c_left,t_left,t_p,t_right,pass_number=0):
    al,bl,hl,kl,gl=left;ap,bp,hp,kp,gp=p;ar,br,hr,kr,gr=right
    dl=x+Z;dr=X-x;answer=NEG;union_lo=POS;union_hi=NEG
    left_low=shape(raw(t_left.lo));p_low=shape(raw(t_p.lo))
    psi_left=effective_width_upper(t_left);psi_right=effective_width_upper(t_right)
    cap_upper=min(up(F(1,60)),(F(27,184)*(F(451,810)-Z+raw(psi_left))).hi,(F(27,184)*(F(451,810)-X+raw(psi_right))).hi,(F(27,184)*(1-Z-X+raw(psi_left)+raw(psi_right))).hi)
    a_left=max(down(F(59,60)),(F(157,184)+F(27,92)*(X-raw(psi_right))).lo)
    h_max=min(up(F(8,15)),(1/(4*raw(c_left.lo))).hi)
    # a(h)=h+sqrt(1/2-h^2) decreases for h>=1/2.
    hh=raw(h_max);j_left=(hh+(F(1,2)-hh.sq()).rt()).lo
    a0_upper=min(up(F(61,60)),((Q-(1-c_left).sq()).rt()-raw(j_left)).hi)
    cap_upper=min(cap_upper,((raw(a0_upper)-raw(a_left))/2).hi)
    if cap_upper<down(F(-1,100000000)):return cap_upper
    for sp in (-1,1):
        delta_p=1-raw(a0_upper)-x
        reach_p=min(hp.lo,div_lower(F(1,2)+delta_p*bp,ap) if sp<0 else div_lower(F(1,2)+delta_p*ap,bp))
        # Solve g1<=hP+9/20-rP exactly, preserving the same P frame.
        axis_allowed=(F(11,25)+t_p*(kp-delta_p)).hi if sp<0 else up(F(11,25))-div_lower(kp+delta_p,t_p)
        allowed_g=min((hp+F(11,25)-raw(reach_p)).hi,axis_allowed)
        if allowed_g<=0:
            answer=max(answer,allowed_g)
            continue
        needed=max(0,(1/(4*raw(allowed_g))-F(1,2)).lo)
        margin_gain=(2*raw(needed).sq()/(1+2*raw(needed))).lo
        delta_p=delta_p+raw(margin_gain)
        yp=(hp+F(1,10)).hi
        c_right=max(down(F(4421,12000)),(F(80669,93000)-c_left+F(64,9)*raw(needed)).lo)
        a_right=max(down(F(59,60)),(F(157,184)+F(27,92)*(Z-raw(psi_left))).lo)+2*needed
        endpoint_rad=Q-(raw(a_right)+F(29927,30000)).sq()
        c_right=POS if endpoint_rad.hi<0 else max(c_right,SCALE-endpoint_rad.rt().hi)
        arc=(4-F(73,30000)+2*raw(needed)-(Q-(1-c_left).sq()).rt()).lo
        assert arc>0
        rad=Q-raw(arc).sq()
        c_right=POS if rad.hi<0 else max(c_right,SCALE-rad.rt().hi)
        for sr in (-1,1):
            rh=corner_upper(right,X,sr);delta=X-A
            rr=min(hr.lo,div_lower(F(1,2)+delta*br,ar) if sr>0 else div_lower(F(1,2)+delta*ar,br))
            horizontal_overlap=X.lo+hr.lo>up(A)
            e_upper=cap_upper
            if horizontal_overlap:e_upper=min(e_upper,(F(9,64)*(raw(rh)-raw(rr)-F(80669,93000)+c_left)).hi)
            if e_upper<down(F(-1,100000000)):
                answer=max(answer,e_upper)
                continue
            e_margin=e_upper;e_upper=max(0,e_upper)
            g_main=(1/(2+4*raw(e_upper))).lo
            xx=I(x.lo,x.hi,True)
            if sp<0:
                xmin=POS if t_p.hi==0 else (1-raw(a0_upper)+raw(margin_gain)-kp+(raw(g_main)-F(11,25))/raw(t_p.hi)).lo
            else:
                xmin=(1-raw(a0_upper)+raw(margin_gain)+kp+t_p*(raw(g_main)-F(11,25))).lo
            xx.lo=max(xx.lo,xmin)
            if xx.lo>xx.hi:
                answer=max(answer,xx.hi-xx.lo)
                continue
            dl=xx+Z;dr=X-xx
            main_h=F(1,2)+raw(e_upper)
            main_k=(F(1,2)-main_h.sq()).rt()
            def main_support(s_low):
                # 1/2+bF H+aF K increases with the outsider folded slope.
                return max(SCALE,(F(1,2)+s_low[1]*main_h+s_low[0]*main_k).lo)
            pl=down(F(-17,50))+main_clearance_lower(p,sp,(x+raw(a0_upper)-F(1,2)-raw(needed)).hi,delta_p,g_floor=g_main,sigma_floor=main_support(p_low))
            rl=max(down(F(3,5)),c_right+rr) if horizontal_overlap else down(F(3,5))
            elo=max(-dr.hi,rl-yp);ehi=min(dr.hi,rh-pl)
            right_margin=min(rh-rl,ehi-elo,directed_pair_upper(p,sp,right,sr,dr,elo,ehi))
            main_axis=(t_p*(kp-delta_p)).hi-(raw(g_main)-F(11,25)).lo if sp<0 else (-kp-delta_p-t_p*(raw(g_main)-F(11,25))).hi
            basic=min(yp-pl,right_margin,main_axis,e_margin-needed,up(F(1,60))-needed,up(F(1,2))-c_right)
            if basic<0:
                answer=max(answer,basic)
                continue
            best_left=NEG
            for sl in (-1,1):
                D=max((Z-L).hi,(raw(a0_upper)-F(1,2)-Z).hi)-needed
                delta_l=raw(min((F(59,60)-Z).lo,(Z+1-raw(a0_upper)).lo)+margin_gain)
                clearance=main_clearance_lower(left,-sl,D,delta_l,Z.lo<up(F(8,15)),g_floor=g_main,sigma_floor=main_support(left_low))
                ll=endpoint_lower(left,-sl,Z,down(F(-17,50))+clearance,c_left.lo)
                lh=corner_upper(left,Z,-sl)
                lo=max(-dl.hi,pl-lh);hi=min(dl.hi,yp-ll)
                gap_left=physical_gap_lower(left,sl,p,sp,lo,hi)
                gap_right=physical_gap_lower(p,sp,right,sr,max(-dr.hi,rl-yp),min(dr.hi,rh-pl))
                new_lo=max(xx.lo,gap_left-Z.hi);new_hi=min(xx.hi,X.hi-gap_right)
                if new_lo>new_hi:
                    best_left=max(best_left,new_hi-new_lo)
                    continue
                xxx=I(new_lo,new_hi,True);ddl=xxx+Z;ddr=X-xxx
                lo=max(-ddl.hi,pl-lh);hi=min(ddl.hi,yp-ll)
                left_margin=min(lh-ll,hi-lo,directed_pair_upper(left,sl,p,sp,ddl,lo,hi),directed_pair_upper(p,sp,right,sr,ddr,max(-ddr.hi,rl-yp),min(ddr.hi,rh-pl)))
                if left_margin>=0:left_margin=min(left_margin,shared_height_owner_upper(left,sl,p,sp,right,sr,ddl,ddr,Z,xxx,X,pl,yp,ll,lh,rl,rh))
                best_left=max(best_left,left_margin)
                chart=min(yp-pl,left_margin,right_margin,main_axis,e_margin-needed,up(F(1,60))-needed,up(F(1,2))-c_right)
                if chart>=0:
                    union_lo=min(union_lo,xxx.lo);union_hi=max(union_hi,xxx.hi)
            branch=min(yp-pl,best_left,right_margin,main_axis,e_margin-needed,up(F(1,60))-needed,up(F(1,2))-c_right)
            answer=max(answer,branch)
    if pass_number<3 and answer>=0 and union_lo<=union_hi and (union_lo>x.lo or union_hi<x.hi):
        return low_floor_upper(left,p,right,Z,I(max(x.lo,union_lo),min(x.hi,union_hi),True),X,c_left,t_left,t_p,t_right,pass_number+1)
    return answer

def margin(box,code,kind):
    tl,tp,tr,Z,x,X,w=[I(*z) for z in box]
    left,p,right=shape(tl),shape(tp),shape(tr)
    al,bl,hl,kl,gl=left;ap,bp,hp,kp,gp=p;ar,br,hr,kr,gr=right
    if kind=='low_floor':
        contracted=contract_low_floor(left,p,right,Z,x,X,w,tl,tr)
        if contracted is None:return NEG
        Z,x,X=contracted
    dl=x+Z;dr=X-x;rows=[]
    if kind=='low_floor':rows.append(x+gp-F(23,150))
    rows.extend((dl-gp-gl,dr-gp-gr,hl+hp-dl,hp+hr-dr))
    if code<len(rows):return rows[code].hi
    assert code==len(rows)
    if kind=='low_floor':return low_floor_upper(left,p,right,Z,x,X,w,tl,tp,tr)
    common=NEG
    for sp in (-1,1):
        needed=0
        if kind=='low_floor':
            delta=-F(1,60)-x
            reach=min(hp.lo,div_lower(F(1,2)+delta*bp,ap) if sp<0 else div_lower(F(1,2)+delta*ap,bp))
            needed=max(0,down(F(1,20))+reach-hp.hi)
        right_height=max(down(F(4421,12000)),(F(80669,93000)-w+F(64,9)*raw(needed)).lo)
        arc=(4-F(73,30000)+2*raw(needed)-(Q-(1-w).sq()).rt()).lo
        assert arc>0
        rad=Q-raw(arc).sq()
        if rad.hi<0:right_height=POS
        else:right_height=max(right_height,SCALE-rad.rt().hi)
        yp=corner_upper(p,x,sp) if kind=='low_right' else (hp+F(1,10)).hi
        pl=down(F(-7,20))+main_clearance_lower(p,sp,(x+F(31,60)).hi,-F(1,60)-x)
        best_left=NEG;best_right=NEG
        for sl in (-1,1):
            D=max((Z-L).hi,(F(31,60)-Z).hi)
            clearance=main_clearance_lower(left,-sl,D,raw(min((F(59,60)-Z).lo,(Z-F(1,60)).lo)),Z.lo<up(F(8,15)))
            base=down(F(-7,20))+clearance
            ll=endpoint_lower(left,-sl,Z,base,w.lo)
            lh=corner_upper(left,Z,-sl)
            elo=max(-dl.hi,pl-lh);ehi=min(dl.hi,yp-ll)
            m=min(lh-ll,ehi-elo,directed_pair_upper(left,sl,p,sp,dl,elo,ehi))
            best_left=max(best_left,m)
        for sr in (-1,1):
            rl=endpoint_lower(right,sr,X,down(F(-113,600)),right_height)
            rh=corner_upper(right,X,sr)
            if kind=='low_right':rh=min(rh,up(F(3,5)))
            elo=max(-dr.hi,rl-yp);ehi=min(dr.hi,rh-pl)
            m=min(rh-rl,ehi-elo,directed_pair_upper(p,sp,right,sr,dr,elo,ehi))
            best_right=max(best_right,m)
        m=min(yp-pl,best_left,best_right,up(F(1,2))-right_height)
        if kind=='low_floor':m=min(m,up(F(1,60))-needed,(F(1,2)-F(80669,93000)+w-F(64,9)*raw(needed)).hi)
        common=max(common,m)
    return common

def root(kind):
    return ((F(0),F(1)),(F(1,27) if kind=='low_floor' else F(0),F(1)),(F(0),F(1)))+((L,U),(F(-23,60),F(23,60)),(L,F(49,80) if kind=='low_right' else U),(F(4421,12000),F(1,2)))

def verify(path,progress=0):
    start=time.monotonic();blob=path.read_bytes();data=json.loads(blob);kind=data['kind'];assert kind in ('low_floor','low_right')
    events=data['events'];assert isinstance(events,list);stack=[(root(kind),0)];counts=Counter();leaves=0;depth=0;least=None
    for j,tag in enumerate(events):
        assert stack,('trailing event',j);assert type(tag) is int,('noninteger tag',j)
        box,d=stack.pop();depth=max(depth,d)
        if tag>=0:
            assert tag<7,('unknown split',j,tag)
            mid=(box[tag][0]+box[tag][1])/2;assert box[tag][0]<mid<box[tag][1]
            a=list(box);b=list(box);a[tag]=(box[tag][0],mid);b[tag]=(mid,box[tag][1])
            stack.append((tuple(b),d+1));stack.append((tuple(a),d+1))
        else:
            code=-tag-1;assert 0<=code<(6 if kind=='low_floor' else 5),('unknown leaf',j,tag)
            m=margin(box,code,kind);assert m<0,('unproved leaf',j,code,str(F(m,SCALE)),box)
            r=-m;least=r if least is None else min(least,r);leaves+=1;counts[code]+=1
        if progress and (j+1)%progress==0:print(json.dumps({'nodes':j+1,'leaves':leaves,'frontier':len(stack),'seconds':time.monotonic()-start}),flush=True)
    assert not stack,('incomplete tree',len(stack));assert len(events)==2*leaves-1
    assert data['nodes']==len(events) and data['leaves']==leaves and data['max_depth']==depth
    return {'status':'EXACT_REPLAY_PASSED','kind':kind,'nodes':len(events),'leaves':leaves,'max_depth':depth,'leaf_rules':dict(sorted(counts.items())),
        'root':[[str(a),str(b)] for a,b in root(kind)],'scale':SCALE,'minimum_exact_reserve':str(F(least,SCALE)),
        'certificate_sha256':hashlib.sha256(blob).hexdigest(),'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'seconds':time.monotonic()-start,'arithmetic':'Directed 80-bit integer dyadics, rational midpoint roots, integer square roots; no floating point',
        'scope':'Original actual cone four-chain and both-weak cone triple with side endpoints; low-right uses yMain>=-7/20, low-floor uses yMain>=-17/50 from the original lower-side theorem. All original nine-square constraints remain in the caller.'}

def main():
    p=argparse.ArgumentParser();base=Path(__file__).resolve().parent
    p.add_argument('--certificate',type=Path,default=base/'middle_main_low_floor_candidate.json');p.add_argument('--report',type=Path);p.add_argument('--progress',type=int,default=0);args=p.parse_args()
    report=verify(args.certificate,args.progress);dest=args.report or args.certificate.with_name(args.certificate.stem+'_exact_replay.json');dest.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2),flush=True)
if __name__=='__main__':main()
