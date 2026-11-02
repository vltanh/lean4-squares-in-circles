"""Directed integer interval evaluation of the joint five-square dual.

Producer-side implementation. A separate Fraction replay is required before
any generated finite cover is promoted to a certificate.
"""
from fractions import Fraction as F
from verify_negative_fork_certificate import V, S

N=4
def hull(xs):return V(min(x.l for x in xs),max(x.h for x in xs),True)
def sym(x):return V(-max(abs(x.l),abs(x.h)),max(abs(x.l),abs(x.h)),True)
def intersect(x,y):return V(max(x.l,y.l),min(x.h,y.h),True)
def zero(x):return x.l==x.h==0

class D:
    def __init__(self,value,grad=None):
        self.v=V(value)
        self.g=tuple(V(0) for _ in range(N)) if grad is None else tuple(V(x) for x in grad)
    def __add__(self,o):
        o=d(o);return D(self.v+o.v,[x+y for x,y in zip(self.g,o.g)])
    __radd__=__add__
    def __neg__(self):return D(-self.v,[-x for x in self.g])
    def __sub__(self,o):return self+-d(o)
    def __rsub__(self,o):return d(o)+-self
    def __mul__(self,o):
        o=d(o);return D(self.v*o.v,[x*o.v+self.v*y for x,y in zip(self.g,o.g)])
    __rmul__=__mul__
    def __truediv__(self,o):
        o=d(o);assert o.v.l>0
        return D(self.v/o.v,[(x*o.v-self.v*y)/o.v.square() for x,y in zip(self.g,o.g)])
    def __rtruediv__(self,o):return d(o)/self
    def square(self):return D(self.v.square(),[2*self.v*x for x in self.g])
    def sqrt(self):
        vv=self.v.sqrt();assert vv.l>0
        return D(vv,[x/(2*vv) for x in self.g])
    def abs(self):
        if self.v.l>0:return self
        if self.v.h<0:return -self
        return D(self.v.abs(),[sym(x) for x in self.g])

def d(x):return x if isinstance(x,D) else D(x)
def choose_hull(xs):return D(hull([x.v for x in xs]),[hull([x.g[j] for x in xs]) for j in range(N)])
def minimum(xs):
    lo=min(x.v.l for x in xs);hi=min(x.v.h for x in xs)
    active=[x for x in xs if x.v.l<=hi]
    return D(V(lo,hi,True),[hull([x.g[j] for x in active]) for j in range(N)])
def maximum(xs):return -minimum([-x for x in xs])
def norm(v):
    vv=(v[0].v.square()+v[1].v.square()).sqrt()
    lips=[sym((v[0].g[j].square()+v[1].g[j].square()).sqrt()) for j in range(N)]
    if vv.l>0:
        return D(vv,[intersect((v[0].v*v[0].g[j]+v[1].v*v[1].g[j])/vv,lips[j]) for j in range(N)])
    return D(vv,lips)
def dot(v,w):return v[0]*w[0]+v[1]*w[1]
def det(v,w):return v[0]*w[1]-v[1]*w[0]
def add(v,w):return [v[0]+w[0],v[1]+w[1]]
def scale(c,v):return [c*v[0],c*v[1]]
def fixed_support(v,axis):return (dot(v,axis).abs()+det(v,axis).abs())/(2*norm(axis))
def fixed_sum(vectors,axis):return sum((fixed_support(v,axis) for v in vectors),D(0))

def free_sum(vectors,limited=False):
    # Minimize one actual support sum over a fixed compact orientation set.
    constants=([D(1),D(F(-7,100))],[D(1),D(F(7,100))]) if limited else ([D(1),D(0)],)
    fixed=[fixed_sum(vectors,ax) for ax in constants]
    candidates=list(fixed);singular=False
    for vv in vectors:
        x,y=vv
        if zero(x.v) and zero(y.v):continue
        ax,ay=x.v.abs(),y.v.abs()
        if limited and ay.l>(F(7,100)*ax).h and ax.l>(F(7,100)*ay).h:continue
        if zero(x.v):axis=[D(0),D(1)]
        elif zero(y.v):axis=[D(1),D(0)]
        else:axis=vv
        if norm(axis).v.l==0:
            singular=True;continue
        candidates.append(fixed_sum(vectors,axis))
    universal=sum((norm(v) for v in vectors),D(0))/2
    upper=min(x.v.h for x in fixed)
    lower=0 if singular else min(x.v.l for x in candidates)
    lower=max(lower,universal.v.l)
    # The derivative of a minimum over a fixed orientation set is enclosed
    # by the derivatives of all possibly minimizing alignment branches.
    lips=[]
    for j in range(N):
        lip=sum((v[0].g[j].square()+v[1].g[j].square()).sqrt() for v in vectors)
        lips.append(sym(lip))  # uniform fixed-frame Lipschitz bound; circumradius <1
    if singular:
        gradients=lips
    else:
        active=[x for x in candidates if x.v.l<=upper]
        gradients=[intersect(hull([x.g[j] for x in active]),lips[j]) for j in range(N)]
    assert lower<=upper
    return D(V(lower,upper,True),gradients)

Q=F(1105,256)
rad=D(V(Q).sqrt());rho=D(V(Q-F(1,4)).sqrt()-F(1,2))
def owned_center(vec,axis):
    den=norm(axis)
    x=(dot(vec,axis)/den).abs();y=(det(vec,axis)/den).abs()
    aa=maximum([x,y]);bb=minimum([x,y])
    test=aa.square()-(4*Q-1)*bb.square()
    side=rho*aa
    circular=rad*norm(vec)-(aa+bb)/2
    if test.v.l>=0:result=side
    elif test.v.h<=0:result=circular
    else:result=choose_hull([side,circular])
    # K_theta is a rotation of one center region contained in the rho-disk.
    # Its support is rho-Lipschitz in the vector, and rho*|v|-Lipschitz in
    # the frame angle. These valid global bounds tame interval dependency.
    le=norm(vec).v;denangle=1+axis[1].v.square();gg=[]
    for j in range(N):
        dv=(vec[0].g[j].square()+vec[1].g[j].square()).sqrt()
        da=(axis[1].g[j]/denangle).abs()
        gg.append(intersect(result.g[j],sym(rho.v*(dv+le*da))))
    return D(result.v,gg)

def center_with_faces(vec,axis,box,nums,den):
    lam=[F(x,den) for x in nums]
    xl,xh,yl,yh=box
    shifted=[vec[0]+lam[0]-lam[1],vec[1]+lam[2]-lam[3]]
    return owned_center(shifted,axis)-xl*lam[0]+xh*lam[1]-yl*lam[2]+yh*lam[3]

def expression(box,cert,owners):
    vals=[]
    for j in range(N):
        gg=[0]*N;gg[j]=1
        vals.append(D(V(box[2*j],box[2*j+1]),gg))
    return mapped_expression(vals,cert,owners)

def mapped_expression(vals,cert,owners,central_owned=False,central_owner_side=1,shoulder_central_owned=(False,False)):
    assert central_owner_side in (0,1) and len(shoulder_central_owned)==2
    assert all(not flag or owners[j]=='E' for j,flag in enumerate(shoulder_central_owned))
    wl,wr,zl,zr=vals
    den=cert['den'];kl,kr,ml,mr,lam,ql,qr=[F(v,den) for v in cert['p']]
    a=F(46);b=F(27,2)
    nl=[wl,D(1)];nr=[-wr,D(1)];dl=[D(-1),zl];dr=[D(1),zr]
    vl=[-a-kl*wl,D(-kl+ql)];vr=[a+kr*wr,D(-kr+qr)]
    sl=[-ml+kl*wl,kl+ml*zl];sr=[mr-kr*wr,kr+mr*zr]
    pc=[D(ml-mr),lam-ml*zl-mr*zr]
    endpoint_other=[[D(a),D(0)]]
    def free_component(vec,other,limited=False,position_box=None):
        cost=free_sum(other,limited)
        choices=[rad*norm(vec)-free_sum([vec,*other],limited),rho*norm(vec)-cost]
        if position_box is not None:
            xl,xh,yl,yh=position_box
            rectangular=((xl+xh)*vec[0]+(yl+yh)*vec[1]+(xh-xl)*vec[0].abs()+(yh-yl)*vec[1].abs())/2
            choices.append(rectangular-cost)
        return minimum(choices)
    parts=[]
    for side,w,z,kn,mn,vv,ss,k,mu in [
        (0,wl,zl,nl,dl,vl,sl,kl,ml),(1,wr,zr,nr,dr,vr,sr,kr,mr)]:
        axis=[D(1),w if side else -w]
        eo=[*endpoint_other,scale(k,kn)];so=[scale(mu,mn),scale(k,kn)]
        eb=(F(89,60),F(91,60),F(-1,8),F(1,8)) if side else (F(-91,60),F(-89,60),F(-1,8),F(1,8))
        sb=(F(23,30),F(13,12),F(25,32),F(21,16)) if side else (F(-13,12),F(-23,30),F(25,32),F(21,16))
        if owners[side]=='E':
            ep=center_with_faces(vv,axis,eb,cert['faces'][side],den)-fixed_sum(eo,axis)
            if shoulder_central_owned[side]:
                sax=[D(1),z if side else -z]
                sp=center_with_faces(ss,sax,sb,cert['central_shoulder_faces'][side],den)-fixed_sum(so,sax)
            else:sp=free_component(ss,so,position_box=sb)
        else:
            ep=free_component(vv,eo,True,eb)
            sp=center_with_faces(ss,axis,sb,cert['faces'][side],den)-fixed_sum(so,axis)
        parts.extend([ep,sp])
    ppen=[scale(ml,dl),scale(mr,dr),[D(0),D(lam)]]
    pbox=(F(-29,60),F(29,60),F(3,5),F(91,60))
    if central_owned:
        paxis=[D(1),zr if central_owner_side else -zl]
        pp=center_with_faces(pc,paxis,pbox,cert['central_faces'],den)-fixed_sum(ppen,paxis)
    else:pp=free_component(pc,ppen,position_box=pbox)
    return b-F(1,10)*lam+max(ql,qr)/8+sum(parts,D(0))+pp-F(211,2)

def ceiling(box,cert,owners):
    whole=expression(box,cert,owners)
    mids=[(box[2*j]+box[2*j+1])/2 for j in range(N)]
    midpoint=tuple(t for m in mids for t in [m,m])
    center=expression(midpoint,cert,owners)
    centered=center.v
    for j,m in enumerate(mids):centered+=whole.g[j]*V(box[2*j]-m,box[2*j+1]-m)
    return min(whole.v.h,centered.h),whole
