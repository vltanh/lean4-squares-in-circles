#!/usr/bin/env python3
"""Exact dual bounds for a quantitative two-group angle neighborhood.

This extends the fixed-frame conditional theorem, without changing any
previously reviewed certificate. All proof comparisons use rational bounds.
"""
from fractions import Fraction as F
from contact_family import family
from isolate_contact_root import I, certificate
from check_fixed_orientation_stress import R, solve_intervals

if not __debug__:
    raise RuntimeError('Run without -O: this certificate uses assertions.')

DISKS=[(0,1,1),(2,1,1),(3,1,-1),(5,1,-1),(6,-1,-1),(7,-1,-1),(7,-1,1),(9,-1,1),(10,-1,1),(10,1,1)]
# i,j, owner, owner axis, sign
EDGES=[(0,1,0,1,-1),(0,2,0,0,1),(0,10,0,0,-1),(1,4,1,1,-1),(2,3,2,1,-1),(3,4,3,0,-1),(4,5,4,1,-1),(4,8,4,0,-1),(5,6,5,0,-1),(6,7,7,1,1),(7,8,7,0,1),(7,9,7,1,1),(8,9,9,1,1),(9,10,9,0,1)]
BOUNDARY=[0,2,3,5,6,7,9,10]

def dot(a,b):return sum(x*y for x,y in zip(a,b))
def neg(a):return tuple(-x for x in a)
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def scale(t,a):return tuple(t*x for x in a)
def norm2(a):return dot(a,a)
def abs_upper(x):return max(abs(x.lo),abs(x.hi))

class D2:
    """Value, gradient and Hessian with outward rational interval entries."""
    def __init__(self,v,g=None,h=None):
        if isinstance(v,D2):self.v,self.g,self.h=v.v,v.g,v.h;return
        self.v=R(v)
        self.g=[R(0),R(0)] if g is None else [R(z) for z in g]
        self.h=[[R(0),R(0)],[R(0),R(0)]] if h is None else [[R(z) for z in row] for row in h]
    def __add__(self,b):
        b=D2(b);return D2(self.v+b.v,[self.g[i]+b.g[i] for i in range(2)],[[self.h[i][j]+b.h[i][j] for j in range(2)] for i in range(2)])
    __radd__=__add__
    def __neg__(self):return D2(-self.v,[-z for z in self.g],[[-z for z in row] for row in self.h])
    def __sub__(self,b):return self+-D2(b)
    def __rsub__(self,b):return D2(b)+-self
    def __mul__(self,b):
        b=D2(b);return D2(self.v*b.v,[self.g[i]*b.v+self.v*b.g[i] for i in range(2)],[[self.h[i][j]*b.v+self.g[i]*b.g[j]+self.g[j]*b.g[i]+self.v*b.h[i][j] for j in range(2)] for i in range(2)])
    __rmul__=__mul__
    def reciprocal(self):
        iv=R(1)/self.v;iv2=iv*iv;iv3=iv2*iv
        return D2(iv,[-g*iv2 for g in self.g],[[2*self.g[i]*self.g[j]*iv3-self.h[i][j]*iv2 for j in range(2)] for i in range(2)])
    def __truediv__(self,b):return self*D2(b).reciprocal()
    def __rtruediv__(self,b):return D2(b)*self.reciprocal()

def frame(t):
    c=(1-t*t)/(1+t*t);s=2*t/(1+t*t)
    return ((c,s),(-s,c))

def geometry(ta,tb):
    zero,one=ta*0,ta*0+1
    frames=[((one,zero),(zero,one))]*7+[frame(ta)]*2+[frame(tb)]*2
    ca,sa=frames[7][0];cb,sb=frames[9][0]
    ka=(1+ca+sa)/2;kb=(1+cb+sb)/2
    cd=ca*cb+sa*sb;sd=ca*sb-sa*cb
    kd=(1+cd+sd)/2 # Used only in the local region alpha < beta.
    widths=[one,one,kb,one,one,one,one,ka,one,ka,one,kd,kd,one]
    return frames,widths,cd

def active_matrix(box):
    _,points,angles,_=family(box[0],box[1],lambda x:x.sqrt())
    tb=angles[1][1]/(1+angles[1][0])
    ta=D2(box[1],[1,0]);tb=D2(tb,[0,1])
    frames,widths,_=geometry(ta,tb)
    coordinates=[(i,k) for i in range(11) for k in range(2) if (i,k)!=(1,0)]
    slot={key:j for j,key in enumerate(coordinates)}
    rows=[]
    for i,e,f in DISKS:
        offset=scale(F(1,2),add(scale(e,frames[i][0]),scale(f,frames[i][1])))
        vertex=add(tuple(D2(x) for x in points[i]),offset);value=-norm2(vertex)
        row=[R(0) for _ in range(24)]
        for k in range(2):row[slot[i,k]]=-2*vertex[k].v
        row[21],row[22]=value.g;row[23]=R(1);rows.append(row)
    for edge,width in zip(EDGES,widths):
        i,j,o,axis,sign=edge;normal=scale(sign,frames[o][axis])
        delta=tuple(D2(y-x) for x,y in zip(points[i],points[j]));slack=dot(normal,delta)-width
        row=[R(0) for _ in range(24)]
        for k in range(2):
            if (i,k) in slot:row[slot[i,k]]=-normal[k].v
            if (j,k) in slot:row[slot[j,k]]=normal[k].v
        row[21],row[22]=slack.g;rows.append(row)
    return [[rows[j][i] for j in range(24)] for i in range(24)]

def dual(ta,tb,weights):
    """A lower bound q >= D for arbitrary centers satisfying 14 halfspaces.

The two variable-angle edge weights are adjusted to balance the three
squares with no disk weight. All other weights are constant.
"""
    frames,widths,cd=geometry(ta,tb)
    ca,sa=frames[7][0];cb,sb=frames[9][0]
    lam=[D2(w) for w in weights[:10]];mu=[D2(w) for w in weights[10:]]
    A,B=mu[0],mu[5]
    mu[3]=mu[6]=A;mu[7]=B
    mu[10]=B*cb/cd;mu[12]=B*sa/cd
    zero=ta*0;forces=[(zero,zero) for _ in range(11)]
    L=[zero for _ in range(11)];V=[(zero,zero) for _ in range(11)]
    total=zero+F(1,2)
    for weight,(i,e,f) in zip(lam,DISKS):
        offset=scale(F(1,2),add(scale(e,frames[i][0]),scale(f,frames[i][1])))
        L[i]=L[i]+weight;V[i]=add(V[i],scale(weight,offset))
    for weight,(i,j,o,axis,sign),width in zip(mu,EDGES,widths):
        normal=scale(sign,frames[o][axis]);forces[i]=add(forces[i],scale(-weight,normal));forces[j]=add(forces[j],scale(weight,normal))
        total=total+weight*width
    for i in BOUNDARY:
        total=total-norm2(add(forces[i],scale(-2,V[i])))/(4*L[i])
    return total

def angle_neighborhood_certificate(verbose=True):
    box=certificate()
    _,_,angles,_=family(box[0],box[1],lambda x:x.sqrt())
    root=[box[1],angles[1][1]/(1+angles[1][0])]
    matrix=active_matrix(box)
    epsilon=F(1,40)
    # Full closed box around each exact root coordinate.  The radius is a
    # rational proof parameter, not an inferred floating tolerance.
    radius=F(1,2000)
    region=[R(x.lo-radius,x.hi+radius) for x in root]
    assert 0 < region[0].lo < region[0].hi < region[1].lo < region[1].hi < 1
    frames,_,cd=geometry(D2(region[0]),D2(region[1]))
    assert cd.v.lo>F(9,10)
    H=F(0);allweights=[]
    for axis in range(2):
        for sign in [-1,1]:
            rhs=[0]*23+[1];rhs[21+axis]=sign*epsilon
            weights=solve_intervals(matrix,rhs)
            assert all(w.lo>F(1,1000) for w in weights)
            value=dual(D2(region[0],[1,0]),D2(region[1],[0,1]),weights)
            H=max(H,*(abs_upper(z) for row in value.h for z in row))
            allweights.append(weights)
    # Taylor: D >= qc + epsilon*d - 2*H*d^2 for the right signed axis,
    # where d=max(|ta-ta*|,|tb-tb*|). This strict rational comparison closes
    # every 0<d<=radius without an interval box needing to resolve qc itself.
    assert H < 20
    assert 2*20*radius < epsilon, (H,radius,epsilon)
    if verbose:
        print('PASS: four nonnegative normalized dual stresses enclose exact roots.')
        print('PASS: every Hessian entry has absolute value < 20 on the angle box.')
        print('PASS: for 0 < d <= 1/2000, q >= qc + (1/40 - 40*d)*d > qc.')
        print('At d=0, the fixed-orientation equality theorem applies.')
    return box,root,allweights,region,H

if __name__=='__main__':angle_neighborhood_certificate()
