#!/usr/bin/env python3
"""Independent Fraction replay of the joint five-square interval cover.

Imports no joint producer or its integer arithmetic. All endpoints are exact
rationals; radicals have independently computed 60-bit dyadic enclosures.
Both the ordinary interval evaluation and a centered mean-value bound are
checked. A checkpoint is never reported as a complete cover.
"""
from fractions import Fraction as F
from pathlib import Path
from copy import deepcopy
import hashlib,json,sys,time
from interval_fraction import I

DIM=4
def root(x):return x.sqrt(60)
def span(values):return I(min(x.lo for x in values),max(x.hi for x in values))
def symmetric(x):
    h=max(abs(x.lo),abs(x.hi));return I(-h,h)
def overlap(x,y):return I(max(x.lo,y.lo),min(x.hi,y.hi))
def constant_zero(x):return x.lo==x.hi==0

class A:
    def __init__(self,x,der=None):
        self.x=I(x);self.der=tuple(I(0) for _ in range(DIM)) if der is None else tuple(I(q) for q in der)
    def __add__(self,y):
        y=as_a(y);return A(self.x+y.x,[p+q for p,q in zip(self.der,y.der)])
    __radd__=__add__
    def __neg__(self):return A(-self.x,[-q for q in self.der])
    def __sub__(self,y):return self+-as_a(y)
    def __rsub__(self,y):return as_a(y)+-self
    def __mul__(self,y):
        y=as_a(y);return A(self.x*y.x,[p*y.x+self.x*q for p,q in zip(self.der,y.der)])
    __rmul__=__mul__
    def __truediv__(self,y):
        y=as_a(y);assert y.x.lo>0
        return A(self.x/y.x,[(p-self.x*q/y.x)/y.x for p,q in zip(self.der,y.der)])
    def __rtruediv__(self,y):return as_a(y)/self
    def sq(self):return A(self.x.sq(),[2*self.x*q for q in self.der])
    def absolute(self):
        if self.x.lo>0:return self
        if self.x.hi<0:return -self
        return A(self.x.abs(),[symmetric(q) for q in self.der])

def as_a(x):return x if isinstance(x,A) else A(x)
def union(branches):
    return A(span([p.x for p in branches]),[span([p.der[j] for p in branches]) for j in range(DIM)])
def least(branches):
    low=min(p.x.lo for p in branches);high=min(p.x.hi for p in branches)
    possible=[p for p in branches if p.x.lo<=high]
    return A(I(low,high),[span([p.der[j] for p in possible]) for j in range(DIM)])
def greatest(branches):return -least([-p for p in branches])
def length(v):
    val=root(v[0].x.sq()+v[1].x.sq())
    lips=[symmetric(root(v[0].der[j].sq()+v[1].der[j].sq())) for j in range(DIM)]
    if val.lo>0:
        ders=[overlap((v[0].x*v[0].der[j]+v[1].x*v[1].der[j])/val,lips[j]) for j in range(DIM)]
    else:
        ders=lips
    return A(val,ders)
def product(v,w):return v[0]*w[0]+v[1]*w[1]
def area(v,w):return v[0]*w[1]-v[1]*w[0]
def times(k,v):return [k*v[0],k*v[1]]
def support(v,axis):
    return (product(v,axis).absolute()+area(v,axis).absolute())/(2*length(axis))
def support_total(vectors,axis):return sum((support(v,axis) for v in vectors),A(0))

def orientation_min(vectors,endpoint=False):
    """An enclosure of one genuine minimum over a fixed frame interval."""
    axis0=[[A(1),A(F(-7,100))],[A(1),A(F(7,100))]] if endpoint else [[A(1),A(0)]]
    boundaries=[support_total(vectors,ax) for ax in axis0]
    values=list(boundaries);uncertain_zero=False
    for vec in vectors:
        xx,yy=vec;vx,vy=xx.x,yy.x
        if constant_zero(vx) and constant_zero(vy):continue
        ux,uy=vx.abs(),vy.abs()
        if endpoint and uy.lo>(F(7,100)*ux).hi and ux.lo>(F(7,100)*uy).hi:continue
        if constant_zero(vx):direction=[A(0),A(1)]
        elif constant_zero(vy):direction=[A(1),A(0)]
        else:direction=vec
        if length(direction).x.lo<=0:
            uncertain_zero=True
        else:values.append(support_total(vectors,direction))
    hi=min(v.x.hi for v in boundaries)
    lo=F(0) if uncertain_zero else min(v.x.lo for v in values)
    lo=max(lo,sum(length(v).x.lo for v in vectors)/2)
    assert lo<=hi
    lips=[]
    for j in range(DIM):
        lip=sum((root(v[0].der[j].sq()+v[1].der[j].sq()) for v in vectors),I(0))
        lips.append(symmetric(lip))
    if uncertain_zero:
        ders=lips
    else:
        eligible=[v for v in values if v.x.lo<=hi]
        ders=[overlap(span([v.der[j] for v in eligible]),lips[j]) for j in range(DIM)]
    return A(I(lo,hi),ders)

Q=F(1105,256)
R=A(root(I(Q)))
CENTER_RADIUS=A(root(I(Q-F(1,4)))-F(1,2))

def square_center_bound(v,axis):
    dn=length(axis)
    p=(product(v,axis)/dn).absolute();q=(area(v,axis)/dn).absolute()
    big=greatest([p,q]);small=least([p,q])
    edge=CENTER_RADIUS*big
    vertex=R*length(v)-(big+small)/2
    discriminator=big.sq()-(4*Q-1)*small.sq()
    if discriminator.x.lo>=0:answer=edge
    elif discriminator.x.hi<=0:answer=vertex
    else:answer=union([edge,vertex])
    length_v=length(v).x;angle_den=1+axis[1].x.sq();der=[]
    for j in range(DIM):
        speed=root(v[0].der[j].sq()+v[1].der[j].sq())
        turn=(axis[1].der[j]/angle_den).abs()
        bound=symmetric(CENTER_RADIUS.x*(speed+length_v*turn))
        der.append(overlap(answer.der[j],bound))
    return A(answer.x,der)

def boxed_bound(v,axis,box,weights):
    lox,hix,loy,hiy=box
    lx,hx,ly,hy=weights
    moved=[v[0]+lx-hx,v[1]+ly-hy]
    return square_center_bound(moved,axis)+hx*hix-lx*lox+hy*hiy-ly*loy

def unfixed_bound(v,penalties,endpoint=False,box=None):
    cost=orientation_min(penalties,endpoint)
    vertex=R*length(v)-orientation_min([*penalties,v],endpoint)
    radial=CENTER_RADIUS*length(v)-cost
    candidates=[vertex,radial]
    if box is not None:
        xl,xh,yl,yh=box
        rectangle=(xl+xh)*v[0]/2+(yl+yh)*v[1]/2+(xh-xl)*v[0].absolute()/2+(yh-yl)*v[1].absolute()/2
        candidates.append(rectangle-cost)
    return least(candidates)

def evaluate(box,certificate,owners):
    vv=[]
    for j in range(DIM):
        dd=[0]*DIM;dd[j]=1
        vv.append(A(I(box[2*j],box[2*j+1]),dd))
    return evaluate_mapped(vv,certificate,owners)

def evaluate_mapped(vv,certificate,owners,central_owned=False,
                    shoulder_central_owned=(False,False),central_owner_side=1):
    assert len(shoulder_central_owned)==2
    assert all(isinstance(flag,bool) for flag in shoulder_central_owned)
    assert all(not flag or owners[i]=='E' for i,flag in enumerate(shoulder_central_owned))
    assert central_owner_side in (0,1)
    wleft,wright,zleft,zright=vv
    denominator=certificate['den'];assert denominator==4096
    pars=certificate['p'];assert len(pars)==7 and all(isinstance(k,int) and k>=0 for k in pars)
    kleft,kright,mleft,mright,floor,qleft,qright=[F(k,denominator) for k in pars]
    assert len(certificate['faces'])==2
    faces=[]
    for entry in certificate['faces']:
        assert len(entry)==4 and all(isinstance(k,int) and k>=0 for k in entry)
        faces.append([F(k,denominator) for k in entry])
    answer=A(F(27,2)-floor/10+max(qleft,qright)/8-F(211,2))
    for i,w,z,k,m,q in [(0,wleft,zleft,kleft,mleft,qleft),(1,wright,zright,kright,mright,qright)]:
        horizontal=1 if i else -1
        n=[-horizontal*w,A(1)];central=[A(horizontal),z]
        endpoint_vector=[horizontal*(46+k*w),A(q-k)]
        shoulder_vector=[horizontal*(m-k*w),k+m*z]
        axis=[A(1),horizontal*w]
        end_costs=[[A(46),A(0)],times(k,n)]
        shoulder_costs=[times(m,central),times(k,n)]
        exx=(F(89,60),F(91,60)) if i else (F(-91,60),F(-89,60))
        sxx=(F(23,30),F(13,12)) if i else (F(-13,12),F(-23,30))
        eb=(*exx,F(-1,8),F(1,8));sb=(*sxx,F(25,32),F(21,16))
        if owners[i]=='E':
            main=boxed_bound(endpoint_vector,axis,eb,faces[i])-support_total(end_costs,axis)
            if shoulder_central_owned[i]:
                ff=certificate['central_shoulder_faces'];assert len(ff)==2
                entry=ff[i];assert len(entry)==4 and all(isinstance(k,int) and k>=0 for k in entry)
                central_axis=[A(1),horizontal*z]
                shoulder=boxed_bound(shoulder_vector,central_axis,sb,[F(k,denominator) for k in entry])-support_total(shoulder_costs,central_axis)
            else:
                shoulder=unfixed_bound(shoulder_vector,shoulder_costs,box=sb)
        else:
            main=unfixed_bound(endpoint_vector,end_costs,True,eb)
            shoulder=boxed_bound(shoulder_vector,axis,sb,faces[i])-support_total(shoulder_costs,axis)
        answer=answer+main+shoulder
    center=[A(mleft-mright),floor-mleft*zleft-mright*zright]
    cp=[[A(-mleft),mleft*zleft],[A(mright),mright*zright],[A(0),A(floor)]]
    pbox=(F(-29,60),F(29,60),F(3,5),F(91,60))
    if central_owned:
        ff=certificate['central_faces'];assert len(ff)==4 and all(isinstance(k,int) and k>=0 for k in ff)
        axis=[A(1),zright if central_owner_side==1 else -zleft]
        pp=boxed_bound(center,axis,pbox,[F(k,denominator) for k in ff])-support_total(cp,axis)
    else:pp=unfixed_bound(center,cp,box=pbox)
    return answer+pp

def upper(box,certificate,owner):
    full=evaluate(box,certificate,owner)
    mid=[(box[2*j]+box[2*j+1])/2 for j in range(DIM)]
    at=evaluate(tuple(t for m in mid for t in [m,m]),certificate,owner).x
    for j,m in enumerate(mid):at=at+full.der[j]*I(box[2*j]-m,box[2*j+1]-m)
    return min(full.x.hi,at.hi)

def initial_roots(owner):
    domains=[(F(-2,3),F(6)) if o=='R' else (F(-1,14),F(1,14)) for o in owner]+[(F(-6),F(6))]*2
    boxes=[];eps=F(1,64)
    for j in range(4):
        for cut in [(domains[j][0],-eps),(eps,domains[j][1])]:
            row=[]
            for i in range(4):row.extend(((-eps,eps) if i<j else (cut if i==j else domains[i])))
            boxes.append(tuple(row))
    return boxes

def verify(data,allow_incomplete=False,progress=False):
    assert data['type']=='joint_five_interval_cover_v2'
    owner=data['owner'];assert owner in ['RR','RE','EE']
    assert data['Q']=='1105/256' and data['T_twice']=='211/2'
    assert data['central_slope_band']==['-6','6'] and data['sharp_cube_epsilon']=='1/64'
    assert data['central_x_band']==['-29/60','29/60']
    assert data['roots']==list(range(8))
    nodes=data['nodes'];certificates=data['certificates'];seen=set();leaves=analytic=missing=0;largest=None;started=last=time.monotonic()
    todo=list(zip(range(8),initial_roots(owner)))
    while todo:
        index,expected=todo.pop();assert isinstance(index,int) and index not in seen and 0<=index<len(nodes);seen.add(index)
        row=nodes[index];box=tuple(map(F,row['box']));assert box==expected
        if 'children' in row:
            assert 'certificate' not in row and 'terminal' not in row
            j=row['split'];assert isinstance(j,int) and 0<=j<4
            children=row['children'];assert len(children)==2 and children[0]!=children[1]
            m=(box[2*j]+box[2*j+1])/2;left=list(box);right=list(box);left[2*j+1]=m;right[2*j]=m
            todo.extend([(children[0],tuple(left)),(children[1],tuple(right))])
        elif 'terminal' in row:
            assert row['terminal']=='positive_joint_triangle' and 'certificate' not in row
            assert box[4]>=0 and box[6]>=0
            x,y=box[5],box[7];assert max(x,y)**2+2*x*y<=1;analytic+=1
        elif 'certificate' in row:
            ci=row['certificate'];assert isinstance(ci,int) and 0<=ci<len(certificates)
            computed=upper(box,certificates[ci],owner)
            assert computed<0,(owner,index,float(computed),box)
            if 'upper' in row:assert F(row['upper'])<0
            largest=computed if largest is None else max(largest,computed);leaves+=1
        else:
            assert allow_incomplete,'unclosed leaf';missing+=1
        now=time.monotonic()
        if progress and now-last>25:
            print('REPLAY',owner,'interval leaves',leaves,'analytic',analytic,'missing',missing,'seconds',round(now-started,1),flush=True);last=now
    assert len(seen)==len(nodes)
    assert leaves+analytic==data['closed']
    if not allow_incomplete:
        assert missing==0 and data['remaining']==0
        assert data['proof_status']=='producer_complete_pending_independent_replay'
    return {'owner':owner,'interval_leaves':leaves,'analytic_leaves':analytic,'unclosed_leaves':missing,'largest_replayed_upper':None if largest is None else str(largest),'complete':missing==0}

def main():
    path=Path(sys.argv[1]);allow='--allow-incomplete' in sys.argv
    raw=path.read_bytes();data=json.loads(raw)
    answer=verify(data,allow,True);answer['sha256']=hashlib.sha256(raw).hexdigest();answer['arithmetic']='exact Fraction intervals with60-bit radical enclosures';answer['proof_status']='independent_cover_replay_passed' if answer['complete'] else 'incomplete_checkpoint_leaves_replayed'
    output=path.with_name(path.stem+'_fraction_replay.json');output.write_text(json.dumps(answer,indent=2)+'\n');print(json.dumps(answer),flush=True)

if __name__=='__main__':main()
