"""Complete exact four-parameter near-extra screen for the strict-middle
zero-channel S123 frame. All arithmetic is outward integer interval
arithmetic. No floating point, sample or external solver is used.
"""
from collections import Counter
from math import isqrt
N=1<<40
def dn(p,q=N):return p//q
def up(p,q=N):return -((-p)//q)
def I(p,q=1):return dn(p*N,q),up(p*N,q)
def add(a,b):return a[0]+b[0],a[1]+b[1]
def neg(a):return -a[1],-a[0]
def sub(a,b):return add(a,neg(b))
def mul(a,b):
 z=[a[0]*b[0],a[0]*b[1],a[1]*b[0],a[1]*b[1]]
 return dn(min(z)),up(max(z))
def div(a,b):
 assert b[0]>0
 return mul(a,(dn(N*N,b[1]),up(N*N,b[0])))
def half(a):return dn(a[0],2),up(a[1],2)
def square(a):
 z=[a[0]*a[0],a[1]*a[1]]
 return dn(0 if a[0]<=0<=a[1] else min(z)),up(max(z))
def absolute(a):
 return (0,max(-a[0],a[1])) if a[0]<=0<=a[1] else ((-a[1],-a[0]) if a[1]<0 else a)
def cs(z):
 l,h=z
 return ((dn((N*N-h*h)*N,N*N+h*h),up((N*N-l*l)*N,N*N+l*l)),(dn(2*l*N*N,N*N+l*l),up(2*h*N*N,N*N+h*h)))
one=I(1);hh=I(1,2)
def check(box):
 a,b,z,V=box
 # A necessary disk-intersection condition in E's actual own frame.
 da=max(0,absolute(a)[0]-N//2);db=max(0,absolute(b)[0]-N//2)
 if 64*(da*da+db*db)>N*N:return 'empty',1
 c,s=cs(z)
 X=sub(mul(a,c),mul(b,s));Y=add(mul(a,s),mul(b,c));rad=half(add(c,s))
 eps=div(square(V),I(4));d=add(one,eps)
 rects=[(sub(eps,one),eps,neg(V),sub(one,V)),(eps,d,I(-79,200),hh)]
 for i,(xl,xh,yl,yh) in enumerate(rects):
  ru0=add(mul(xl,c),mul(yl,s));ru1=add(mul(xh,c),mul(yh,s))
  rv0=sub(mul(yl,c),mul(xh,s));rv1=sub(mul(yh,c),mul(xl,s))
  gaps=[sub(add(X,rad),xl),sub(add(xh,rad),X),sub(add(Y,rad),yl),sub(add(yh,rad),Y),sub(add(a,hh),ru0),sub(add(ru1,hh),a),sub(add(b,hh),rv0),sub(add(rv1,hh),b)]
  m=min(g[0] for g in gaps)
  if m>0:return i,m
 al=div(sub(one,eps),d);bl=div(V,d)
 H=add(mul(al,c),mul(bl,s));K=sub(mul(bl,c),mul(al,s))
 lr=half(add(H,absolute(K)))
 cen=add(d,hh)
 le=neg(mul(cen,H));lj=neg(mul(cen,K))
 eg=neg(add(mul(H,a),mul(K,b)));ej=sub(mul(K,a),mul(H,b))
 gaps=[sub(add(eg,lr),d),sub(add(add(d,one),lr),eg),add(add(ej,lr),hh),sub(add(hh,lr),ej),sub(add(add(a,hh),lr),le),sub(add(add(le,lr),hh),a),sub(add(add(b,hh),lr),lj),sub(add(add(lj,lr),hh),b)]
 m=min(g[0] for g in gaps)
 if m>0:return 2,m
 return None
stack=[(((-5*N//8,5*N//8),(-5*N//8,5*N//8),(0,N),(I(1,50)[0],I(13,100)[1])),0)]
cnt=Counter();mins={0:N,1:N,2:N};vis=0;depth=0
while stack:
 box,dep=stack.pop();vis+=1;r=check(box)
 if r is not None:
  key,m=r;cnt[key]+=1;depth=max(depth,dep)
  if key!='empty':mins[key]=min(mins[key],m)
  continue
 if dep>=76:
  print('UNRESOLVED',box,'depth',dep,'counts',dict(cnt),'visited',vis,flush=True);raise SystemExit(2)
 widths=[box[0][1]-box[0][0],box[1][1]-box[1][0],(box[2][1]-box[2][0])*5//4,(box[3][1]-box[3][0])*125//11]
 j=max(range(4),key=lambda k:widths[k]);lo,hi=box[j];mid=(lo+hi)//2
 if mid==lo:raise RuntimeError('precision')
 l=list(box);r=list(box);l[j]=(lo,mid);r[j]=(mid,hi)
 stack.append((tuple(r),dep+1));stack.append((tuple(l),dep+1));cnt['split']+=1
 if vis%200000==0:print('PROGRESS',vis,dict(cnt),dep,len(stack),flush=True)
assert cnt==Counter({'split':11008,2:5442,'empty':163,1:4126,0:1278})
assert vis==22017 and depth==32
assert mins=={0:20622436,1:4372443,2:471919}
assert min(mins.values())>0
print('PASS',dict(cnt),'vis',vis,'depth',depth,'mins',mins,'denominator',N,flush=True)

