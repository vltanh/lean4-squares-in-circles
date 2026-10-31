"""Complete exact five-parameter covers for the positive-channel unique
opposite-circle middle in the original S123 component.

The actual A, actual radial L and contained rotated U strip are retained.
Two additional world rectangles are forbidden to extra interiors by the
proved actual empty-hole winding theorem, not assumed occupied squares.
The aligned row also uses a proved actual U subrectangle.

Every operation is outward integer interval arithmetic on 2**40. All
signed own-center/orientation endpoints and the original root/B guards
are retained. An unresolved box, depth guard or precision guard is an
error, never acceptance. No floating point, sample or solver is used.
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
 assert b[0]>0,b
 return mul(a,(dn(N*N,b[1]),up(N*N,b[0])))
def half(a):return dn(a[0],2),up(a[1],2)
def square(a):
 z=[a[0]*a[0],a[1]*a[1]]
 return dn(0 if a[0]<=0<=a[1] else min(z)),up(max(z))
def absolute(a):
 return (0,max(-a[0],a[1])) if a[0]<=0<=a[1] else ((-a[1],-a[0]) if a[1]<0 else a)
def root(a):
 assert a[1]>=0,a
 l=isqrt(max(0,a[0])*N);h=isqrt(a[1]*N)
 return l,h+(h*h<a[1]*N)
def cs(z):
 l,h=z
 return ((dn((N*N-h*h)*N,N*N+h*h),up((N*N-l*l)*N,N*N+l*l)),(dn(2*l*N*N,N*N+l*l),up(2*h*N*N,N*N+h*h)))
O=I(0);one=I(1);hh=I(1,2)
def check(box,typ):
 ae,be,ze,V,eps=box
 da=max(0,absolute(ae)[0]-N//2);db=max(0,absolute(be)[0]-N//2)
 if 64*(da*da+db*db)>N*N:return 'empty',1
 d=add(one,eps);F=sub(one,V)
 if typ=='aligned':
  r=neg(eps);XA=d
  z=div(eps,V)
  J=div(add(square(V),square(eps)),mul(I(2),eps))
  if J[0]>=N//2:return 'J',1
 else:
  XA=root(sub(square(d),square(V)));r=sub(one,XA)
  if r[0]>eps[1] or r[1]<-eps[1]:return 'r',1
  rad=mul(I(2),add(eps,r))
  if rad[1]<=0:return 'r',1
  z=div(sub(eps,r),add(V,root(rad)))
 if z[0]>I(1,3)[1] or z[1]<0:return 'angle',1
 z=(max(0,z[0]),min(I(1,3)[1],z[1]));x,t=cs(z)
 T=sub(mul(V,x),mul(r,t))
 if typ=='tilted':
  den=add(t,T)
  if den[0]<=0:return None
  J=div(mul(XA,T),den)
 R2=add(square(add(d,one)),I(1,4))
 W=root(sub(R2,square(add(F,one))));u=sub(one,W)
 if W[0]>=N or W[1]<=N//2:return 'W',1
 Y=div(mul(J,add(F,one)),W)
 if Y[1]<F[0] or Y[0]>=I(97,100)[1]:return 'Y',1
 Qn=sub(mul(u,x),mul(Y,t));Qf=add(mul(u,t),mul(Y,x))
 if Qn[1]<=eps[0] or Qf[0]>=I(97,100)[1]:return 'Q',1
 c,s=cs(ze)
 Ex=sub(mul(ae,c),mul(be,s));Ey=add(mul(ae,s),mul(be,c));erad=half(add(c,s))
 def axisrect(xl,xh,yl,yh):
  ru0=add(mul(xl,c),mul(yl,s));ru1=add(mul(xh,c),mul(yh,s))
  rv0=sub(mul(yl,c),mul(xh,s));rv1=sub(mul(yh,c),mul(xl,s))
  gaps=[sub(add(Ex,erad),xl),sub(add(xh,erad),Ex),sub(add(Ey,erad),yl),sub(add(yh,erad),Ey),sub(add(ae,hh),ru0),sub(add(ru1,hh),ae),sub(add(be,hh),rv0),sub(add(rv1,hh),be)]
  return min(g[0] for g in gaps)
 rects=[(sub(r,one),r,neg(V),F),(r,I(1,2),I(-3,8),I(1,4)),(r,I(3,4),I(-3,8),I(1,16))]
 if typ=='aligned':rects.append((sub(r,div(V,I(4))),r,I(-3,8),sub(neg(V),I(1,8))))
 for k,rec in enumerate(rects):
  m=axisrect(*rec)
  if m>0:return 'rect'+str(k),m
 def rotated(nx,ny,fx,fy,S,T,hx,hy):
  H=add(mul(c,nx),mul(s,ny));K=add(mul(c,fx),mul(s,fy))
  L=add(mul(neg(s),nx),mul(c,ny));M=add(mul(neg(s),fx),mul(c,fy))
  eu=add(mul(ae,H),mul(be,L));ev=add(mul(ae,K),mul(be,M))
  re=add(mul(S,H),mul(T,K));rj=add(mul(S,L),mul(T,M))
  gaps=[sub(add(hx,half(add(absolute(H),absolute(L)))),absolute(sub(eu,S))),sub(add(hy,half(add(absolute(K),absolute(M)))),absolute(sub(ev,T))),sub(add(hh,add(mul(hx,absolute(H)),mul(hy,absolute(K)))),absolute(sub(ae,re))),sub(add(hh,add(mul(hx,absolute(L)),mul(hy,absolute(M)))),absolute(sub(be,rj)))]
  return min(g[0] for g in gaps)
 m=rotated(x,neg(t),t,x,add(eps,hh),I(21,400),hh,I(179,400))
 if m>0:return 'U',m
 if typ=='aligned':
  m=axisrect(neg(add(d,one)),neg(d),I(-1,2),hh)
 else:
  al=div(XA,d);bl=div(V,d)
  m=rotated(neg(al),neg(bl),bl,neg(al),add(d,hh),O,hh,hh)
 if m>0:return 'L',m
 return None

def run(typ):
 stack=[(((-5*N//8,5*N//8),(-5*N//8,5*N//8),(0,N),(I(3,100)[0],I(13,100)[1]),(I(9,40000)[0],I(1,60)[1])),0)]
 cnt=Counter();mins={};vis=0;depth=0
 while stack:
  box,dep=stack.pop();vis+=1;r=check(box,typ)
  if r is not None:
   key,m=r;cnt[key]+=1;depth=max(depth,dep)
   if key not in ('empty','J','r','W','Y','Q','angle'):mins[key]=min(mins.get(key,N),m)
   continue
  if dep>=85:
   print('UNRESOLVED',typ,[[q/N for q in z] for z in box],'depth',dep,'counts',dict(cnt),'visited',vis,flush=True);raise SystemExit(2)
  widths=[box[0][1]-box[0][0],box[1][1]-box[1][0],(box[2][1]-box[2][0])*5//4,(box[3][1]-box[3][0])*25//2,(box[4][1]-box[4][0])*75]
  j=max(range(5),key=lambda k:widths[k]);lo,hi=box[j];mid=(lo+hi)//2
  if mid==lo:raise RuntimeError('precision')
  l=list(box);r=list(box);l[j]=(lo,mid);r[j]=(mid,hi)
  stack.append((tuple(r),dep+1));stack.append((tuple(l),dep+1));cnt['split']+=1
  if vis%100000==0:print('PROGRESS',typ,vis,dict(cnt),dep,len(stack),flush=True)
 expected = {'aligned': (Counter({'split':6388,'Y':945,'L':1425,'Q':295,'J':66,'empty':97,'U':1616,'rect3':421,'rect1':515,'rect0':997,'rect2':12}),12777,32,{'L':70557689,'U':20330533,'rect3':247390114,'rect1':39234891,'rect0':40714994,'rect2':54975581388}), 'tilted': (Counter({'split':18211,'L':5176,'Y':3072,'empty':324,'rect1':2308,'U':4336,'Q':391,'rect0':2589,'rect2':16}),36423,34,{'L':2455650,'rect1':5181912,'U':19703318,'rect0':4190209,'rect2':54975581388})}[typ]
 assert (cnt,vis,depth,mins)==expected,(typ,cnt,vis,depth,mins)
 assert min(mins.values())>0
 print('PASS',typ,dict(cnt),'vis',vis,'depth',depth,'mins',mins,'denominator',N,flush=True)

if __name__=='__main__':
 run('aligned')
 run('tilted')
