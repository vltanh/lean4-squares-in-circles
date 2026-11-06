"""Exact rational outer model for four original squares E,F,H,I.

No optimizer is imported here. Every affine row is rounded outward to the
2^-44 grid, paying coefficient changes with |z_k| <= 4. Radicals are
bounded by integer-square-root comparisons at precision 2^-54.
This is a proof-rule prototype; complete-cover/certificate verification is separate.
"""
from fractions import Fraction as F
from math import isqrt
from itertools import product, combinations, permutations

Q=F(1105,256);rho=F(91,60);D=1<<44;SD=1<<54
ROOT_P=[(-F(161,125),-F(47,64)),(F(641,1000),F(567,500)),(-F(103,500),F(17,64)),(-F(71,200),F(11,1000)),(-F(41,100),F(507,1000)),(F(203,500),F(359,500)),(-F(201,500),F(103,100)),(F(1113,1000),rho)]
# Arbitrary rational directions, frozen independently of their trigonometric
# discovery. Their exact norm, not a presumed unit norm, enters each cap.
DIRECTIONS=[tuple(map(F,p)) for p in [['1', '0'], ['8700286382685973/9007199254740992', '291404338770025/1125899906842624'], ['7800463371553963/9007199254740992', '9007199254740991/18014398509481984'], ['6369051672525773/9007199254740992', '1592262918131443/2251799813685248'], ['4503599627370497/9007199254740992', '3900231685776981/4503599627370496'], ['1165617355080101/4503599627370496', '2175071595671493/2251799813685248'], ['4967757600021511/81129638414606681695789005144064', '1'], ['-2331234710160199/9007199254740992', '8700286382685973/9007199254740992'], ['-2251799813685247/4503599627370496', '7800463371553963/9007199254740992'], ['-1592262918131443/2251799813685248', '6369051672525773/9007199254740992'], ['-7800463371553961/9007199254740992', '4503599627370499/9007199254740992'], ['-2175071595671493/2251799813685248', '4662469420320405/18014398509481984'], ['-1', '4967757600021511/40564819207303340847894502572032'], ['-4350143191342987/4503599627370496', '-4662469420320393/18014398509481984'], ['-1950115842888491/2251799813685248', '-9007199254740987/18014398509481984'], ['-398065729532861/562949953421312', '-6369051672525769/9007199254740992'], ['-1125899906842625/2251799813685248', '-975057921444245/1125899906842624'], ['-2331234710160207/9007199254740992', '-8700286382685971/9007199254740992'], ['-3725818200016133/20282409603651670423947251286016', '-1'], ['582808677540049/2251799813685248', '-4350143191342987/4503599627370496'], ['2251799813685245/4503599627370496', '-3900231685776983/4503599627370496'], ['6369051672525771/9007199254740992', '-3184525836262887/4503599627370496'], ['975057921444245/1125899906842624', '-1125899906842625/2251799813685248'], ['8700286382685971/9007199254740992', '-4662469420320415/18014398509481984']]]

def low(x):x=F(x);return F((x.numerator*D)//x.denominator,D)
def high(x):x=F(x);return F(-((-x.numerator*D)//x.denominator),D)
def sqrt_bounds(x):
 x=F(x)
 if x<0:raise ValueError('negative radicand')
 k=isqrt((x.numerator*SD*SD)//x.denominator)
 l=F(k,SD)
 return (l,l) if l*l==x else (l,F(k+1,SD))
def sqrtlo(x):return sqrt_bounds(x)[0]
def sqrthi(x):return sqrt_bounds(x)[1]
def linspace(a,b,n):return [a+(b-a)*F(k,n-1) for k in range(n)]
def x(i):return 2*i
def y(i):return 2*i+1
def a(i):return 8+i
def b(i):return 12+i
def ab(i):return 16+i
def g(i):return 20+i

def frame_bounds(T,P):
 aa=[];bb=[];vv=[];gg=[]
 for lo,hi in T:
  L=F(0) if lo<=0<=hi else min(abs(lo),abs(hi));U=max(abs(lo),abs(hi))
  aa.append((low(1/sqrthi(1+U*U)),high(1/sqrtlo(1+L*L))))
  bl=lo/(sqrtlo(1+lo*lo) if lo<0 else sqrthi(1+lo*lo))
  bh=hi/(sqrthi(1+hi*hi) if hi<0 else sqrtlo(1+hi*hi))
  bb.append((low(bl),high(bh)))
  vv.append((low(L/sqrthi(1+L*L)),high(U/sqrtlo(1+U*U))))
  gg.append((low(sqrtlo(1+U*U)/(2*(1+U))),high(sqrthi(1+L*L)/(2*(1+L)))))
 return list(P)+aa+bb+vv+gg

class Model:
 def __init__(self,T,sats,with_extra=True):
  self.T=[tuple(map(F,t)) for t in T];self.bounds=frame_bounds(self.T,ROOT_P)
  self.rows=[];self.names=[];self.prods={};self.build(sats)
  if with_extra:self.extra_rows(sats)
  # The delivered four-square proof uses no imported pair-cap, tilt-toll,
  # or three-square-energy theorem. Keep indices stable with valid 0<=0 rows.
  banned={'weighted original pair cap','pair cap beta toll','pair cap sharp toll','three-square center energy'}
  for k,name in enumerate(self.names):
   if name in banned:self.rows[k]=({},0);self.names[k]='unused imported row (zero)'

 def row(self,c,r,name):
  c={k:F(v) for k,v in c.items() if v};r=F(r)
  quant={k:low(v) for k,v in c.items()};error=4*sum(abs(c[k]-quant[k]) for k in c)
  rr=high(r+error)
  self.rows.append(({k:int(v*D) for k,v in quant.items() if v},int(rr*D)));self.names.append(name)
 def terms(self,*items):
  c={}
  for k,v in items:c[k]=c.get(k,F(0))+v
  return c
 def mc(self,i,j):
  if i>j:i,j=j,i
  if (i,j) in self.prods:return self.prods[i,j]
  z=len(self.bounds);self.prods[i,j]=z
  lo,hi=self.bounds[i];l,h=self.bounds[j]
  self.bounds.append((min(lo*l,lo*h,hi*l,hi*h),max(lo*l,lo*h,hi*l,hi*h)))
  self.row(self.terms((i,l),(j,lo),(z,-1)),lo*l,'mcc lower')
  self.row(self.terms((i,h),(j,hi),(z,-1)),hi*h,'mcc lower')
  self.row(self.terms((i,-l),(j,-hi),(z,1)),-hi*l,'mcc upper')
  self.row(self.terms((i,-h),(j,-lo),(z,1)),-lo*h,'mcc upper')
  return z
 def build(self,sats):
  for i in range(4):
   tl,tu=self.T[i]
   self.row({b(i):1,a(i):-tu},0,'slope upper');self.row({b(i):-1,a(i):tl},0,'slope lower')
   self.row({b(i):1,ab(i):-1},0,'abs');self.row({b(i):-1,ab(i):-1},0,'abs')
   bl,bh=self.bounds[b(i)]
   if bl>=0:self.row({ab(i):1,b(i):-1},0,'abs positive')
   elif bh<=0:self.row({ab(i):1,b(i):1},0,'abs negative')
   else:self.row({ab(i):1,b(i):-(bh+bl)/(bh-bl)},-2*bh*bl/(bh-bl),'abs secant')
   l,h=self.bounds[ab(i)];cl=sqrtlo(1-l*l);ch=sqrtlo(1-h*h)
   if h>l:
    slope=(ch-cl)/(h-l);self.row({a(i):-1,ab(i):slope},-cl+slope*l,'cos chord')
   for w in linspace(l,h,5):
    c=sqrtlo(1-w*w);self.row({a(i):c,ab(i):w},1,'circle tangent frame')
   self.row({a(i):-1,ab(i):-1},-1,'width >= 1/2');self.row({ab(i):1,a(i):-1},0,'folded')
   self.row({a(i):-F(1,2),ab(i):-F(1,2),g(i):-1},-1,'h+g>=1')
   hL=max(F(1,2),(self.bounds[a(i)][0]+self.bounds[ab(i)][0])/2)
   hU=min(sqrthi(F(1,2)),(self.bounds[a(i)][1]+self.bounds[ab(i)][1])/2)
   if hU>hL:
    sl=(1/(4*hU)-1/(4*hL))/(hU-hL)
    self.row({g(i):1,a(i):-sl/2,ab(i):-sl/2},1/(4*hL)-sl*hL,'inset secant')
   for h0 in linspace(hL,hU,4):
    sl=-1/(4*h0*h0);self.row({g(i):-1,a(i):sl/2,ab(i):sl/2},-1/(4*h0)+sl*h0,'inset tangent')
   for ux,uy in DIRECTIONS:
    norm2=ux*ux+uy*uy
    for su,sv in product([-1,1],repeat=2):
     self.row({x(i):ux,y(i):uy,a(i):(su*ux+sv*uy)/2,b(i):(su*uy-sv*ux)/2},sqrthi(Q*norm2),'corner support')
    self.row({x(i):ux,y(i):uy},rho*sqrthi(norm2),'center disk support')
  for i in range(4):
   X,Y=x(i),y(i);sq=[]
   for z in [X,Y]:
    l,h=self.bounds[z];qv=len(self.bounds);sq.append(qv)
    self.bounds.append((F(0) if l<=0<=h else min(l*l,h*h),max(l*l,h*h)))
    self.row({qv:1,z:-(l+h)},-l*h,'square secant')
    for c0 in linspace(l,h,5):self.row({z:2*c0,qv:-1},c0*c0,'square tangent')
   ax=self.mc(a(i),X);by=self.mc(b(i),Y);bx=self.mc(b(i),X);ay=self.mc(a(i),Y)
   for ss,tt in product([-1,1],repeat=2):self.row(self.terms((sq[0],1),(sq[1],1),(ax,ss),(by,ss),(bx,-tt),(ay,tt)),Q-F(1,2),'same-frame squared corner')
   self.row({sq[0]:1,sq[1]:1},rho*rho,'center quadratic upper')
  self.row({x(0):1,x(1):-1,a(0):F(1,2),ab(0):F(1,2),a(1):F(1,2),ab(1):F(1,2)},0,'EF actual')
  for sg in [-1,1]:self.row({x(0):1,x(1):-1,y(1):sg,y(0):-sg},0,'EF cone')
  for i,j,k in [(1,2,1),(2,3,1),(0,2,0)]:self.row({2*i+k:1,2*j+k:-1,g(i):1,g(j):1},0,'original inset relation')
  self.row({x(2):1,x(3):-1},0,'HI x sorted')
  for i,j in permutations(range(4),2):
   for axis in [0,1]:
    for sg in [-1,1]:
     self.row({2*i+axis:46*sg,2*j+axis:F(27,2)*sg,a(i):-23,ab(i):-23,a(j):-F(27,4),ab(j):-F(27,4)},F(211,4),'weighted original pair cap')
     self.row({2*i+axis:46*sg,2*j+axis:F(27,2)*sg,a(i):-23,ab(i):-19,a(j):-F(27,4),ab(j):-F(27,4)},F(211,4),'pair cap beta toll')
     self.row({2*i+axis:46*sg,2*j+axis:F(27,2)*sg,a(i):-23+F(46*41,32),ab(i):-23+F(46*9,32),a(j):-F(27,4),ab(j):-F(27,4)},F(211,4)+F(46*41,32),'pair cap sharp toll')
  self.pairranges={}
  for i,j in combinations(range(4),2):
   ints=[(self.bounds[2*j+k][0]-self.bounds[2*i+k][1],self.bounds[2*j+k][1]-self.bounds[2*i+k][0]) for k in [0,1]]
   self.pairranges[i,j]=ints;c={};rhs=F(-1)
   for k,(lo,hi) in enumerate(ints):c[2*j+k]=-(lo+hi);c[2*i+k]=lo+hi;rhs-=lo*hi
   self.row(c,rhs,'center distance square secants')
   aa=min(self.bounds[a(i)][0],self.bounds[a(j)][0])
   for sign in [-1,1]:
    cc=c.copy()
    for k,coef in [(a(i),aa*sign),(ab(i),aa*sign),(a(j),-aa*sign),(ab(j),-aa*sign)]:cc[k]=cc.get(k,F(0))+coef
    self.row(cc,rhs,'owner-free width difference')
  for I in combinations(range(4),3):
   c={};rhs=-F(7,2)
   for i,j in combinations(I,2):
    for k,(lo,hi) in enumerate(self.pairranges[i,j]):c[2*j+k]=c.get(2*j+k,F(0))-(lo+hi);c[2*i+k]=c.get(2*i+k,F(0))+(lo+hi);rhs-=lo*hi
   self.row(c,rhs,'three-square center energy')
  for i,j,owner,axis,sg in sats:
   dv=[]
   for k in [0,1]:
    lo,hi=self.pairranges[i,j][k]
    for p,q,kk,sign in [(1,2,1,1),(2,3,1,1),(0,2,0,1)]:
     if (p,q,kk)==(i,j,k):lo=max(lo,self.bounds[g(i)][0]+self.bounds[g(j)][0])
    z=len(self.bounds);self.bounds.append((lo,hi));dv.append(z)
    self.row({z:1,2*j+k:-1,2*i+k:1},0,'pair difference definition');self.row({z:-1,2*j+k:1,2*i+k:-1},0,'pair difference definition')
   xx,yy=(a(owner),b(owner)) if axis==0 else (b(owner),a(owner));xs,ys=(sg,sg) if axis==0 else (-sg,sg)
   px=self.mc(xx,dv[0]);py=self.mc(yy,dv[1]);dcx=self.bounds[dv[0]];dcy=self.bounds[dv[1]]
   if max(map(abs,dcx))<1:
    if dcy[0]>=0:self.row({yy:-ys},0,'owned vertical sign forced')
    elif dcy[1]<=0:self.row({yy:ys},0,'owned vertical sign forced')
   if max(map(abs,dcy))<1:
    if dcx[0]>=0:self.row({xx:-xs},0,'owned horizontal sign forced')
    elif dcx[1]<=0:self.row({xx:xs},0,'owned horizontal sign forced')
   self.row({px:-xs,py:-ys},-support_min(self.T[i],self.T[j]),'exact relative support lower')
   for ds in [-1,1]:
    terms=[(px,-2*xs),(py,-2*ys),(self.mc(a(i),a(j)),1),(self.mc(b(i),b(j)),1),(self.mc(a(i),b(j)),ds),(self.mc(b(i),a(j)),-ds)]
    self.row(self.terms(*terms),-1,'physical owned axis')
 def extra_rows(self,sats):
  T=self.T;P=ROOT_P
  for i,j in combinations(range(4),2):
   ranges=[[P[2*j+k][0]-P[2*i+k][1],P[2*j+k][1]-P[2*i+k][0]] for k in [0,1]]
   if (i,j)==(0,1):ranges[0][0]=max(ranges[0][0],hmin(T[i],1,0)+hmin(T[j],1,0))
   if (i,j) in [(1,2),(2,3)]:ranges[1][0]=max(ranges[1][0],gmin(T[i])+gmin(T[j]))
   if (i,j)==(0,2):ranges[0][0]=max(ranges[0][0],gmin(T[i])+gmin(T[j]))
   if (i,j)==(2,3):ranges[0][0]=max(ranges[0][0],F(0))
   cc={};offset=F(0)
   for k,(l,h) in enumerate(ranges):
    if l>=0:coef,add=F(1),F(0)
    elif h<=0:coef,add=F(-1),F(0)
    else:coef=(h+l)/(h-l);add=-2*l*h/(h-l)
    cc[2*i+k]=coef;cc[2*j+k]=-coef;offset+=add
   radius=F(0)
   for l,h in [T[i],T[j]]:
    t=F(0) if l<=0<=h else min(abs(l),abs(h));radius+=sqrtlo(1+t*t)/2
   self.row(cc,offset-radius,'all-sign original diamond secant')
  for i,j,o,axis,sg in sats:
   tl,tu=T[o];tm=(tl+tu)/2
   c={2*j:sg,2*i:-sg,2*j+1:sg*tm,2*i+1:-sg*tm} if axis==0 else {2*j:-sg*tm,2*i:sg*tm,2*j+1:sg,2*i+1:-sg}
   k=1 if axis==0 else 0;ss=sg if axis==0 else -sg
   lo=P[2*j+k][0]-P[2*i+k][1];hi=P[2*j+k][1]-P[2*i+k][0]
   if k==1 and (i,j) in [(1,2),(2,3)]:lo=max(lo,gmin(T[i])+gmin(T[j]))
   if k==0 and (i,j)==(0,2):lo=max(lo,gmin(T[i])+gmin(T[j]))
   if k==0 and (i,j)==(2,3):lo=max(lo,F(0))
   if k==0 and (i,j)==(0,1):lo=max(lo,hmin(T[i],1,0)+hmin(T[j],1,0))
   vl,vh=sorted([ss*lo,ss*hi]);other=j if o==i else i
   lower=coupled_lower(T[o],T[other],tm,vl,vh)
   self.row({k:-v for k,v in c.items()},-lower,'coupled owned separator enclosure')
 def with_bounds(self):
  rows=list(self.rows);names=list(self.names)
  for k,(l,h) in enumerate(self.bounds):
   # The bound endpoints themselves are rigorous; rounding RHS upward is safe.
   rows.append(({k:D},int(high(h)*D)));names.append('variable upper')
   rows.append(({k:-D},int(high(-l)*D)));names.append('variable lower')
  return rows,names

def hmin(T,p,q):
 lo,hi=T;v=[lo,hi]
 if q and lo<=-F(p,q)<=hi:v.append(-F(p,q))
 if p and lo<=F(q,p)<=hi:v.append(F(q,p))
 return low(min((abs(p+q*t)+abs(q-p*t))/(2*sqrthi(1+t*t)) for t in v))
def gmin(T):
 t=max(map(abs,T));return low(sqrtlo(1+t*t)/(2*(1+t)))
def support_min(T,U):
 def s(t,u):return F(1,2)+(1+t*u+abs(u-t))/(2*sqrthi((1+t*t)*(1+u*u)))
 vals=[s(T[1],U[0]),s(T[0],U[1])]
 if max(T[0],U[0])<=min(T[1],U[1]):vals.append(F(1))
 return low(min(vals))

def cvx_lower(A,B,C,l,h):
 def endpoint(t):return A*sqrtlo(1+t*t)+B*t+C
 if B>=A:return endpoint(l)
 if B<=-A:return endpoint(h)
 denlo,denhi=sqrt_bounds(A*A-B*B)
 if B<=0:cl,ch=-B/denhi,-B/denlo
 else:cl,ch=-B/denlo,-B/denhi
 if ch<l:return endpoint(l)
 if cl>h:return endpoint(h)
 return A*A/denhi-B*B/denhi+C # = lower sqrt(A*A-B*B)+C

def coupled_lower(T,U,tm,vl,vu):
 ans=[]
 for l,h,v in [(T[0],tm,vl),(tm,T[1],vu)]:
  for other in U:
   rl,rh=sqrt_bounds(1+other*other)
   for aa,bb,sg in [(l,min(h,other),-1),(max(l,other),h,1)]:
    if aa>bb:continue
    num=other+sg;B0=num/(2*(rh if num>=0 else rl))-v;B1=num/(2*(rl if num>=0 else rh))-v
    C=(1-sg*other)/(2*rh)+v*tm
    # Coefficient intervals are enclosed uniformly, with the correct sign of t.
    if aa<0:ans.append(cvx_lower(F(1,2),B1,C,aa,min(bb,F(0))))
    if bb>=0:ans.append(cvx_lower(F(1,2),B0,C,max(aa,F(0)),bb))
  aa,bb=max(l,U[0]),min(h,U[1])
  if aa<=bb:ans.append(cvx_lower(F(1),-v,v*tm,aa,bb))
 return low(min(ans))
