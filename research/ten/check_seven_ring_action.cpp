#include <cmath>
#include <algorithm>
#include <array>
#include <vector>
#include <iostream>
#include <iomanip>
#include <stdexcept>
#include <limits>
using namespace std;
static_assert(numeric_limits<double>::is_iec559 && numeric_limits<double>::digits == 53,
              "Exact dyadic endpoint storage requires IEEE binary64.");

// Exhaustive finite verification for SEVEN_RING_GLOBAL_ACTION.md.
// Build: g++ -O3 -std=c++17 check_seven_ring_action.cpp -o /tmp/check_seven_ring_action
// Run:   /tmp/check_seven_ring_action
// Exit 0 requires complete coverage, with no unresolved cell.
// No floating-point approximation is used to decide interval inequalities:
// all endpoints lie on Q36; arithmetic bounds use exact integer floor/ceil.
// sqrtl supplies only an initial integer-square-root guess, repaired exactly.
// Exception 1 means "subdivide"; exception 2 means a necessary condition fails.

// Exact dyadic interval arithmetic. Double storage is exact for our bounded Q36 grid.
using Int=__int128_t; using UInt=__uint128_t;
constexpr long long SCALE=1LL<<36; constexpr long long LIM=1LL<<52;
long long floordiv(Int n,Int d){if(d<0){d=-d;n=-n;}Int q=n/d,r=n%d;if(r<0)--q;if(q<=-LIM||q>=LIM)throw 1;return (long long)q;}
long long ceildiv(Int n,Int d){return -floordiv(-n,d);}
long long grid(double x){return (long long)ldexp(x,36);}
struct I {double l,h; I(double x=0){if(!isfinite(x)||abs(x)>=65536)throw 1;l=ldexp(floor(ldexp(x,36)),-36);h=ldexp(ceil(ldexp(x,36)),-36);} I(double x,double y){if(x>y)throw 1;if(!isfinite(x)||!isfinite(y)||abs(x)>=65536||abs(y)>=65536)throw 1;l=ldexp(floor(ldexp(x,36)),-36);h=ldexp(ceil(ldexp(y,36)),-36);} };
I out(long long l,long long h){if(l<=-LIM||h>=LIM)throw 1;return I(ldexp((double)l,-36),ldexp((double)h,-36));}
I operator+(I a,I b){return out(grid(a.l)+grid(b.l),grid(a.h)+grid(b.h));} I operator-(I a){return I(-a.h,-a.l);} I operator-(I a,I b){return a+-b;}
I operator*(I a,I b){Int v[]={(Int)grid(a.l)*grid(b.l),(Int)grid(a.l)*grid(b.h),(Int)grid(a.h)*grid(b.l),(Int)grid(a.h)*grid(b.h)};return out(floordiv(*min_element(v,v+4),SCALE),ceildiv(*max_element(v,v+4),SCALE));}
I operator/(I a,I b){if(b.l<=0&&b.h>=0)throw 1;long long low=LIM,high=-LIM;for(long long x:{grid(a.l),grid(a.h)})for(long long y:{grid(b.l),grid(b.h)}){low=min(low,floordiv((Int)x*SCALE,y));high=max(high,ceildiv((Int)x*SCALE,y));}return out(low,high);}
I sq(I a){if(a.l>=0)return out(floordiv((Int)grid(a.l)*grid(a.l),SCALE),ceildiv((Int)grid(a.h)*grid(a.h),SCALE));if(a.h<=0)return sq(-a);return I(0,(a*a).h);}
long long isqrt(UInt n){unsigned long long r=(unsigned long long)sqrtl((long double)n);while((UInt)r*r>n)--r;while((UInt)(r+1)*(r+1)<=n)++r;return (long long)r;}
I root(I a){if(a.h<0)throw 2;long long l=a.l<=0?0:isqrt((UInt)grid(a.l)*SCALE),h=isqrt((UInt)grid(a.h)*SCALE);if((UInt)h*h<(UInt)grid(a.h)*SCALE)++h;return out(l,h);}
struct V {I a,b,d,e;V(I x=I(0)):a(x),b(x),d(0),e(0){} V(I x,I y,I z,I w):a(x),b(y),d(z),e(w){} };
V operator+(V a,V b){return {a.a+b.a,a.b+b.b,a.d+b.d,a.e+b.e};} V operator-(V a){return {-a.a,-a.b,-a.d,-a.e};} V operator-(V a,V b){return a+-b;}
V operator*(V a,V b){I aa=(a.a+a.b)/I(2),bb=(b.a+b.b)/I(2);return {a.a*b.a,a.b*b.b,aa*b.d+bb*a.d,aa*b.e+bb*a.e};}
V operator/(V a,V b){I q=a.a/b.a,q0=a.b/b.b;return {q,q0,(I(2)*a.d-(q+q0)*b.d)/(b.a+b.b),(I(2)*a.e-(q+q0)*b.e)/(b.a+b.b)};}
V square(V a){return {sq(a.a),sq(a.b),(a.a+a.b)*a.d,(a.a+a.b)*a.e};}
V root(V a){I q=root(a.a),q0=root(a.b);return {q,q0,a.d/(q+q0),a.e/(q+q0)};}
I Rof(I s){return root(I(1)-sq(s))+I(1)/(I(2)*s);}
bool impossible(I x,I R){if(x.h<=0||x.l>=1)return true; if((R*x).h<=.5)return true;if((R*root(I(1)-sq(x))).h<=.5)return true;return false;}
I tight(I x,I y,I R);
I step(I x,I y,I R){
 if(impossible(x,R)||impossible(y,R))throw 2;
 I c=root(I(1)-sq(y)),A=R*c-I(1),B=R*y,D2=sq(R)+I(1)-I(2)*R*c,H=R*x-I(1),k=root(D2-sq(H));
 I cd=(A*k+B*H)/D2,sd=(B*k-A*H)/D2,cb=(k*(R-c)+H*y)/D2;
 if(cd.h<=0||sd.h<=0||cb.h<=0||(cd*y-cb).l>0)throw 2;
 I kn=k*c/cb,cn=(sq(R)+I(1)-sq(R*y-I(1))-sq(kn))/(I(2)*R);
 if(cn.h<=0||cn.l>=1||(R*cn).h<=.5)throw 2;
 I z=root(I(1)-sq(cn)); try{I tz=tight(x,y,R);z=I(max(z.l,tz.l),min(z.h,tz.h));}catch(int){} if(impossible(z,R))throw 2;return z;
}

I basic(I x,I y,I R, I *jx=nullptr,I *jy=nullptr,I *jr=nullptr){
 I c=root(I(1)-sq(y)),A=R*c-I(1),B=R*y,D2=sq(R)+I(1)-I(2)*R*c,H=R*x-I(1),k=root(D2-sq(H));
 I cd=(A*k+B*H)/D2,sd=(B*k-A*H)/D2,cb=(k*(R-c)+H*y)/D2,sb=sd*c-cd*y,kn=k*c/cb;
 I cn=(sq(R)+I(1)-sq(R*y-I(1))-sq(kn))/(I(2)*R),z=root(I(1)-sq(cn));
 if(jx){
  if(k.l<=0||cb.l<=0||cn.l<=0||cn.h>=1||z.l<=0||c.l<=0)throw 1;
  *jx=-(y*cn*sq(c)/(z*cb*cb*cb));
  *jy=cn/z*((R*y-I(1))+k*c*sb*cd/(R*cb*cb*cb)+c*y/sq(cb)-sq(k)*y/(R*sq(cb)));
  I kr=(R-c-x*H)/k,cbr=(kr*(R-c)+k+x*y-I(2)*(R-c)*cb)/D2,knr=kn*(kr/k-cbr/cb),cnr=(R-y*(R*y-I(1))-kn*knr-cn)/R;
  *jr=-cn*cnr/z;
 }
 return z;
}
I tight(I x,I y,I R){
 I fx,fy,fr;I z=basic(x,y,R,&fx,&fy,&fr);I xm((x.l+x.h)/2),ym((y.l+y.h)/2),rm((R.l+R.h)/2);
 I zmid=basic(xm,ym,rm),zm=zmid+fx*(x-xm)+fy*(y-ym)+fr*(R-rm);return I(max(z.l,zm.l),min(z.h,zm.h));
}
V slope(V x,V y,I rv,I s){
 V R(rv),c=root(V(1)-square(y)),D2=square(R)+V(1)-V(2)*R*c,H=R*x-V(1),k=root(D2-square(H));
 V cb=(k*(R-c)+H*y)/D2,kn=k*c/cb,cn=(square(R)+V(1)-square(R*y-V(1))-square(kn))/(V(2)*R);
 V z=root(V(1)-square(cn));z.b=s;try{I tz=tight(x.a,y.a,rv);z.a=I(max(z.a.l,tz.l),min(z.a.h,tz.h));}catch(int){}return z;
}
bool pd(I a,I b,I d){return a.l>0 && d.l>0 && (a*d-sq(b)).l>0;}
bool direct(I s,I x,I y){
 I R=Rof(s),z=tight(x,y,R),w=tight(y,z,R),X=x-s,Y=y-s,Z=z-s,W=w-s;
 I g11=I(1),g12=I(0),g22=I(1),c=I(9)/I(20);
 I D=X*(g11*Z+g12*W)+Y*(g12*Z+g22*W),K=Y*Z-X*W;
 return (sq(Y)-X*Z).l>0 && D.h<0 && (K-c*D).l>0 && (-K-D).l>0;
}
bool check(I s,I x,I y){
 I R=Rof(s); V X(x,s,1,0),Y(y,s,0,1),Z=slope(X,Y,R,s),W=slope(Y,Z,R,s);
 // One-step clockwise lift in ordinary coordinates.
 I A=-Z.d,B=Z.e;if(A.l<=0||(I(4)*A-sq(B)).l<=0)return false;
 I j11=Z.d,j12=Z.e,j21=W.d,j22=W.e;
 // Metric G has determinant 1. Q=-sym(GJ); K=sym(rot J).
 I g11=I(1),g12=I(0),g22=I(1),c=I(9)/I(20);
 I q11=-(g11*j11+g12*j21),q22=-(g12*j12+g22*j22),q12=-(g11*j12+g12*j22+g12*j11+g22*j21)/I(2);
 I k11=-j21,k22=j12,k12=(j11-j22)/I(2);
 return pd(q11,q12,q22)&&pd(k11+c*q11,k12+c*q12,k22+c*q22)&&pd(q11-k11,q12-k12,q22-k22);
}
struct Box{I s,x,y;int depth;};
int main(){
 const int steps=2; const long limit=10000000;
 I sl=I(413)/I(1000), sh=I(23)/I(50), lo=I(23)/I(100), hi=I(49)/I(50);
 vector<Box> todo={{I(sl.l,sh.h),I(lo.l,hi.h),I(lo.l,hi.h),0}};
 long n=0,elim=0,pass=0,deep=0; int maxdepth=0;

 while(!todo.empty()&&n<limit){auto b=todo.back();todo.pop_back();++n;maxdepth=max(maxdepth,b.depth);int status=0;
 try {I R=Rof(b.s);if(R.h<(I(79)/I(40)).l||sq(R).l>4.5){status=2;}else{
  try{if(direct(b.s,b.x,b.y))status=1;}catch(int){}
  if(!status){try{if(check(b.s,b.x,b.y))status=1;}catch(int){}}
  if(!status){I x=b.x,y=b.y;for(int i=0;i<steps;i++){I z=step(x,y,R);x=y;y=z;}}
 }}catch(int code){if(code==2)status=2;}
 if(status==1){pass++;continue;}if(status==2){elim++;continue;}
 if(b.depth>=54){++deep;break;}
 double ws=(b.s.h-b.s.l)*5,wx=b.x.h-b.x.l,wy=b.y.h-b.y.l;Box a=b,c=b;a.depth=c.depth=b.depth+1;
 I *p,*q;if(ws>=wx&&ws>=wy){p=&a.s;q=&c.s;}else if(wx>=wy){p=&a.x;q=&c.x;}else{p=&a.y;q=&c.y;}double mid=ldexp((double)((grid(p->l)+grid(p->h))/2),-36);p->h=mid;q->l=mid;todo.push_back(c);todo.push_back(a);

 }
 cout<<"RESULT nodes "<<n<<" pass "<<pass<<" elim "<<elim<<" todo "<<todo.size()<<" deep "<<deep<<" maxdepth "<<maxdepth<<endl;
 return (todo.empty() && deep==0) ? 0 : 1;
}
