// UNTRUSTED FLOATING DISCOVERY ONLY. Every leaf requires independent exact replay.
#include <algorithm>
#include <array>
#include <cmath>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
using ld=long double;
struct I {ld lo,hi;I(ld x=0):lo(x),hi(x){}I(ld x,ld y):lo(x),hi(y){}};
I operator+(I a,I b){return {a.lo+b.lo,a.hi+b.hi};}
I operator-(I a){return {-a.hi,-a.lo};}
I operator-(I a,I b){return a+-b;}
I operator*(I a,I b){ld q[]={a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi};return {*min_element(q,q+4),*max_element(q,q+4)};}
I rec(I a){return {1/a.hi,1/a.lo};}
I operator/(I a,I b){return a*rec(b);}
I sq(I a){return {(a.lo<=0&&a.hi>=0)?0:min(a.lo*a.lo,a.hi*a.hi),max(a.lo*a.lo,a.hi*a.hi)};}
I ab(I a){return {max({0.L,a.lo,-a.hi}),max(abs(a.lo),abs(a.hi))};}
I root(I a){return {sqrtl(max(0.L,a.lo)),sqrtl(max(0.L,a.hi))};}
I mn(initializer_list<I> aa){ld lo=1e100L,hi=lo;for(auto a:aa){lo=min(lo,a.lo);hi=min(hi,a.hi);}return {lo,hi};}
I mx(initializer_list<I> aa){ld lo=-1e100L,hi=lo;for(auto a:aa){lo=max(lo,a.lo);hi=max(hi,a.hi);}return {lo,hi};}
struct Frame {I a,b,h,k,g,d;};
Frame shape(I t){
 auto at=[](ld z){ld d=sqrtl(1+z*z),a=1/d,b=z/d;return array<ld,5>{a,b,(a+b)/2,(a-b)/2,d};};
 auto p=at(t.lo),q=at(t.hi);Frame f{{q[0],p[0]},{p[1],q[1]},{p[2],q[2]},{q[3],p[3]},I(),{p[4],q[4]}};
 f.g=rec(I(4)*f.h);return f;
}
const ld Q=1105.L/256,l=29.L/60,g=15.L/31,delta=331.L/20000,rho=sqrtl(Q-.25L)-.5L;
I loss(I s,I t,Frame f){return mx({I(0),t*(f.k+s),(s-f.k)/mx({t,I(.0001L)})});}
I ceiling(I x,Frame f){
 x=ab(x);I side=root(I(Q)-sq(x+f.h));
 I p=mn({root(I(Q)-sq(x+f.k))-f.h,side+f.k});
 I m=mn({root(I(Q)-sq(x-f.k))-f.h,side-f.k});
 return mn({I(rho),mx({p,m})});
}
using Box=array<I,5>;
array<ld,6> margins(Box b){
 I x=b[0],z=b[1],s=b[2],t=b[3],u=b[4];Frame P=shape(s),H=shape(t),B=shape(u);
 I r=mx({I(0),s*(P.k+I(delta+2.L/15)-P.g)});
 I p=loss(I(delta+11.L/15)-P.g,s,P);
 I hl=loss(x+I(delta),t,H),hr=loss(I(delta)-x,t,H);
 I sb=mx({z-I(59.L/60),I(delta)-z}),bl=mx({I(0),u*(B.k+sb)});
 I yh=mx({I(2*g-.6L)+P.h+H.h-mn({r+hl,p+hr}),I(g+23.L/60)});
 I yb=mx({I(2*g-.6L)+P.h+B.h-p-bl,I(g+11.L/30)});
 I mh=ceiling(x,H),mb=ceiling(z,B);
 I dx=z-x,dy=mx({I(0),mb-yh,mh-yb});
 I sigma=(I(1)+(I(1)+t*u+ab(t-u))/(H.d*B.d))/I(2);
 sigma.lo=max(1.L,sigma.lo);
 I pair=mx({H.a*dx+H.b*dy,H.b*dx+H.a*dy,B.a*dx+B.b*dy,B.b*dx+B.a*dy})-sigma;
 I de=I(3.L/2-217.L/480)-z,ve=mb-I(221.L/600);
 I end=mx({de-B.h,ve-B.h,B.a*de+B.b*ve-I(.5L),B.b*de+B.a*ve-I(.5L)});
 return {(I(13.L/30)-P.g).hi,(mh-yh).hi,(mb-yb).hi,pair.hi,end.hi,(I(19.L/20-g)-P.h+p).hi};
}
struct Job {Box box;int depth;};
int main(int argc,char**argv){
 string path=argc>1?argv[1]:"131_opposite_low_middle_float_tree.json";
 long long limit=argc>2?stoll(argv[2]):4000000;
 Box initial{I(-l,l),I(l,13.L/12),I(1.L/6,1),I(0,1),I(0,1)};
 array<ld,5> widths;for(int j=0;j<5;j++)widths[j]=initial[j].hi-initial[j].lo;
 vector<Job> jobs{{initial,0}};vector<int> events;long long leaves=0;int depth=0;ld reserve=1e10L;
 while(!jobs.empty()){
  if((long long)events.size()>=limit){cerr<<"INCOMPLETE node budget\n";return 2;}
  auto job=jobs.back();jobs.pop_back();depth=max(depth,job.depth);auto vals=margins(job.box);
  int rule=min_element(vals.begin(),vals.end())-vals.begin();
  if(vals[rule]<-1e-8L){events.push_back(-rule-1);leaves++;reserve=min(reserve,-vals[rule]);}
  else{
   if(job.depth>=65){cerr<<"UNRESOLVED depth "<<job.depth<<"\n";return 2;}
   int axis=0;ld score=-1;
   for(int j=0;j<5;j++){ld w=(job.box[j].hi-job.box[j].lo)/widths[j];if(w>score){score=w;axis=j;}}
   auto lo=job.box,hi=job.box;ld mid=(lo[axis].lo+lo[axis].hi)/2;lo[axis].hi=mid;hi[axis].lo=mid;
   events.push_back(axis);jobs.push_back({hi,job.depth+1});jobs.push_back({lo,job.depth+1});
  }
  if(events.size()%200000==0)cerr<<"nodes "<<events.size()<<" leaves "<<leaves<<" frontier "<<jobs.size()<<" depth "<<depth<<"\n";
 }
 ofstream out(path);out<<"{\"status\":\"COMPLETE_UNTRUSTED_DISCOVERY\",\"nodes\":"<<events.size()<<",\"leaves\":"<<leaves<<",\"maxdepth\":"<<depth<<",\"events\":[";
 for(size_t i=0;i<events.size();i++){if(i)out<<',';out<<events[i];}out<<"]}\n";
 cerr<<"COMPLETE nodes "<<events.size()<<" leaves "<<leaves<<" depth "<<depth<<" reserve "<<reserve<<"\n";
}
