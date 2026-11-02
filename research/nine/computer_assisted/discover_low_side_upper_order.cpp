#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <cmath>
#include <csignal>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <string>
#include <tuple>
#include <vector>
using namespace std;
// Floating guidance only. No leaf is accepted without independent exact replay.
struct I {
 double l,u; I(double x=0):l(x),u(x){} I(double x,double y):l(x),u(y){}
 I sq()const{return I(l<=0&&u>=0?0:min(l*l,u*u),max(l*l,u*u));}
 I ab()const{return I(max({0.,l,-u}),max(abs(l),abs(u)));}
 I rt()const{return I(sqrt(max(0.,l)),sqrt(max(0.,u)));}
};
I operator+(I a,I b){return I(a.l+b.l,a.u+b.u);} I operator-(I a){return I(-a.u,-a.l);}
I operator-(I a,I b){return a+-b;}
I operator*(I a,I b){return I(min({a.l*b.l,a.l*b.u,a.u*b.l,a.u*b.u}),max({a.l*b.l,a.l*b.u,a.u*b.l,a.u*b.u}));}
I operator/(I a,I b){assert(b.l>0);return a*I(1/b.u,1/b.l);}
I mx(initializer_list<I> xs){double l=-1e100,u=-1e100;for(I x:xs){l=max(l,x.l);u=max(u,x.u);}return I(l,u);}
I mn(initializer_list<I> xs){double l=1e100,u=1e100;for(I x:xs){l=min(l,x.l);u=min(u,x.u);}return I(l,u);}
struct Frame{I a,b,h,k;};
Frame frame(I t){auto f=[](double q){double a=1/sqrt(1+q*q),b=q*a;return array<double,4>{a,b,(a+b)/2,(a-b)/2};};auto lo=f(t.l),hi=f(t.u);return {I(hi[0],lo[0]),I(lo[1],hi[1]),I(lo[2],hi[2]),I(hi[3],lo[3])};}
I top(I x,Frame f,int s){auto rt=[](I z){return (I(1105./256)-z.sq()).rt();};return s>0?mn({rt(x+f.k)-f.h,rt(x+f.h)+f.k}):mn({rt(x+f.h)-f.k,rt(x-f.k)-f.h});}
I toll(I t,Frame f){auto c=[](double q){return (6*q+13.5)/sqrt(1+q*q)-13.5;};I raw=6*f.b-13.5*(1-f.a);return I(max(2*f.b.l,min(c(t.l),c(t.u))),max(2*f.b.u,raw.u));}
using Box=array<I,6>;using Eval=pair<double,int>;
I clearance(Frame f,Frame g,I d){
 I s=mx({1+(f.h-g.h).ab(),.5+mx({f.k*g.a+f.h*g.b,f.h*g.a-f.k*g.b})});
 return mx({(s.sq()-d.sq()).rt(),mn({(s-f.a*d)/mx({f.b,.025}),(s-f.b*d)/f.a,
                      (s-g.a*d)/mx({g.b,.025}),(s-g.b*d)/g.a})});
}
Eval evaluate(const Box& z,int rid){
 int side=rid&4?1:-1,sp=rid&2?1:-1,sr=rid&1?1:-1;
 I tp=z[0],tr=z[1],ts=z[2],x=z[3],X=z[4],h=z[5];
 Frame p=frame(tp),r=frame(tr),s=frame(ts);
 auto mf=[](double h){double k=sqrt(.5-h*h);return array<double,5>{h+k,h-k,k,1/(4*h),h+1/(4*h)-1};};
 auto ma=mf(h.l),mb=mf(h.u);
 Frame m{I(mb[0],ma[0]),I(ma[1],mb[1]),h,I(mb[2],ma[2])};
 I g(mb[3],ma[3]),eta(ma[4],mb[4]);
 I TR=toll(tr,r),AL=mx({59./60,157./184+(27./92)*(X-r.h)+TR/46})+eta,AR=59./60+eta;
 auto ca=[&](I A){return mx({4421./12000+(32./9)*eta,1-(I(1105./256)-(mn({A,61./60})+29927./30000).sq()).rt()});};
 I cL=ca(AL),cR=ca(AR),e=.6-cL;
 I qmin=mn({s.h,(.5-s.b*e)/s.a,(.5-s.a*e)/mx({s.b,.025})});
 I zmax=mn({.605,503./480-qmin}),d=mx({0,x+zmax});
 I KPS=clearance(p,s,d);
 I dmp=side<0?x+1+331./20000-h:mx({(x-(g-331./20000)).ab(),(x-(1+331./20000-h)).ab()});
 I inset=g+mn({p.h,(.5+(g-dmp)*p.b)/p.a,(.5+(g-dmp)*p.a)/mx({p.b,.025})});
 I Plo=-1823./3000+mx({clearance(m,p,dmp),inset});
 I Phi=mn({p.h+.1,top(x,p,sp),.6-KPS});
 I q=503./480-X,loss=sr>0?mx({0,tr*(r.k+q)}):mx({0,(q-r.k)/mx({tr,.25})});
 I Rlo=mx({.6,cR+r.h-loss}),Rhi=top(X,r,sr),D=X-x;
 Plo=mx({Plo,Rlo-D});Phi=mn({Phi,Rhi+D});Rlo=mx({Rlo,Plo-D});Rhi=mn({Rhi,Phi+D});
 I lo=mx({Rlo-Phi,-D}),hi=mn({Rhi-Plo,D});
 I support=(1+(p.a*r.a+(sp*sr)*p.b*r.b).ab()+(sr*p.a*r.b-sp*p.b*r.a).ab())/2;
 I proj(-1e100);for(auto[nx,ny]:array<pair<I,I>,4>{{{p.a,sp*p.b},{-sp*p.b,p.a},{r.a,sr*r.b},{-sr*r.b,r.a}}})for(I E:{lo,hi})proj=mx({proj,(nx*D+ny*E).ab()});
 array<I,13>v={Phi-Plo,Rhi-Rlo,zmax-29./60,61./60-AL,61./60-AR,1./30-eta,
   r.h+451./810-X-(92./27)*eta-(2./27)*TR,hi-lo,D-.707,p.h+r.h-D,D-1/(4*p.h)-1/(4*r.h),proj-support,
   D.sq()+mx({lo.sq(),hi.sq()})-support.sq()};
 Eval out{1e100,-1};for(int j=0;j<13;++j)if(v[j].u<out.first)out={v[j].u,j};return out;
}
Box root(){return {I(0,1),I(0,1),I(0,1),I(0,1129./3000),I(.7,13./12),I(.5,.57)};}
pair<Box,Box>halves(Box b,int j){Box a=b;double m=(b[j].l+b[j].u)/2;a[j].u=m;b[j].l=m;return {a,b};}
struct Pending{int rid,depth;Box box;Eval val;};
int main(int argc,char**argv){
 string out=argc>1?argv[1]:"low_side_upper_order_compact_cover.json";
 double seconds=argc>2?stod(argv[2]):600;long maxnodes=10000000;
 vector<int>events;vector<Pending>stack;array<long,13>counts{};array<long,8>perroot{};
 for(int i=7;i>=0;--i)stack.push_back({i,0,root(),{numeric_limits<double>::infinity(),-1}});
 long leaves=0;int depth=0;auto start=chrono::steady_clock::now(),last=start;
 auto elapsed=[&](){return chrono::duration<double>(chrono::steady_clock::now()-start).count();};
 array<double,6>weights={.5,.5,.5,1,1,2};
 while(!stack.empty()&&elapsed()<seconds&&(long)events.size()<maxnodes){
  Pending p=stack.back();stack.pop_back();depth=max(depth,p.depth);if(p.val.second<0)p.val=evaluate(p.box,p.rid);
  if(p.val.first< -1e-7){events.push_back(-p.val.second-1);++leaves;++counts[p.val.second];++perroot[p.rid];}
  else if(p.depth>=70){stack.push_back(p);break;}
  else{
   double widest=0;for(int j=0;j<6;++j)widest=max(widest,(p.box[j].u-p.box[j].l)*weights[j]);
   tuple<int,double,double,double>best{-1,-1e100,-1e100,-1e100};int dim=-1;Box left,right;Eval vl,vr;
   for(int j=0;j<6;++j){double width=(p.box[j].u-p.box[j].l)*weights[j];if(width<widest/4)continue;
    auto[a,b]=halves(p.box,j);auto va=evaluate(a,p.rid),vb=evaluate(b,p.rid);
    auto score=make_tuple(int(va.first< -1e-7)+int(vb.first< -1e-7),-max(va.first,vb.first),-(va.first+vb.first),width);
    if(score>best){best=score;dim=j;left=a;right=b;vl=va;vr=vb;}}
   assert(dim>=0);events.push_back(dim);stack.push_back({p.rid,p.depth+1,right,vr});stack.push_back({p.rid,p.depth+1,left,vl});
  }
  if(chrono::duration<double>(chrono::steady_clock::now()-last).count()>20){last=chrono::steady_clock::now();cerr<<"nodes "<<events.size()<<" leaves "<<leaves<<" root "<<p.rid<<" pending "<<stack.size()<<" depth "<<depth<<" seconds "<<elapsed()<<'\n';}
 }
 ofstream f(out);f<<setprecision(17)<<"{\"schema\":\"low_side_upper_order_compact_v1\",\"status\":\""<<(stack.empty()?"COMPLETE_PENDING_INDEPENDENT_REPLAY":"INCOMPLETE_DISCOVERY_ONLY")<<"\",\"events\":[";
 for(size_t j=0;j<events.size();++j){if(j)f<<',';f<<events[j];}f<<"],\"remaining\":"<<stack.size()<<",\"nodes\":"<<events.size()<<",\"leaves\":"<<leaves<<",\"maximum_depth\":"<<depth<<",\"counts\":[";
 for(int j=0;j<13;++j){if(j)f<<',';f<<counts[j];}f<<"],\"leaves_per_root\":[";
 for(int j=0;j<8;++j){if(j)f<<',';f<<perroot[j];}f<<"],\"seconds\":"<<elapsed()<<"}\n";
 cout<<"{\"complete\":"<<(stack.empty()?"true":"false")<<",\"nodes\":"<<events.size()<<",\"leaves\":"<<leaves<<",\"remaining\":"<<stack.size()<<",\"maximum_depth\":"<<depth<<",\"seconds\":"<<elapsed()<<"}\n";
}
