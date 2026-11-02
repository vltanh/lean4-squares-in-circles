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
using Box=array<I,7>;using Eval=pair<double,int>;
array<int,3> signs(int rid){int j=rid/2;return {j&4?1:-1,j&2?1:-1,j&1?1:-1};}
Eval evaluate(const Box& box,int rid){
 auto [sp,sl,sr]=signs(rid);bool raised=rid%2;I tp=box[0],tl=box[1],tr=box[2],x=box[3],zl=box[4],zr=box[5],h=box[6];
 Frame p=frame(tp),l=frame(tl),r=frame(tr);
 auto fm=[](double q){double k=sqrt(.5-q*q);return array<double,5>{q+k,q-k,1/(4*q),q+1/(4*q)-1,k};};auto ml=fm(h.l),mu=fm(h.u);
 I am(mu[0],ml[0]),bm(ml[1],mu[1]),gm(mu[2],ml[2]),eta(ml[3],mu[3]),km(mu[4],ml[4]);
 // Two successive original physical clearances M -> U -> P.
 auto mh=[](double H){return 1/(4*H)-199./120+(32./9)*(H+1/(4*H)-1);};
 double critical=sqrt(41./128),minm=min(mh(h.l),mh(h.u));
 if(h.l<=critical&&critical<=h.u)minm=4*sqrt(82.)/9-32./9-199./120;
 I m(minm,max(mh(h.l),mh(h.u))),Delta=(h-p.h).ab(),S=1+Delta;
 I separation(1e100);
 for(double e:{0.,29./60}){
  I d1=mx({e-gm+1./60,61./60-h-e}),d2=x+e;
  I T0=(1-d1.sq()).rt()+(S.sq()-d2.sq()).rt();
  I T1=(S.sq()-d1.sq()).rt()+(1-d2.sq()).rt();
  separation=mn({separation,T0,T1});
 }
 I plo=m+separation;
 I phi=mn({p.h+.1,top(x,p,sp)}),taul=toll(tl,l),taur=toll(tr,r);
 I AL=mx({59./60,157./184+(27./92)*(zr-r.h)+taur/46})+eta;
 I AR=mx({59./60,157./184+(27./92)*(zl-l.h)+taul/46})+eta;
 auto lower=[&](I z,Frame f,I t,int sign,I A,double cut){
  I ca=mx({4421./12000+(32./9)*eta,1-(I(1105./256)-(mn({A,61./60})+29927./30000).sq()).rt()});
  I ss=503./480-z;I loss=sign>0?mx({0,t*(f.k+ss)}):mx({0,(ss-f.k)/mx({t,cut})});return ca+f.h-loss;
 };
 I Llo=raised?lower(zl,l,tl,-sl,AL,1./16):I(-.45),Rlo=lower(zr,r,tr,sr,AR,1./4);
 I Lhi=top(zl,l,-sl),Rhi=top(zr,r,sr);
 // Ordered contractions using only the two retained original cones.
 I DL=zl+x,DR=zr-x;
 plo=mx({plo,Llo-DL,Rlo-DR});phi=mn({phi,Lhi+DL,Rhi+DR});
 Llo=mx({Llo,plo-DL});Lhi=mn({Lhi,phi+DL});
 Rlo=mx({Rlo,plo-DR});Rhi=mn({Rhi,phi+DR});
 vector<I> vals={phi-plo,Lhi-Llo,Rhi-Rlo,1./30-eta,61./60-AL,61./60-AR,1+l.h+r.h-zl-zr-(taul+taur)/13.5-(92./27)*eta,l.h+451./810-zl-(92./27)*eta-taul/13.5,r.h+451./810-zr-(92./27)*eta-taur/13.5};
 auto pair_rows=[&](I D,I elo,I ehi,Frame f,int sf,Frame g,int sg){
  I low=mx({elo,-D}),high=mn({ehi,D});I co=f.a*g.a+(sf*sg)*f.b*g.b,si=sg*f.a*g.b-sf*f.b*g.a;I support=(1+co.ab()+si.ab())/2;
  I proj(-1e100);for(auto [nx,ny]:array<pair<I,I>,4>{pair<I,I>{f.a,sf*f.b},{-sf*f.b,f.a},{g.a,sg*g.b},{-sg*g.b,g.a}})for(I ee:{low,high})proj=mx({proj,(nx*D+ny*ee).ab()});
  for(I z:{high-low,D-.707,f.h+g.h-D,D-1/(4*f.h)-1/(4*g.h),proj-support,D.sq()+mx({low.sq(),high.sq()})-support.sq()})vals.push_back(z);
 };
 pair_rows(zl+x,plo-Lhi,phi-Llo,l,sl,p,sp);pair_rows(zr-x,Rlo-phi,Rhi-plo,p,sp,r,sr);
 Eval ans{1e100,-1};for(int j=0;j<(int)vals.size();++j)if(vals[j].u<ans.first)ans={vals[j].u,j};return ans;
}
Box root(int rid){return {I(0,1),I(0,1),I(0,1),I(0,1129./3000),rid%2?I(3./5,13./12):I(19./60,3./5),I(7./10,13./12),I(.5,.65)};}
pair<Box,Box> halves(Box b,int j){Box a=b;double m=(b[j].l+b[j].u)/2;a[j].u=m;b[j].l=m;return {a,b};}
struct Pending{int rid,depth;Box box;Eval val;};
volatile sig_atomic_t stopped=0;void signal_handler(int){stopped=1;}
int main(int argc,char**argv){
 string out="work_01011/upper_extra_order_cover.json";double seconds=180;bool resume=false,greedy=true;long maxnodes=6000000;int maxdepth=60;
 for(int j=1;j<argc;++j){string s=argv[j];if(s=="--out")out=argv[++j];else if(s=="--seconds")seconds=stod(argv[++j]);else if(s=="--nodes")maxnodes=stol(argv[++j]);else if(s=="--depth")maxdepth=stoi(argv[++j]);else if(s=="--resume")resume=true;else if(s=="--widest")greedy=false;else return 2;}
 signal(SIGINT,signal_handler);signal(SIGTERM,signal_handler);
 vector<int>events;vector<Pending>stack;array<long,21>counts{};array<long,16>perroot{};long leaves=0;int reached=0;double previous=0;
 if(resume){ifstream f(out+".checkpoint");long ne,ns;f>>ne>>ns>>leaves>>reached>>previous;assert(f);events.resize(ne);for(int&v:events)f>>v;for(auto&v:counts)f>>v;for(auto&v:perroot)f>>v;for(long j=0;j<ns;++j){Pending p;string value;f>>p.rid>>p.depth>>value>>p.val.second;p.val.first=stod(value);for(I&v:p.box)f>>v.l>>v.u;stack.push_back(p);}assert(f);}
 else for(int r=15;r>=0;--r)stack.push_back({r,0,root(r),{numeric_limits<double>::infinity(),-1}});
 auto start=chrono::steady_clock::now(),last=start;array<double,7>w={.4,.4,.4,1,1,1,2};
 auto elapsed=[&](){return chrono::duration<double>(chrono::steady_clock::now()-start).count();};
 while(!stack.empty()&&!stopped&&elapsed()<seconds&&(long)events.size()<maxnodes){
  Pending p=stack.back();stack.pop_back();reached=max(reached,p.depth);if(p.val.second<0)p.val=evaluate(p.box,p.rid);
  if(p.val.first< -1e-8){events.push_back(-p.val.second-1);++leaves;++counts[p.val.second];++perroot[p.rid];}
  else if(p.depth>=maxdepth){stack.push_back(p);break;}
  else{
   double widest=0;int dim=0;for(int j=0;j<7;++j){double ww=(p.box[j].u-p.box[j].l)*w[j];if(ww>widest){widest=ww;dim=j;}}
   Box left,right;Eval vl,vr;
   if(greedy){tuple<int,double,double,double>best{-1,-1e100,-1e100,-1e100};for(int j=0;j<7;++j){double width=(p.box[j].u-p.box[j].l)*w[j];if(width<widest/4)continue;auto[a,b]=halves(p.box,j);auto va=evaluate(a,p.rid),vb=evaluate(b,p.rid);auto score=make_tuple(int(va.first< -1e-8)+int(vb.first< -1e-8),-max(va.first,vb.first),-(va.first+vb.first),width);if(score>best){best=score;dim=j;left=a;right=b;vl=va;vr=vb;}}}
   else{tie(left,right)=halves(p.box,dim);vl=vr={numeric_limits<double>::infinity(),-1};}
   events.push_back(dim);stack.push_back({p.rid,p.depth+1,right,vr});stack.push_back({p.rid,p.depth+1,left,vl});
  }
  if(chrono::duration<double>(chrono::steady_clock::now()-last).count()>20){last=chrono::steady_clock::now();cerr<<"nodes "<<events.size()<<" leaves "<<leaves<<" root "<<p.rid<<" pending "<<stack.size()<<" depth "<<reached<<" seconds "<<elapsed()<<'\n';}
 }
 double total=previous+elapsed();ofstream f(out);f<<setprecision(17)<<"{\"schema\":\"weak_middle_upper_extra_order_cover_v1\",\"proof_status\":\""<<(stack.empty()?"discovery_complete_pending_independent_replay":"incomplete_discovery")<<"\",\"Q\":\"1105/256\",\"target\":\"upper_central_extra_above_P\",\"floor\":\"1/10\",\"root_count\":16,\"events\":[";
 for(size_t j=0;j<events.size();++j){if(j)f<<',';f<<events[j];}f<<"],\"frontier_count\":"<<stack.size()<<",\"nodes\":"<<events.size()<<",\"leaves\":"<<leaves<<",\"max_depth\":"<<reached<<",\"counts\":[";for(int j=0;j<21;++j){if(j)f<<',';f<<counts[j];}f<<"],\"leaves_per_root\":[";for(int j=0;j<16;++j){if(j)f<<',';f<<perroot[j];}f<<"],\"seconds\":"<<total<<"}\n";f.close();
 if(!stack.empty()){ofstream c(out+".checkpoint");c<<setprecision(17)<<events.size()<<' '<<stack.size()<<' '<<leaves<<' '<<reached<<' '<<total<<'\n';for(int v:events)c<<v<<' ';c<<'\n';for(long v:counts)c<<v<<' ';c<<'\n';for(long v:perroot)c<<v<<' ';c<<'\n';for(Pending p:stack){c<<p.rid<<' '<<p.depth<<' '<<p.val.first<<' '<<p.val.second;for(I v:p.box)c<<' '<<v.l<<' '<<v.u;c<<'\n';}}
 cout<<"{\"discovery_complete\":"<<(stack.empty()?"true":"false")<<",\"leaves\":"<<leaves<<",\"nodes\":"<<events.size()<<",\"pending\":"<<stack.size()<<",\"seconds\":"<<total<<"}\n";
}
