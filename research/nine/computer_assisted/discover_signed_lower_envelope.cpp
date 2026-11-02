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

I signed_support(I t,I u,int signprod){
 auto one=[](double t,double u,int sg){double den=sqrt((1+t*t)*(1+u*u));return .5+(abs(1+sg*t*u)+abs(u-sg*t))/(2*den);};
 double a=one(t.l,signprod>0?u.u:u.l,signprod),b=one(t.u,signprod>0?u.l:u.u,signprod);
 double low=min(a,b),high=max(a,b);
 if(signprod>0){if(t.l<=u.u&&u.l<=t.u)low=1;}
 else if(t.l+u.l+t.l*u.l<=1&&t.u+u.u+t.u*u.u>=1)high=(1+sqrt(2.))/2;
 return I(low,high);
}


using Box=array<I,3>;using Eval=pair<double,int>;
Eval evaluate(const Box& b,int root){
 int sm=(root&2)?1:-1,ss=(root&1)?1:-1;
 I H=b[0],t=b[1],z=b[2];Frame f=frame(t);
 auto mf=[](double h){double k=sqrt(.5-h*h);return array<double,5>{h+k,h-k,1/(4*h),(h-k)/(h+k),k};};
 auto lo=mf(H.l),hi=mf(H.u);I a(hi[0],lo[0]),bb(lo[1],hi[1]),g(hi[2],lo[2]),tm(lo[3],hi[3]);
 I sigma=signed_support(tm,t,sm*ss);
 I gap(1e100);for(I xm:{g-1./60,61./60-H}){
  I dx=xm-z;I cur(1e100);
  for(auto [nx,ny]:array<pair<I,I>,4>{{{sm*a,bb},{-sm*bb,a},{ss*f.a,f.b},{-ss*f.b,f.a}}})cur=mn({cur,(sigma-nx*dx)/mx({ny,1./40})});
  gap=mn({gap,cur});
 }
 I U=top(z,f,-ss);
 auto pp=[](double h){double d=h-.5;return -.331-.45*d-1.75*d*d;};
 I target=sm<0?I(-1./3):I(pp(H.u),pp(H.l));
 return {(target-gap+U).u,0};
}
Box root(int){return {I(.5,.65),I(0,1),I(29./60,13./12)};}
pair<Box,Box> halves(Box b,int j){Box a=b;double m=(b[j].l+b[j].u)/2;a[j].u=m;b[j].l=m;return {a,b};}
struct Pending{int rid,depth;Box box;Eval val;};
int main(int argc,char**argv){
 string out="signed_lower_side_envelope.json";double seconds=60;long maxnodes=6000000;int maxdepth=70;
 for(int j=1;j<argc;++j){string s=argv[j];if(s=="--out")out=argv[++j];else if(s=="--seconds")seconds=stod(argv[++j]);else if(s=="--nodes")maxnodes=stol(argv[++j]);else return 2;}
 vector<int>ev;vector<Pending>stack;array<long,4>counts{};long leaves=0;int reached=0;
 for(int r=3;r>=0;r--)stack.push_back({r,0,root(r),{numeric_limits<double>::infinity(),-1}});
 auto start=chrono::steady_clock::now(),last=start;auto elapsed=[&](){return chrono::duration<double>(chrono::steady_clock::now()-start).count();};
 while(!stack.empty()&&elapsed()<seconds&&(long)ev.size()<maxnodes){
  auto p=stack.back();stack.pop_back();reached=max(reached,p.depth);if(p.val.second<0)p.val=evaluate(p.box,p.rid);
  if(p.val.first<-1e-8){ev.push_back(-1);++leaves;++counts[p.rid];}
  else if(p.depth>=maxdepth){stack.push_back(p);break;}
  else{
   array<double,3>scale={5,1,1};double widest=0;for(int j=0;j<3;j++)widest=max(widest,(p.box[j].u-p.box[j].l)*scale[j]);
   int dim=0;Box left,right;Eval vl,vr;tuple<int,double,double>best{-1,-1e100,-1e100};
   for(int j=0;j<3;j++){double w=(p.box[j].u-p.box[j].l)*scale[j];if(w<widest/4)continue;auto [l,r]=halves(p.box,j);auto a=evaluate(l,p.rid),b=evaluate(r,p.rid);auto sc=make_tuple(int(a.first<-1e-8)+int(b.first<-1e-8),-max(a.first,b.first),-a.first-b.first);if(sc>best){best=sc;dim=j;left=l;right=r;vl=a;vr=b;}}
   ev.push_back(dim);stack.push_back({p.rid,p.depth+1,right,vr});stack.push_back({p.rid,p.depth+1,left,vl});
  }
  if(chrono::duration<double>(chrono::steady_clock::now()-last).count()>10){last=chrono::steady_clock::now();cerr<<ev.size()<<" nodes "<<leaves<<" leaves root "<<p.rid<<" depth "<<reached<<" time "<<elapsed()<<'\n';}
 }
 ofstream f(out);f<<"{\"schema\":\"signed_lower_side_envelope_v1\",\"complete\":"<<(stack.empty()?"true":"false")<<",\"events\":[";for(size_t i=0;i<ev.size();i++){if(i)f<<',';f<<ev[i];}f<<"],\"leaves\":"<<leaves<<",\"nodes\":"<<ev.size()<<",\"depth\":"<<reached<<",\"perroot\":[";for(int j=0;j<4;j++){if(j)f<<',';f<<counts[j];}f<<"]}\n";
 cout<<"complete "<<stack.empty()<<" leaves "<<leaves<<" depth "<<reached<<" seconds "<<elapsed()<<'\n';
}
