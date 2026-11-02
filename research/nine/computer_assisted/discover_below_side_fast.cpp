// Untrusted floating discovery only. Every complete tree requires independent exact replay.
#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <filesystem>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
struct I {double lo,hi;I(double a=0):lo(a),hi(a){}I(double a,double b):lo(a),hi(b){}};
I operator+(I a,I b){return {a.lo+b.lo,a.hi+b.hi};}I operator-(I a){return {-a.hi,-a.lo};}I operator-(I a,I b){return a+-b;}
I operator*(I a,I b){array<double,4> q={a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi};return {*min_element(q.begin(),q.end()),*max_element(q.begin(),q.end())};}
I operator/(I a,I b){return a*I(1/b.hi,1/b.lo);}I sq(I a){return {a.lo<=0&&0<=a.hi?0:min(a.lo*a.lo,a.hi*a.hi),max(a.lo*a.lo,a.hi*a.hi)};}
I ab(I a){return {max({0.,a.lo,-a.hi}),max(abs(a.lo),abs(a.hi))};}I rt(I a){return {sqrt(max(0.,a.lo)),sqrt(max(0.,a.hi))};}
I mn(I a,I b){return {min(a.lo,b.lo),min(a.hi,b.hi)};}I mx(I a,I b){return {max(a.lo,b.lo),max(a.hi,b.hi)};}
struct Or {I a,b,h,k;};
Or orient(I t){double al=1/sqrt(1+t.lo*t.lo),au=1/sqrt(1+t.hi*t.hi);return {{au,al},{t.lo*al,t.hi*au},{(1+t.lo)*al/2,(1+t.hi)*au/2},{(1-t.hi)*au/2,(1-t.lo)*al/2}};}
using Box=array<I,5>;
struct Forms {Or p,r;I am,bm,gm,eta,D,W,A,ylo,U,rad,ca,rr,supp,E;};
Forms forms(const Box& b){I tp=b[0],tr=b[1],x=b[2],X=b[3],h=b[4];Or p=orient(tp),r=orient(tr);I k=rt(I(.5)-sq(h));
 I am={h.hi+k.lo,h.lo+k.hi},bm={h.lo-k.hi,h.hi-k.lo},gm={1/(4*h.hi),1/(4*h.lo)},eta={h.lo+1/(4*h.lo)-1,h.hi+1/(4*h.hi)-1};
 I D=X-x,W=I(1)+r.h-p.h-D,A=mx(I(59./60),I(157./184)+I(27./92)*(p.h-x))+eta;
 I delta=-ab(x)-I(1./60),ra=(I(.5)+delta*p.b)/p.a,n=I(.5)+delta*p.a;
 I reach={min({p.h.lo,ra.lo,p.b.hi>0?n.lo/p.b.hi:1e100}),min(p.h.hi,ra.hi)};
 I s=mx(I(1)+ab(h-p.h),I(.5)+mx(k*p.a+h*p.b,h*p.a-k*p.b)),d=I(61./60)-h+ab(x);
 array<I,4> nums={mx(I(.1),s-am*d),mx(I(.1),s-bm*d),mx(I(.1),s-p.a*d),mx(I(.1),s-p.b*d)},dens={bm,am,p.b,p.a};
 double flo=1e100;for(int j=0;j<4;j++)if(dens[j].hi>0)flo=min(flo,nums[j].lo/dens[j].hi);
 I phy={flo,min((nums[1]/am).hi,(nums[3]/p.a).hi)};
 I ylo=mx(mx(gm+reach,rt(sq(s)-sq(d))),phy)-I(2./3)*h+mx(I(0),mn((h-I(.5))/I(6),(I(.54)-h)/I(3)))+I(1./400);
 I U=mx(mn(rt(I(1105./256)-sq(X+r.k))-r.h,r.k+rt(I(1105./256)-sq(X+r.h))),mn(rt(I(1105./256)-sq(X+r.h))-r.k,rt(I(1105./256)-sq(X-r.k))-r.h));
 I rad=I(1105./256)-sq(A+I(29927./30000)),ca=mx(I(4421./12000)+I(32./9)*eta,I(1)-rt(rad));
 I dr=X-I(503./480),rra=(I(.5)+dr*r.b)/r.a,rn=I(.5)+dr*r.a;I rr(min({r.h.lo,rra.lo,r.b.hi>0?rn.lo/r.b.hi:1e100}));
 I supp=mx(I(1)+ab(p.h-r.h),I(.5)+mx(p.k*r.a+p.h*r.b,p.h*r.a-p.k*r.b));
 return {p,r,am,bm,gm,eta,D,W,A,ylo,U,rad,ca,rr,supp,mn(U-ylo,D)};
}
double arc(double alpha,double beta,double lo,double hi){double R=sqrt(1105./256);if(lo>R)return 1e100;lo=max(-R,lo);hi=min(R,hi);if(hi<lo)return 1e100;double z=clamp(R*alpha/sqrt(alpha*alpha+beta*beta),lo,hi);return alpha*z+beta*sqrt(max(0.,1105./256-z*z));}
double weighted(const Box& b,const Forms& f){const auto& p=f.p;const auto&r=f.r;I x=b[2],X=b[3],tr=b[1];double lam=.9,kap=27./92,C=29927./30000+157./184+kap*p.h.lo+f.eta.lo;
 vector<pair<double,double>> branches={{0,r.h.lo},{tr.lo,.5/r.a.hi},{tr.hi,.5/r.a.hi}};I n2=I(.5)+(X-I(503./480))*r.a;if(r.b.hi>0)branches.push_back({0,n2.lo/r.b.hi});
 vector<vector<pair<double,double>>> corners={{{r.k.lo,r.h.lo},{r.h.lo,-r.k.hi}},{{r.h.lo,r.k.lo},{-r.k.hi,r.h.lo}}};
 double total=-1e100;for(auto own:array<pair<I,I>,2>{{{p.a,p.b},{r.a,r.b}}}){I ai=own.first,bi=own.second;double beta=bi.hi+lam,GX=-1e100;
 for(auto [slope,constant]:branches){double alpha=ai.hi-lam*slope;double chi=-1e100;for(auto chir:corners){double cap=1e100;for(auto [c,off]:chir)cap=min(cap,arc(alpha,beta,X.lo+c,X.hi+c)-alpha*c-beta*off-lam*constant+lam*slope*503./480);chi=max(chi,cap);}GX=max(GX,chi);}
 double gx=-1e100;for(double a:{ai.lo,ai.hi}){double alpha=a/kap;gx=max(gx,arc(alpha,lam,C-kap*x.hi,C-kap*x.lo)-alpha*C-lam);}total=max(total,GX+gx-(bi*f.ylo).lo-f.supp.lo);}return total;}
pair<double,int> evaluate(const Box& b,bool use_weighted){auto f=forms(b);auto p=f.p,r=f.r;I x=b[2],X=b[3];array<double,14> v;
 v[0]=(x-p.h+I(451./810)-I(92./27)*f.eta).hi;v[1]=(r.h+I(451./810)-X-I(92./27)*f.eta).hi;v[2]=f.W.hi;
 v[3]=(I(2)*sq(f.D)-sq(I(1)+ab(p.h-r.h))).hi;v[4]=(I(61./60)-f.A).hi;v[5]=(p.h+I(.1)-f.ylo).hi;
 v[6]=f.U.hi-f.ca.lo-f.rr.lo;v[7]=(f.U-f.ylo).hi;v[8]=(mx(p.a*f.D+p.b*f.E,r.a*f.D+r.b*f.E)-f.supp).hi;
 v[9]=(I(27./92)*f.W-f.eta).hi;v[10]=(I(1./30)-f.eta).hi;v[11]=f.rad.hi;v[12]=(sq(f.D)+sq(mx(f.E,I(0)))-sq(f.supp)).hi;
 int j=min_element(v.begin(),v.begin()+13)-v.begin();if(use_weighted&&v[j]>=-1e-8){v[13]=weighted(b,f);if(v[13]<v[j])j=13;}return {v[j],j};}
struct Entry {Box b;int depth;};
int main(int argc,char**argv){string output=argc>1?argv[1]:(filesystem::absolute(argv[0]).parent_path()/"weak_middle_below_side_fast_balanced_candidate.json").string();long limit=argc>2?stol(argv[2]):100000000;double seconds=argc>3?stod(argv[3]):90;bool use_weighted=argc>4?stoi(argv[4]):true;
 Box root={I(0,1),I(0,1),I(-23./405,23./60),I(23./30,13./12),I(.5,.65)};array<double,5> weights={1,1,1,1,1};if(argc>=10)for(int j=0;j<5;j++)weights[j]=stod(argv[5+j]);vector<Entry> todo={{root,0}};vector<int8_t> events;events.reserve(10000000);long leaves=0;int depth=0;array<long,14> counts={};auto start=chrono::steady_clock::now();
 while(!todo.empty()&&(long)events.size()<limit&&chrono::duration<double>(chrono::steady_clock::now()-start).count()<seconds){Entry e=todo.back();todo.pop_back();depth=max(depth,e.depth);auto [v,code]=evaluate(e.b,use_weighted);if(v<-1e-8){events.push_back(-code-1);leaves++;counts[code]++;continue;}if(e.depth>=70){todo.push_back(e);break;}int j=0;for(int k=1;k<5;k++)if((e.b[k].hi-e.b[k].lo)*weights[k]>(e.b[j].hi-e.b[j].lo)*weights[j])j=k;
 Box lo=e.b,hi=e.b;double mid=(e.b[j].lo+e.b[j].hi)/2;lo[j].hi=mid;hi[j].lo=mid;events.push_back(j);todo.push_back({hi,e.depth+1});todo.push_back({lo,e.depth+1});
 if(events.size()%1000000<2){double vol=1;for(auto &q:todo)vol-=ldexp(1.,-q.depth);cout<<"nodes "<<events.size()<<" leaves "<<leaves<<" frontier "<<todo.size()<<" depth "<<depth<<" volume "<<vol<<endl;}}
 ofstream out(output);out<<"{\"status\":\""<<(todo.empty()?"DISCOVERY_COMPLETE_AWAITING_EXACT_REPLAY":"INCOMPLETE_DISCOVERY")<<"\",\"events\":[";for(size_t j=0;j<events.size();j++){if(j)out<<',';out<<(int)events[j];}out<<"],\"nodes\":"<<events.size()<<",\"leaves\":"<<leaves<<",\"max_depth\":"<<depth<<",\"remaining\":"<<todo.size()<<",\"counts\":{";bool comma=false;for(int j=0;j<14;j++)if(counts[j]){if(comma)out<<',';comma=true;out<<'"'<<j<<"\":"<<counts[j];}out<<"},\"scope\":\"Untrusted floating discovery; original weak-middle below-side transfer, no mask closure\"}\n";
 cout<<(todo.empty()?"COMPLETE":"INCOMPLETE")<<" nodes="<<events.size()<<" leaves="<<leaves<<" depth="<<depth<<" remaining="<<todo.size()<<" seconds="<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;}
