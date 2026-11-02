// Untrusted floating interval discovery. Exact independent replay is required.
#include <algorithm>
#include <array>
#include <cmath>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
using R = long double;
struct I { R lo,hi; I(R a=0):lo(a),hi(a){} I(R a,R b):lo(a),hi(b){} };
I operator+(I a,I b){return {a.lo+b.lo,a.hi+b.hi};}
I operator-(I a){return {-a.hi,-a.lo};}
I operator-(I a,I b){return a+-b;}
I operator*(I a,I b){R p[]={a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi};return {*min_element(p,p+4),*max_element(p,p+4)};}
I operator/(I a,R b){return {a.lo/b,a.hi/b};}
I ab(I a){return {max({0.L,a.lo,-a.hi}),max(abs(a.lo),abs(a.hi))};}
struct Shape {I a,b,h,g,eta;};
Shape mainshape(I h){
  auto f=[](R z){R k=sqrtl(.5L-z*z);return array<R,3>{z+k,z-k,z+1/(4*z)-1};};
  auto a=f(h.lo),b=f(h.hi);
  return {{b[0],a[0]},{a[1],b[1]},h,{1/(4*h.hi),1/(4*h.lo)},{a[2],b[2]}};
}
Shape free_shape(I t){
  auto f=[](R z){R a=1/sqrtl(1+z*z),b=z*a;return array<R,3>{a,b,(a+b)/2};};
  auto a=f(t.lo),b=f(t.hi);
  return {{b[0],a[0]},{a[1],b[1]},{a[2],b[2]},{1/(4*b[2]),1/(4*a[2])},I()};
}
R clearance(Shape a,Shape b,R D){
  R sigma=max(1.L,(I(1)+a.a*b.a+a.b*b.b+ab(a.a*b.b-a.b*b.a)).lo/2);
  R out=1000;
  for(auto [nx,ny]:array<pair<I,I>,4>{{{a.a,a.b},{a.b,a.a},{b.a,b.b},{b.b,b.a}}}){
    R num=sigma-nx.hi*D;
    R q=num<=0?0:(ny.hi==0?1000:num/ny.hi);
    out=min(out,q);
  }
  return out;
}
I square(I a){return {(a.lo<=0&&a.hi>=0)?0:min(a.lo*a.lo,a.hi*a.hi),max(a.lo*a.lo,a.hi*a.hi)};}
const R Q=1105.L/256,l=29.L/60;
R ceiling(I x,Shape s){
  R best=-1000;
  for(int sign:{-1,1}){
    R v=91.L/60;
    for(int u:{-1,1})for(int w:{-1,1}){
      I dx=(I(u)*s.a-I(w*sign)*s.b)/2;
      I dy=(I(u*sign)*s.b+I(w)*s.a)/2;
      R rad=Q-square(x+dx).lo;
      if(rad<0)v=-1000;else v=min(v,sqrtl(rad)-dy.lo);
    }
    best=max(best,v);
  }
  return best;
}
using Box=array<I,6>;
array<R,2> values(Box z,bool own){
  auto b=mainshape(z[0]),c=mainshape(z[1]),f=free_shape(z[2]),g=free_shape(z[3]);
  I V=b.eta+c.eta;
  I bl=z[0]-I(20331.L/20000),br=I(331.L/20000)-b.g-c.eta;
  I cl=c.g+b.eta-I(331.L/20000),cr=I(20331.L/20000)-z[1];
  I xf=z[4],xg=z[5];auto dist=[](I x,I y){return ab(x-y).hi;};
  R bf=clearance(b,f,max(dist(xf,bl),dist(xf,br)));
  R cf=clearance(c,f,max(dist(xf,cl),dist(xf,cr)));
  R bg=clearance(b,g,max(dist(xg,bl),dist(xg,br)));
  R cg=clearance(c,g,max(dist(xg,cl),dist(xg,cr)));
  R middle=clearance(b,c,(cr-bl).hi);
  R left=min(clearance(b,f,dist(xf,bl))+clearance(b,g,dist(xg,bl)),
             clearance(b,f,dist(xf,br))+clearance(b,g,dist(xg,br)));
  R right=min(clearance(c,f,dist(xf,cl))+clearance(c,g,dist(xg,cl)),
              clearance(c,f,dist(xf,cr))+clearance(c,g,dist(xg,cr)));
  R lower=max({left,right,middle+min(cf+bg,bf+cg)})-f.h.hi-.1L;
  return {V.lo-1.L/30,lower-(own?g.h.hi+.45L:.6L)};
}
struct Node{Box box;int depth;};
int main(int argc,char**argv){
  bool own=argc>1&&string(argv[1])=="own";
  string outname=argc>2?argv[2]:(own?"wide_own_lower_floor_candidate.json":"wide_lower_height_candidate.json");
  Box root{I(.5L,.65L),I(.5L,.65L),I(0,1),I(0,1),I(0,l),I(own?0:-l,l)};
  array<R,6> widths;for(int j=0;j<6;j++)widths[j]=root[j].hi-root[j].lo;
  vector<Node>todo{{root,0}};vector<int>events;long long leaves=0;int maxdepth=0;R least=1000;
  while(!todo.empty()&&events.size()<10000000){
    auto n=todo.back();todo.pop_back();maxdepth=max(maxdepth,n.depth);
    auto v=values(n.box,own);int rule=v[0]>1e-9L?0:(v[1]>1e-9L?1:-1);
    if(rule>=0){events.push_back(-rule-1);leaves++;least=min(least,v[rule]);}
    else{
      if(n.depth>=35){
        Box point;for(int j=0;j<6;j++)point[j]=I((n.box[j].lo+n.box[j].hi)/2);
        auto p=values(point,own);
        if(max(p[0],p[1])< -1e-11L){
          cerr<<"POSSIBLE_RELAXATION_POINT depth "<<n.depth<<"\n";
          for(auto x:point)cerr<<setprecision(20)<<x.lo<<" ";cerr<<"\n";
          for(auto x:p)cerr<<setprecision(20)<<x<<" ";cerr<<"\n";return 3;
        }
      }
      int axis=0;R score=-1;
      for(int j=0;j<6;j++){R s=(n.box[j].hi-n.box[j].lo)/widths[j];if(s>score){axis=j;score=s;}}
      if(n.depth>=6){
        R best=-1e9;int choice=axis;
        for(int j=0;j<6;j++){
          if((n.box[j].hi-n.box[j].lo)/widths[j]<score/8)continue;
          R m=(n.box[j].lo+n.box[j].hi)/2;Box a=n.box,b=n.box;a[j].hi=m;b[j].lo=m;
          auto va=values(a,own),vb=values(b,own);R sa=max(va[0],va[1]),sb=max(vb[0],vb[1]);
          R s=min(sa,sb)+.05L*max(sa,sb);if(s>best){best=s;choice=j;}
        }axis=choice;
      }
      if(n.depth>90){cerr<<"UNRESOLVED at depth "<<n.depth<<"\n";return 3;}
      R m=(n.box[axis].lo+n.box[axis].hi)/2;Box a=n.box,b=n.box;a[axis].hi=m;b[axis].lo=m;
      events.push_back(axis);todo.push_back({b,n.depth+1});todo.push_back({a,n.depth+1});
    }
    if(events.size()%100000==0)cerr<<"nodes "<<events.size()<<" leaves "<<leaves<<" pending "<<todo.size()<<" depth "<<maxdepth<<"\n";
  }
  if(!todo.empty()){cerr<<"INCOMPLETE "<<events.size()<<" nodes\n";return 2;}
  ofstream o(outname);o<<"{\"type\":\"wide_main_low_floor_lower_height_v1\",\"status\":\"COMPLETE_UNTRUSTED_DISCOVERY\",\"own_half_floor\":"<<(own?"true":"false")<<",\"root\":[[\"1/2\",\"13/20\"],[\"1/2\",\"13/20\"],[\"0\",\"1\"],[\"0\",\"1\"],[\"0\",\"29/60\"],[\""<<(own?"0":"-29/60")<<"\",\"29/60\"]],\"nodes\":"<<events.size()<<",\"leaves\":"<<leaves<<",\"maximum_depth\":"<<maxdepth<<",\"events\":[";
  for(size_t j=0;j<events.size();j++){if(j)o<<',';o<<events[j];}o<<"]}\n";
  cerr<<"COMPLETE nodes "<<events.size()<<" leaves "<<leaves<<" depth "<<maxdepth<<" reserve "<<setprecision(18)<<least<<"\n";
}
