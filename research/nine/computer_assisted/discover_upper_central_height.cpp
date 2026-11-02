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
using Box=array<I,4>;
array<R,2> values(Box z){
  auto b=mainshape(z[0]),c=mainshape(z[1]),f=free_shape(z[2]);
  I V=b.eta+c.eta;
  I bl=z[0]-I(61.L/60),br=I(1.L/60)-b.g-c.eta;
  I cl=c.g+b.eta-I(1.L/60),cr=I(61.L/60)-z[1],x=z[3];
  auto dist=[&](I p){return ab(x-p).hi;};
  R left=min(-bl.hi+clearance(b,f,dist(bl)),-br.hi+clearance(b,f,dist(br)));
  R right=min(cl.lo+clearance(c,f,dist(cl)),cr.lo+clearance(c,f,dist(cr)));
  R cb=clearance(b,f,max(dist(bl),dist(br)));
  R cc=clearance(c,f,max(dist(cl),dist(cr)));
  R mid=clearance(b,c,(cr-bl).hi);
  R my=mid-129.L/80+min(-br.hi+cc,cl.lo+cb);
  R y=max({-.3L,-129.L/80+left,-129.L/80+right,
           -379.L/240+(16.L/9)*V.lo+(left+right)/2,my});
  return {V.lo-1.L/30,y+7.L/40};
}
struct Node{Box box;int depth;};
int main(int argc,char**argv){
  string outname=argc>1?argv[1]:"upper_central_height_candidate.json";
  long long limit=argc>2?stoll(argv[2]):20000000;
  Box root{I(.5L,.65L),I(.5L,.65L),I(0,1),I(0,29.L/60)};
  array<R,4> widths;for(int j=0;j<4;j++)widths[j]=root[j].hi-root[j].lo;
  vector<Node>todo{{root,0}};vector<int>events;long long leaves=0;int maxdepth=0;R least=1000;
  while(!todo.empty()&&(long long)events.size()<limit){
    auto n=todo.back();todo.pop_back();maxdepth=max(maxdepth,n.depth);
    auto v=values(n.box);int rule=v[0]>1e-9L?0:(v[1]>1e-9L?1:-1);
    if(rule>=0){events.push_back(-rule-1);leaves++;least=min(least,v[rule]);}
    else{
      int axis=0;R score=-1;
      for(int j=0;j<4;j++){R s=(n.box[j].hi-n.box[j].lo)/widths[j];if(s>score){axis=j;score=s;}}
      // A producer heuristic only: seek the split whose poorer child improves most.
      if(n.depth>=6){
        R best=-1e9;int choice=axis;
        for(int j=0;j<4;j++){
          if((n.box[j].hi-n.box[j].lo)/widths[j]<score/8)continue;
          R m=(n.box[j].lo+n.box[j].hi)/2;Box a=n.box,b=n.box;a[j].hi=m;b[j].lo=m;
          auto va=values(a),vb=values(b);
          R sa=max(va[0],va[1]),sb=max(vb[0],vb[1]);
          R s=min(sa,sb)+.05L*max(sa,sb);
          if(s>best){best=s;choice=j;}
        }
        axis=choice;
      }
      if(n.depth>90){cerr<<"UNRESOLVED at depth "<<n.depth<<"\n";return 3;}
      R m=(n.box[axis].lo+n.box[axis].hi)/2;Box a=n.box,b=n.box;a[axis].hi=m;b[axis].lo=m;
      events.push_back(axis);todo.push_back({b,n.depth+1});todo.push_back({a,n.depth+1});
    }
    if(events.size()%100000==0)cerr<<"nodes "<<events.size()<<" leaves "<<leaves<<" pending "<<todo.size()<<" depth "<<maxdepth<<"\n";
  }
  if(!todo.empty()){cerr<<"INCOMPLETE "<<events.size()<<" nodes, "<<todo.size()<<" frontier\n";return 2;}
  ofstream o(outname);o<<"{\"type\":\"wide_main_upper_central_height_v1\",\"status\":\"COMPLETE_UNTRUSTED_DISCOVERY\",\"root\":[[\"1/2\",\"13/20\"],[\"1/2\",\"13/20\"],[\"0\",\"1\"],[\"0\",\"29/60\"]],\"nodes\":"<<events.size()<<",\"leaves\":"<<leaves<<",\"maximum_depth\":"<<maxdepth<<",\"events\":[";
  for(size_t j=0;j<events.size();j++){if(j)o<<',';o<<events[j];}o<<"]}\n";
  cerr<<"COMPLETE nodes "<<events.size()<<" leaves "<<leaves<<" depth "<<maxdepth<<" reserve "<<setprecision(18)<<least<<"\n";
}
