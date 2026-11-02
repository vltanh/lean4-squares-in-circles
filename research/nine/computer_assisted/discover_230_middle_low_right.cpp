// UNTRUSTED FLOATING DISCOVERY ONLY. Exact independent replay is mandatory.
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
I operator*(I a,I b){ld v[]={a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi};return {*min_element(v,v+4),*max_element(v,v+4)};}
I operator/(I a,ld b){return {a.lo/b,a.hi/b};}
I sq(I a){return {(a.lo<=0&&a.hi>=0)?0:min(a.lo*a.lo,a.hi*a.hi),max(a.lo*a.lo,a.hi*a.hi)};}
I ab(I a){return {max({0.L,a.lo,-a.hi}),max(abs(a.lo),abs(a.hi))};}
I rec(I a){return {1/a.hi,1/a.lo};}
struct Frame{I a,b,h,k,g;};
Frame shape(I t){
 auto f=[](ld z){ld a=1/sqrtl(1+z*z),b=z*a;return array<ld,4>{a,b,(a+b)/2,(a-b)/2};};
 auto lo=f(t.lo),hi=f(t.hi);
 Frame r{{hi[0],lo[0]},{lo[1],hi[1]},{lo[2],hi[2]},{hi[3],lo[3]},I()};r.g=rec(I(4)*r.h);return r;
}
const ld Q=1105.L/256,l=29.L/60,rho=91.L/60;
ld ceiling(Frame s,I x,int sign){
 array<I,4> dx{s.h,I(sign)*s.k,-s.h,I(-sign)*s.k};
 array<I,4> dy{I(-sign)*s.k,s.h,I(sign)*s.k,-s.h};
 ld r=rho;
 for(int j=0;j<4;j++){I q=I(Q)-sq(x+dx[j]);if(q.hi<0)return -1000;r=min(r,sqrtl(max(0.L,q.hi))-dy[j].lo);}
 return r;
}
ld physical(Frame s,int ss,Frame t,int st,I D,ld lo,ld hi){
 if(lo>hi)return hi-lo;
 I E(lo,hi);
 I co=s.a*t.a+I(ss*st)*s.b*t.b;
 I si=I(ss)*s.b*t.a-I(st)*s.a*t.b;
 ld sigma=max(1.L,(1+ab(co).lo+ab(si).lo)/2);
 ld p=max({(s.a*D+I(ss)*s.b*E).hi,(s.b*D-I(ss)*s.a*E).hi,(t.a*D+I(st)*t.b*E).hi,(t.b*D-I(st)*t.a*E).hi});
 return p-sigma;
}
using Box=array<I,6>;
array<ld,3> margins(Box box){
 Frame L=shape(box[0]),P=shape(box[1]),R=shape(box[2]);
 I Z=box[3],x=box[4],X=box[5],dl=x+Z,dr=X-x;
 array<ld,3> result{(dl-L.g-P.g).hi,(dr-P.g-R.g).hi,1000};
 if(min(result[0],result[1])< -1e-8L)return result;
 ld pl=P.h.lo+509.L/4960;
 ld ll=max(27.L/40,221.L/600+min(L.h.lo,(I(.5)*rec(L.a)+box[0]*(Z-I(503.L/480))).lo));
 ld rl=-7.L/40,common=-1000;
 for(int sp:{-1,1}){
  ld pu=ceiling(P,x,sp),left=-1000,right=-1000;
  for(int sl:{-1,1}){
   ld lu=ceiling(L,Z,-sl),lo=max(-dl.hi,pl-lu),hi=min(dl.hi,pu-ll);
   left=max(left,min({lu-ll,dl.hi+pu-ll,dl.hi+lu-pl,physical(L,sl,P,sp,dl,lo,hi)}));
  }
  for(int sr:{-1,1}){
   ld ru=min(.6L,ceiling(R,X,sr)),lo=max(-dr.hi,rl-pu),hi=min(dr.hi,ru-pl);
   right=max(right,min({ru-rl,dr.hi+pu-rl,dr.hi+ru-pl,physical(P,sp,R,sr,dr,lo,hi)}));
  }
  common=max(common,min({pu-pl,left,right}));
 }
 result[2]=common;return result;
}
struct Job{Box box;int depth;};
int main(int argc,char**argv){
 string filename=argc>1?argv[1]:"230_middle_low_right_float_tree.json";
 long long limit=argc>2?stoll(argv[2]):2000000;
 Box root{I(0,1),I(0,1),I(0,1),I(11.L/12,13.L/12),I(-23.L/60,0),I(19.L/60,29.L/60)};
 array<ld,6> widths;for(int j=0;j<6;j++)widths[j]=root[j].hi-root[j].lo;
 vector<Job> stack{{root,0}};vector<int> events;long long leaves=0;int maxdepth=0;ld reserve=1000;bool complete=true;
 while(!stack.empty()){
  if((long long)events.size()>=limit){complete=false;break;}
  auto job=stack.back();stack.pop_back();maxdepth=max(maxdepth,job.depth);
  auto values=margins(job.box);int rule=min_element(values.begin(),values.end())-values.begin();
  if(values[rule]<-1e-8L){events.push_back(-rule-1);leaves++;reserve=min(reserve,-values[rule]);}
  else{
   if(job.depth>=60){complete=false;cerr<<"UNRESOLVED depth "<<job.depth<<"\n";break;}
   int axis=0;ld score=-1;
   for(int j=0;j<6;j++){ld w=(job.box[j].hi-job.box[j].lo)/widths[j];if(w>score){score=w;axis=j;}}
   ld mid=(job.box[axis].lo+job.box[axis].hi)/2;
   if(mid==job.box[axis].lo||mid==job.box[axis].hi){complete=false;break;}
   auto left=job.box,right=job.box;left[axis].hi=mid;right[axis].lo=mid;
   events.push_back(axis);stack.push_back({right,job.depth+1});stack.push_back({left,job.depth+1});
  }
  if(events.size()%200000==0)cerr<<"nodes "<<events.size()<<" leaves "<<leaves<<" frontier "<<stack.size()<<" depth "<<maxdepth<<"\n";
 }
 if(!complete||!stack.empty()){cerr<<"INCOMPLETE nodes "<<events.size()<<" leaves "<<leaves<<" frontier "<<stack.size()<<"\n";return 2;}
 ofstream out(filename);
 out<<"{\"status\":\"COMPLETE_UNTRUSTED_DISCOVERY\",\"nodes\":"<<events.size()<<",\"leaves\":"<<leaves<<",\"maxdepth\":"<<maxdepth<<",\"events\":[";
 for(size_t i=0;i<events.size();i++){if(i)out<<',';out<<events[i];}out<<"]}\n";
 cerr<<"COMPLETE nodes "<<events.size()<<" leaves "<<leaves<<" depth "<<maxdepth<<" reserve "<<reserve<<"\n";
}
