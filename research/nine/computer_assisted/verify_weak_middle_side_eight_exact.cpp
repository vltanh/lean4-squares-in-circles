// Independent exact replay of the wide-middle side-triple eight-original tree.
// Standard-library C++ only. No floating-point arithmetic, producer code,
// numerical tolerance, external solver, Lean, or CI is used for acceptance.
// The mathematical reference is the separately implemented Python verifier.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

using N=std::int64_t;
using W=__int128_t;
using UW=__uint128_t;
constexpr N SCALE=N(1)<<48;
constexpr N NEG=-1000*SCALE,POS=1000*SCALE;
void need(bool yes,const char* message){if(!yes)throw std::runtime_error(message);}
N narrow(W x){need(x>=std::numeric_limits<N>::min()&&x<=std::numeric_limits<N>::max(),"integer range exceeded");return N(x);}
W floorq(W a,W b){need(b>0,"nonpositive denominator");W q=a/b,r=a%b;return q-(r!=0&&a<0);}
W ceilq(W a,W b){need(b>0,"nonpositive denominator");W q=a/b,r=a%b;return q+(r!=0&&a>0);}
std::uint64_t isqrt(UW n){
 if(n==0)return 0;
 std::uint64_t upper=std::uint64_t(n>>64),lower=std::uint64_t(n);
 unsigned bits=upper?128-__builtin_clzll(upper):64-__builtin_clzll(lower);
 need((bits+1)/2<64,"square-root seed range");
 std::uint64_t x=std::uint64_t(1)<<((bits+1)/2);
 for(;;){std::uint64_t y=std::uint64_t((UW(x)+n/x)/2);if(y>=x)break;x=y;}
 need(UW(x)*x<=n&&UW(x+1)*(x+1)>n,"integer square-root enclosure");
 return x;
}
struct I {
 N lo,hi;
 I(N integer=0):lo(narrow(W(integer)*SCALE)),hi(lo){}
 static I raw(N l,N h){need(l<=h,"reversed interval");I x;x.lo=l;x.hi=h;return x;}
 static I raw(N x){return raw(x,x);}
 friend I operator+(I a,I b){return raw(narrow(W(a.lo)+b.lo),narrow(W(a.hi)+b.hi));}
 friend I operator-(I a){return raw(narrow(-W(a.hi)),narrow(-W(a.lo)));}
 friend I operator-(I a,I b){return a+-b;}
 friend I operator*(I a,I b){
   std::array<W,4> p={W(a.lo)*b.lo,W(a.lo)*b.hi,W(a.hi)*b.lo,W(a.hi)*b.hi};
   return raw(narrow(floorq(*std::min_element(p.begin(),p.end()),SCALE)),narrow(ceilq(*std::max_element(p.begin(),p.end()),SCALE)));
 }
 friend I operator/(I a,I b){
   need(b.lo>0,"division interval touches zero");
   I inverse=raw(narrow(floorq(W(SCALE)*SCALE,b.hi)),narrow(ceilq(W(SCALE)*SCALE,b.lo)));
   return a*inverse;
 }
 I sq()const{
   W a=W(lo)*lo,b=W(hi)*hi;
   return raw(narrow(floorq(lo<=0&&hi>=0?0:std::min(a,b),SCALE)),narrow(ceilq(std::max(a,b),SCALE)));
 }
 I ab()const{return raw(std::max({N(0),lo,narrow(-W(hi))}),std::max(narrow(lo<0?-W(lo):W(lo)),narrow(hi<0?-W(hi):W(hi))));}
 I rt()const{
   need(hi>=0,"negative radical");
   UW l=UW(std::max(N(0),lo))*SCALE,h=UW(hi)*SCALE;
   auto a=isqrt(l),b=isqrt(h);if(UW(b)*b<h)++b;
   return raw(narrow(a),narrow(b));
 }
};
I C(N a,N b=1){return I::raw(narrow(floorq(W(a)*SCALE,b)),narrow(ceilq(W(a)*SCALE,b)));}
I raw(N x){return I::raw(x);}
N down(N a,N b=1){return C(a,b).lo;}
N up(N a,N b=1){return C(a,b).hi;}
const I Q=C(1105,256),L=C(29,60),U=C(13,12),RHO=C(91,60),A=C(503,480),K=C(80669,93000),CSTAR=C(4421,12000);
using Frame=std::array<I,5>;
I imin(I a,I b){return I::raw(std::min(a.lo,b.lo),std::min(a.hi,b.hi));}
I imax(I a,I b){return I::raw(std::max(a.lo,b.lo),std::max(a.hi,b.hi));}
Frame shape(I t){
 auto point=[](N z){I v=raw(z),a=I(1)/(I(1)+v.sq()).rt(),b=v*a;return Frame{a,b,(a+b)/2,(a-b)/2,I(0)};};
 auto l=point(t.lo),h=point(t.hi);
 I a=I::raw(h[0].lo,l[0].hi),b=I::raw(l[1].lo,h[1].hi),hh=I::raw(l[2].lo,h[2].hi),k=I::raw(h[3].lo,l[3].hi);
 return {a,b,hh,k,I(1)/(4*hh)};
}
Frame shape_h(I h){
 I lo=raw(h.lo),hi=raw(h.hi),kl=(C(1,2)-lo.sq()).rt(),kh=(C(1,2)-hi.sq()).rt();
 I a=I::raw((hi+kh).lo,(lo+kl).hi),b=I::raw((lo-kl).lo,(hi-kh).hi),k=I::raw(kh.lo,kl.hi);
 return {a,b,h,k,I(1)/(4*h)};
}
I eta_h(I h){
 auto eta=[](N z){I v=raw(z);return (v-C(1,2)).sq()/v;};
 return I::raw(eta(h.lo).lo,eta(h.hi).hi);
}
N main_height_floor(I h){
 I z=raw(h.hi),bump=imax(I(0),imin((z-C(1,2))/6,(C(27,50)-z)/3));
 return (-C(2,3)*z+bump+C(1,400)).lo;
}
N div_lower(I n,I d){
 if(d.hi==0)return POS;
 if(n.lo>=0){W q=floorq(W(n.lo)*SCALE,d.hi);return q>POS?POS:narrow(q);}
 if(d.lo==0)return NEG;
 W q=floorq(W(n.lo)*SCALE,d.lo);
 // A quotient below -1000 is irrelevant to the physical lower bounds:
 // clearance is maximized with a nonnegative disk bound; endpoint overlap
 // gives r_minus>-k>=-1/2 and r_plus>=k>=0; cone ranges intersect +/-d.
 // Positive saturation similarly remains above every physical height.
 return q<NEG?NEG:narrow(q);
}
N support_lower(const Frame&s,int ss,const Frame&t,int st){
 I co=s[0]*t[0]+(ss*st)*s[1]*t[1],si=ss*s[1]*t[0]-st*s[0]*t[1];
 return std::max(SCALE,((I(1)+co.ab()+si.ab())/2).lo);
}
N psi_upper(I t){
 auto lo=shape(raw(t.lo)),hi=shape(raw(t.hi));
 N lin=std::max((lo[0]/2+C(19,54)*lo[1]).hi,(hi[0]/2+C(19,54)*hi[1]).hi);
 if(t.lo<=up(19,27)&&t.hi>=down(19,27))lin=std::max(lin,(I(1090).rt()/54).hi);
 return std::min(lin,(I(1)-hi[0]/2+hi[1]/18).hi);
}
N corner_upper(const Frame&s,I x,int sign){
 std::array<I,4> xx={s[2],sign*s[3],-s[2],-sign*s[3]},yy={-sign*s[3],s[2],sign*s[3],-s[2]};
 N out=up(91,60);
 for(int j=0;j<4;++j){I rad=Q-(x+xx[j]).sq();if(rad.hi<0)return NEG;out=std::min(out,rad.rt().hi-yy[j].lo);}
 return out;
}
N main_clearance(const Frame&s,int ss,const Frame&m,int sm,I d){
 I a=s[0],b=s[1],h=s[2],am=m[0],bm=m[1],gm=m[4];
 N sigma=support_lower(s,ss,m,sm),D=std::max(narrow(d.lo<0?-W(d.lo):W(d.lo)),narrow(d.hi<0?-W(d.hi):W(d.hi)));
 I delta=gm-raw(D);
 N reach=std::min({h.lo,div_lower(C(1,2)+delta*b,a),div_lower(C(1,2)+delta*a,b)}),inset=gm.lo+reach,owner=POS;
 std::array<std::pair<I,I>,4> axes={{{sm*am,bm},{-sm*bm,am},{ss*a,b},{-ss*b,a}}};
 for(auto n:axes){if(n.second.hi==0)continue;owner=std::min(owner,div_lower(raw(sigma)-n.first*d,n.second));}
 I rad=raw(sigma).sq()-raw(D).sq();N disk=I::raw(std::max(N(0),rad.lo),std::max(N(0),rad.hi)).rt().lo;
 return std::max({inset,owner,disk});
}
N endpoint_lower(const Frame&s,int sg,I x,N base,N c){
 N edge=std::min(up(503,480),up(91,60)-c);
 if(x.lo+s[2].lo<=edge)return base;
 I delta=x-raw(edge);
 auto reach=[&](int sign){return std::min(s[2].lo,sign>0?div_lower(C(1,2)+delta*s[1],s[0]):div_lower(C(1,2)+delta*s[0],s[1]));};
 N wp=c+reach(sg),wm=c+reach(-sg);
 return base+wm>0?std::max(base,wp):base;
}
struct Owner{I nx,mag;int sign;};
std::vector<std::pair<N,N>> pair_ranges(const Frame&s,int ss,const Frame&t,int st,I d,N lo,N hi,bool first){
 std::vector<std::pair<N,N>> out;if(lo>hi)return out;
 N sigma=support_lower(s,ss,t,st);
 std::array<Owner,4> axes={{{s[0],s[1],ss},{s[1],s[0],-ss},{t[0],t[1],st},{t[1],t[0],-st}}};
 for(auto n:axes){
   N low=-d.hi,high=d.hi;I num=raw(sigma)-n.nx*d;
   if(n.mag.hi==0){if(num.lo>0)continue;}
   else if(n.sign>0)low=std::max(low,div_lower(num,n.mag));
   else high=std::min(high,-div_lower(num,n.mag));
   if(low>high)continue;
   out.push_back(first?std::pair<N,N>{lo-high,hi-low}:std::pair<N,N>{lo+low,hi+high});
 }
 return out;
}

N margin(const std::array<I,9>&box,bool low_floor){
 I tl=box[0],tp=box[1],tr=box[2],Z=box[3],x=box[4],X=box[5],c0=box[6],hb=box[7],hc=box[8];
 auto left=shape(tl),p=shape(tp),right=shape(tr),bmain=shape_h(hb),cmain=shape_h(hc);
 I eb=eta_h(hb),ec=eta_h(hc),V=eb+ec;
 N psL=psi_upper(tl),psR=psi_upper(tr),hmax=std::min(up(8,15),(I(1)/(4*raw(c0.lo))).hi);
 I hh=raw(hmax);N jlo=(hh+(C(1,2)-hh.sq()).rt()).lo;
 N a0max=std::min(up(61,60),((Q-(I(1)-c0).sq()).rt()-raw(jlo)).hi);
 N a0min=(C(157,184)+V+C(27,92)*(X-raw(psR))).lo;
 N vcap=std::min({up(1,30),(C(27,92)*(C(451,810)-Z+raw(psL))).hi,
    (C(27,92)*(C(451,810)-X+raw(psR))).hi,(C(27,92)*(I(1)-Z-X+raw(psL)+raw(psR))).hi});
 I dl=x+Z,dr=X-x;
 N basic=std::min({vcap-V.lo,a0max-a0min,(c0-CSTAR-C(32,9)*V).hi,
    (dl-left[4]-p[4]).hi,(dr-p[4]-right[4]).hi,
    (left[2]+p[2]-dl).hi,(p[2]+right[2]-dr).hi});
 if(basic<0)return basic;
 N c3=std::max((CSTAR+C(32,9)*V).lo,(K-c0+C(32,9)*V).lo);
 N arc=(I(4)-C(73,30000)+V-(Q-(I(1)-c0).sq()).rt()).lo;
 need(arc>0,"endpoint arc sign");
 I rad=Q-raw(arc).sq();if(rad.hi<0)return rad.hi;
 c3=std::max(c3,(I(1)-rad.rt()).lo);
 N a3min=(C(157,184)+V+C(27,92)*(Z-raw(psL))).lo;
 rad=Q-(raw(a3min)+C(29927,30000)).sq();if(rad.hi<0)return rad.hi;
 c3=std::max(c3,(I(1)-rad.rt()).lo);
 N blo=(hb-raw(a0max)).lo,bhi=(C(1,60)-bmain[4]-ec).hi;
 N clo=(cmain[4]+eb-C(1,60)).lo,chi=(C(61,60)-hc).hi;
 N dmain=std::min(chi-blo,(hb+hc).hi);
 basic=std::min({basic,up(1,2)-c3,bhi-blo,chi-clo,dmain-(bmain[4]+cmain[4]).lo});
 if(basic<0)return basic;
 N bouter=(bmain[4]+ec-C(199,120)+C(32,9)*V).lo;
 N couter=(cmain[4]+eb-C(199,120)+C(32,9)*V).lo;
 N by=std::max({main_height_floor(hb),bouter,(raw(c0.lo)-C(121,60)-raw(bhi)).lo});
 N cy=std::max(couter,(raw(c3)+raw(clo)-C(121,60)).lo);
 I bx=I::raw(blo,bhi),cx=I::raw(clo,chi);N answer=NEG;
 for(int sb:{-1,1})for(int sc:{-1,1}){
   N sigma=support_lower(bmain,sb,cmain,sc);
   std::array<std::pair<I,I>,4> owners={{{bmain[0],sb*bmain[1]},{bmain[1],-sb*bmain[0]},
       {cmain[0],sc*cmain[1]},{cmain[1],-sc*cmain[0]}}};
   for(int sp:{-1,1}){
     N cbp=main_clearance(p,sp,bmain,sb,x-bx),ccp=main_clearance(p,sp,cmain,sc,x-cx);
     N pl=std::max(by+cbp,cy+ccp),ph=corner_upper(p,x,sp);
     if(low_floor)ph=std::min(ph,(p[2]+C(1,10)).hi);
     if(ph<pl){answer=std::max(answer,ph-pl);continue;}
     for(int sl:{-1,1}){
       N cbl=main_clearance(left,sl,bmain,sb,-Z-bx);
       N ll=endpoint_lower(left,-sl,Z,by+cbl,c0.lo),lh=corner_upper(left,Z,-sl);
       if(lh<ll){answer=std::max(answer,lh-ll);continue;}
       auto lefts=pair_ranges(left,sl,p,sp,dl,ll,lh,false);
       for(int sr:{-1,1}){
         N ccr=main_clearance(right,sr,cmain,sc,X-cx);
         N rl=endpoint_lower(right,sr,X,std::max(down(-9,20),cy+ccr),c3),rh=corner_upper(right,X,sr);
         if(!low_floor)rh=std::min(rh,up(3,5));
         if(rh<rl){answer=std::max(answer,rh-rl);continue;}
         auto rights=pair_ranges(p,sp,right,sr,dr,rl,rh,true);N best=NEG;
         for(auto lp:lefts)for(auto rp:rights){
           N pylo=std::max({pl,lp.first,rp.first}),pyhi=std::min({ph,lp.second,rp.second});
           N Bhi=std::min({pyhi-cbp,lh-cbl,-bouter}),Chi=std::min({pyhi-ccp,rh-ccr,-couter});
           N elo=std::max(-dmain,cy-Bhi),ehi=std::min(dmain,Chi-by);
           N overlap=std::min({pyhi-pylo,ehi-elo,Bhi-by,Chi-cy});
           if(overlap>=0){
             I E=I::raw(elo,ehi);N m=NEG;
             for(auto n:owners)m=std::max(m,(n.first*raw(dmain)+n.second*E).hi-sigma);
             overlap=std::min(overlap,m);
           }
           best=std::max(best,overlap);
         }
         answer=std::max(answer,std::min({ph-pl,lh-ll,rh-rl,best}));
       }
     }
   }
 }
 return std::min(basic,answer);
}

struct Certificate{std::string kind,status;std::uint64_t nodes=0,leaves=0,depth=0;std::vector<std::int8_t>events;};
class Parser{
 const std::string&text;std::size_t at=0;
 void space(){while(at<text.size()&&(text[at]==' '||text[at]=='\n'||text[at]=='\r'||text[at]=='\t'))++at;}
 char peek(){space();need(at<text.size(),"unexpected end of JSON");return text[at];}
 void take(char c){need(peek()==c,"unexpected JSON punctuation");++at;}
 std::string word(){take('"');std::string s;while(at<text.size()&&text[at]!='"'){unsigned char c=text[at++];need(c>=32&&c!='\\',"escaped or control string outside schema");s.push_back(char(c));}need(at<text.size(),"unterminated JSON string");++at;return s;}
 std::int64_t integer(){
   space();bool neg=false;if(at<text.size()&&text[at]=='-'){neg=true;++at;}
   need(at<text.size()&&text[at]>='0'&&text[at]<='9',"expected JSON integer");bool zero=text[at]=='0';std::uint64_t n=0;unsigned digits=0;
   while(at<text.size()&&text[at]>='0'&&text[at]<='9'){need(n<=100000000,"JSON integer too large");n=10*n+unsigned(text[at++]-'0');++digits;}
   need(!zero||digits==1,"leading zero in JSON integer");need(n<=1000000000,"JSON count too large");return neg?-std::int64_t(n):std::int64_t(n);
 }
 void ignored_number(){
   // Validate JSON number syntax only. These discovery timing/reserve
   // metadata are never converted to floating point or used mathematically.
   space();if(at<text.size()&&text[at]=='-')++at;
   need(at<text.size()&&text[at]>='0'&&text[at]<='9',"invalid metadata number");
   if(text[at]=='0')++at;else while(at<text.size()&&text[at]>='0'&&text[at]<='9')++at;
   if(at<text.size()&&text[at]=='.'){++at;std::size_t start=at;while(at<text.size()&&text[at]>='0'&&text[at]<='9')++at;need(at>start,"empty decimal fraction");}
   if(at<text.size()&&(text[at]=='e'||text[at]=='E')){++at;if(at<text.size()&&(text[at]=='+'||text[at]=='-'))++at;std::size_t start=at;while(at<text.size()&&text[at]>='0'&&text[at]<='9')++at;need(at>start,"empty decimal exponent");}
 }
public:
 explicit Parser(const std::string&s):text(s){}
 Certificate parse(){
   Certificate c;std::set<std::string>fields;take('{');
   for(;;){
     std::string key=word();need(fields.insert(key).second,"duplicate certificate field");take(':');
     if(key=="kind")c.kind=word();else if(key=="status")c.status=word();
     else if(key=="nodes"||key=="leaves"||key=="max_depth"){
       auto n=integer();need(n>=0,"negative certificate count");if(key=="nodes")c.nodes=n;else if(key=="leaves")c.leaves=n;else c.depth=n;
     }else if(key=="events"){
       take('[');if(c.nodes)c.events.reserve(c.nodes);
       if(peek()!=']')for(;;){auto tag=integer();need(0<=tag&&tag<=9,"unsupported split or leaf tag");c.events.push_back(std::int8_t(tag));if(peek()==']')break;take(',');}take(']');
     }else if(key=="frontier"){take('[');take(']');}
     else if(key=="least_float_reserve"||key=="seconds")ignored_number();
     else need(false,"unknown certificate field");
     if(peek()=='}')break;take(',');
   }
   take('}');space();need(at==text.size(),"trailing JSON data");
   need(fields==std::set<std::string>{"kind","status","nodes","leaves","max_depth","events","frontier","least_float_reserve","seconds"},"missing certificate field");
   need(c.kind=="low_right"||c.kind=="low_floor","wrong root family");need(c.status=="COMPLETE_DISCOVERY","incomplete discovery status");
   need(c.nodes>0&&c.events.size()==c.nodes&&c.nodes==2*c.leaves-1,"inconsistent counts");need(c.depth<=60,"exact cell depth budget");return c;
 }
};
constexpr std::array<N,9> ROOT_LEFT={0,0,0,29,-23,29,4421,10,10};
constexpr std::array<N,9> ROOT_RIGHT={1,1,1,65,23,65,6000,13,13};
constexpr std::array<N,9> ROOT_DEN={1,1,1,60,60,60,12000,20,20};
struct Cell{
 std::array<unsigned,9>level{};std::array<std::uint64_t,9>index{};unsigned depth=0;
 std::array<I,9>enclosure()const{
   std::array<I,9>box;
   for(unsigned j=0;j<9;++j){need(level[j]<=60,"coordinate depth budget");W power=W(1)<<level[j];need(W(index[j])<power,"cell outside root");W width=ROOT_RIGHT[j]-ROOT_LEFT[j],n=W(ROOT_LEFT[j])*power+width*index[j],d=W(ROOT_DEN[j])*power;box[j]=I::raw(narrow(floorq(n*SCALE,d)),narrow(ceilq((n+width)*SCALE,d)));}
   return box;
 }
};
std::string cell_description(const Cell&c){std::ostringstream out;out<<"[";for(int j=0;j<9;++j){if(j)out<<",";out<<"["<<c.level[j]<<","<<c.index[j]<<"]";}return out.str()+"]";}
int main(int argc,char**argv){
 try{
   need(argc>=2&&argc<=4,"usage: checker certificate.json [maximum_nodes_for_benchmark] [progress_nodes]");
   std::uint64_t limit=argc>=3?std::stoull(argv[2]):0,progress=argc>=4?std::stoull(argv[3]):100000;
   std::ifstream input(argv[1],std::ios::binary);need(bool(input),"cannot read certificate");std::string text((std::istreambuf_iterator<char>(input)),std::istreambuf_iterator<char>());
   auto cert=Parser(text).parse();auto begin=std::chrono::steady_clock::now();bool low_floor=cert.kind=="low_floor";
   std::vector<Cell>stack(1);std::uint64_t leaves=0,processed=0;unsigned depth=0;N least=std::numeric_limits<N>::max();
   for(auto tag:cert.events){
     need(!stack.empty(),"trailing event after complete root");auto cell=stack.back();stack.pop_back();depth=std::max(depth,cell.depth);
     if(tag<9){
       need(cell.depth<60&&cell.level[tag]<60,"split depth budget");auto left=cell,right=cell;left.depth=right.depth=cell.depth+1;++left.level[tag];++right.level[tag];left.index[tag]=2*cell.index[tag];right.index[tag]=2*cell.index[tag]+1;stack.push_back(right);stack.push_back(left);
     }else{
       need(tag==9,"unknown leaf rule");N m=margin(cell.enclosure(),low_floor);
       if(m>=0){std::cerr<<"Unproved leaf at event "<<processed<<" with margin "<<m<<"/"<<SCALE<<", cell "<<cell_description(cell)<<"\n";throw std::runtime_error("exact arithmetic did not exclude leaf");}
       least=std::min(least,-m);++leaves;
     }
     ++processed;
     if(progress&&processed%progress==0){auto ms=std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now()-begin).count();std::cout<<"{\"progress_nodes\":"<<processed<<",\"leaves\":"<<leaves<<",\"frontier\":"<<stack.size()<<",\"elapsed_ms\":"<<ms<<"}"<<std::endl;}
     if(limit&&processed>=limit){auto ms=std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now()-begin).count();std::cout<<"{\"status\":\"BENCHMARK_ONLY_INCOMPLETE\",\"nodes\":"<<processed<<",\"leaves\":"<<leaves<<",\"frontier\":"<<stack.size()<<",\"elapsed_ms\":"<<ms<<"}"<<std::endl;return 0;}
   }
   need(stack.empty(),"missing child or unfinished cover");need(leaves==cert.leaves&&processed==cert.nodes&&processed==2*leaves-1,"count mismatch");need(depth==cert.depth,"depth mismatch");
   auto ms=std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now()-begin).count();
   std::cout<<"{\"status\":\"EXACT_REPLAY_PASSED\",\"kind\":\""<<cert.kind<<"\",\"nodes\":"<<processed<<",\"leaves\":"<<leaves<<",\"maximum_depth\":"<<depth<<",\"scale\":"<<SCALE<<",\"minimum_exact_reserve\":\""<<least<<"/"<<SCALE<<"\",\"elapsed_ms\":"<<ms<<",\"arithmetic\":\"48-bit directed dyadics, checked signed __int128 arithmetic, integer-only radicals, exact rational root cells\"}"<<std::endl;
   return 0;
 }catch(const std::exception&e){std::cerr<<"REJECTED: "<<e.what()<<"\n";return 1;}
}
