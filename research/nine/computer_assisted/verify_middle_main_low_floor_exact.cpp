// Independent exact replay of the completed middle-main low-floor tree.
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
const I Q=C(1105,256),G=C(15,31),A=C(503,480),L=C(29,60),U=C(13,12),RHO=C(91,60);
using Frame=std::array<I,5>;
Frame shape(I t){
 auto point=[](N z){I v=raw(z),a=I(1)/(I(1)+v.sq()).rt(),b=v*a;return Frame{a,b,(a+b)/2,(a-b)/2,I(0)};};
 Frame l=point(t.lo),h=point(t.hi);
 I a=I::raw(h[0].lo,l[0].hi),b=I::raw(l[1].lo,h[1].hi),hh=I::raw(l[2].lo,h[2].hi),k=I::raw(h[3].lo,l[3].hi);
 return {a,b,hh,k,I(1)/(4*hh)};
}
N div_lower(I n,I d){
 if(d.hi==0)return POS;
 if(n.lo>=0){W q=floorq(W(n.lo)*SCALE,d.hi);return q>POS?POS:narrow(q);}
 if(d.lo==0)return NEG;
 return narrow(floorq(W(n.lo)*SCALE,d.lo));
}
N corner_upper(const Frame&s,I X,int sign){
 std::array<I,4> dx={s[2],sign*s[3],-s[2],-sign*s[3]},dy={-sign*s[3],s[2],sign*s[3],-s[2]};
 N bound=up(91,60);
 for(int j=0;j<4;++j){I rad=Q-(X+dx[j]).sq();if(rad.hi<0)return NEG;bound=std::min(bound,rad.rt().hi-dy[j].lo);}
 return bound;
}
N main_clearance_lower(const Frame&s,int sign,N D,I delta,bool generic,N gfloor,N sigmafloor){
 I a=s[0],b=s[1],h=s[2];N reach=h.lo;
 if(generic||sign<0)reach=std::min(reach,div_lower(C(1,2)+delta*b,a));
 if(generic||sign>0)reach=std::min(reach,div_lower(C(1,2)+delta*a,b));
 I rad=raw(sigmafloor).sq()-raw(D).sq();
 N disk=I::raw(std::max(N(0),rad.lo),std::max(N(0),rad.hi)).rt().lo;
 return std::max(gfloor+reach,disk);
}
N endpoint_lower(const Frame&s,int sign,I X,N base,N c){
 N edge=std::min(up(503,480),up(91,60)-c);
 if(X.lo+s[2].lo<=edge)return base;
 I delta=X-raw(edge);
 auto reach=[&](int ss){N r=ss>0?div_lower(C(1,2)+delta*s[1],s[0]):div_lower(C(1,2)+delta*s[0],s[1]);return std::min(s[2].lo,r);};
 N wp=c+reach(sign),wm=c+reach(-sign);
 return base+wm>0?std::max(base,wp):base;
}
N support_lower(const Frame&s,int ss,const Frame&t,int st){
 I co=s[0]*t[0]+(ss*st)*s[1]*t[1],si=ss*s[1]*t[0]-st*s[0]*t[1];
 return std::max(SCALE,((I(1)+co.ab()+si.ab())/2).lo);
}
struct Owner{I nx,mag;int sign;};
std::array<Owner,4> owners(const Frame&s,int ss,const Frame&t,int st){
 return {{{s[0],s[1],ss},{s[1],s[0],-ss},{t[0],t[1],st},{t[1],t[0],-st}}};
}
N directed_pair_upper(const Frame&s,int ss,const Frame&t,int st,I D,N elo,N ehi){
 if(elo>ehi)return ehi-elo;
 I E=I::raw(elo,ehi);N bound=NEG;
 for(auto n:owners(s,ss,t,st))bound=std::max(bound,(n.nx*D+n.sign*n.mag*E).hi);
 return bound-support_lower(s,ss,t,st);
}
N physical_gap_lower(const Frame&s,int ss,const Frame&t,int st,N elo,N ehi){
 if(elo>ehi)return POS;
 I E=I::raw(elo,ehi);N sigma=support_lower(s,ss,t,st),bound=POS;
 for(auto n:owners(s,ss,t,st)){
   I required=raw(sigma)-n.sign*n.mag*E;
   // A physical cone gap is nonnegative. A nonpositive relaxed numerator
   // therefore contributes the harmless lower bound zero, avoiding an
   // unbounded negative quotient at a horizontal-component endpoint.
   N candidate=required.lo<=0?0:(n.nx.hi==0?POS:div_lower(required,n.nx));
   bound=std::min(bound,candidate);
 }
 return bound;
}
N shared_height_owner_upper(const Frame&left,int sl,const Frame&p,int sp,const Frame&right,int sr,
 I dl,I dr,I Z,I x,I X,N pl,N yp,N ll,N lh,N rl,N rh){
 N elo=std::max(-dl.hi,pl-lh),ehi=std::min(dl.hi,yp-ll),flo=std::max(-dr.hi,rl-yp),fhi=std::min(dr.hi,rh-pl);
 if(elo>ehi||flo>fhi)return std::min(ehi-elo,fhi-flo);
 I E=I::raw(elo,ehi),V=I::raw(flo,fhi);
 N sL=support_lower(left,sl,p,sp),sR=support_lower(p,sp,right,sr),answer=NEG;
 auto ol=owners(left,sl,p,sp),orr=owners(p,sp,right,sr);
 for(int ia=0;ia<4;++ia)for(int ib=0;ib<4;++ib){
   auto n=ol[ia],m=orr[ib];I ny=n.sign*n.mag,my=m.sign*m.mag;
   N one=(n.nx*dl+ny*E).hi-sL,two=(m.nx*dr+my*V).hi-sR;
   I ac=n.nx*m.nx,cb=m.nx*ny,ad=n.nx*my;
   I cross=ac*(Z+X)+(cb-ad)*I::raw(pl,yp)-cb*raw(n.sign>0?ll:lh)+ad*raw(m.sign>0?rh:rl)-m.nx*raw(sL)-n.nx*raw(sR);
   N horizontal=cross.hi,weighted=POS;
   if(n.sign==m.sign){
     I aa=raw(sL)-n.nx*dl+ny*raw(n.sign>0?ll:lh),bb=raw(sR)-m.nx*dr-my*raw(m.sign>0?rh:rl);
     weighted=-(m.mag*aa+n.mag*bb).lo;
     N yl=n.sign>0?ll:lh,yr=m.sign>0?rh:rl;
     I expanded=m.mag*raw(sL)+n.mag*raw(sR)-m.mag*n.nx*Z-n.mag*m.nx*X+(n.mag*m.nx-m.mag*n.nx)*x+n.sign*n.mag*m.mag*raw(yl-yr);
     weighted=std::min(weighted,-expanded.lo);
     if(ia==ib+2&&ib<2)weighted=std::min(weighted,(n.nx*(Z+X)+ny*raw(yr-yl)).hi-sL-sR);
   }
   answer=std::max(answer,std::min({one,two,weighted,horizontal}));
 }
 return answer;
}
N effective_width_upper(I t){
 Frame l=shape(raw(t.lo)),h=shape(raw(t.hi));
 N linear=std::max((l[0]/2+C(19,54)*l[1]).hi,(h[0]/2+C(19,54)*h[1]).hi);
 if(t.lo<=up(19,27)&&t.hi>=down(19,27))linear=std::max(linear,(I(1090).rt()/54).hi);
 N curve=(I(1)-h[0]/2+h[1]/18).hi;
 return std::min(linear,curve);
}
bool contract_low_floor(const Frame&left,const Frame&p,const Frame&right,I&Z,I&x,I&X,I c,I tl,I tr){
 N psL=effective_width_upper(tl),psR=effective_width_upper(tr);
 N hmax=std::min(up(8,15),(I(1)/(4*raw(c.lo))).hi);
 I hh=raw(hmax);N jleft=(hh+(C(1,2)-hh.sq()).rt()).lo;
 N a0=std::min(up(61,60),((Q-(I(1)-c).sq()).rt()-raw(jleft)).hi);
 N zcap=(C(451,810)+raw(psL)).hi,xcap=(C(451,810)+raw(psR)).hi,total=(I(1)+raw(psL)+raw(psR)).hi;
 N adaptive=(raw(psR)+C(92,27)*(raw(a0)-C(157,184))).hi;
 for(int pass=0;pass<3;++pass){
   x.lo=std::max({x.lo,down(-1,5),down(23,150)-p[4].hi,p[4].lo+left[4].lo-Z.hi,X.lo-p[2].hi-right[2].hi});
   x.hi=std::min({x.hi,left[2].hi+p[2].hi-Z.lo,X.hi-p[4].lo-right[4].lo});
   Z.lo=std::max(Z.lo,left[4].lo+p[4].lo-x.hi);X.lo=std::max(X.lo,x.lo+p[4].lo+right[4].lo);
   Z.hi=std::min({Z.hi,left[2].hi+p[2].hi-x.lo,zcap,total-X.lo});
   X.hi=std::min({X.hi,x.hi+p[2].hi+right[2].hi,xcap,total-Z.lo,adaptive});
   if(x.lo>x.hi||Z.lo>Z.hi||X.lo>X.hi)return false;
 }
 return true;
}

N low_floor_upper(const Frame&left,const Frame&p,const Frame&right,I Z,I x,I X,I c,I tl,I tp,I tr,int pass_number=0){
 I ap=p[0],bp=p[1],hp=p[2],kp=p[3];
 I ar=right[0],br=right[1],hr=right[2];
 N answer=NEG,union_lo=POS,union_hi=NEG;
 Frame left_low=shape(raw(tl.lo)),p_low=shape(raw(tp.lo));
 N psi_left=effective_width_upper(tl),psi_right=effective_width_upper(tr);
 N cap_upper=std::min({up(1,60),(C(27,184)*(C(451,810)-Z+raw(psi_left))).hi,
   (C(27,184)*(C(451,810)-X+raw(psi_right))).hi,
   (C(27,184)*(I(1)-Z-X+raw(psi_left)+raw(psi_right))).hi});
 N a_left=std::max(down(59,60),(C(157,184)+C(27,92)*(X-raw(psi_right))).lo);
 N hmax=std::min(up(8,15),(I(1)/(4*raw(c.lo))).hi);
 I hh=raw(hmax);N jleft=(hh+(C(1,2)-hh.sq()).rt()).lo;
 N a0_upper=std::min(up(61,60),((Q-(I(1)-c).sq()).rt()-raw(jleft)).hi);
 cap_upper=std::min(cap_upper,((raw(a0_upper)-raw(a_left))/2).hi);
 // These early exits are already retained necessary inequalities in the
 // Python reference. Checking them before reciprocals also keeps the
 // bounded fixed-point implementation away from irrelevant huge values.
 if(cap_upper<0)return cap_upper;
 for(int sp:{-1,1}){
   I delta_p=I(1)-raw(a0_upper)-x;
   N reach_p=std::min(hp.lo,sp<0?div_lower(C(1,2)+delta_p*bp,ap):div_lower(C(1,2)+delta_p*ap,bp));
   N axis_allowed=sp<0?(C(11,25)+tp*(kp-delta_p)).hi:up(11,25)-div_lower(kp+delta_p,tp);
   N allowed_g=std::min((hp+C(11,25)-raw(reach_p)).hi,axis_allowed);
   if(allowed_g<down(15,31)){answer=std::max(answer,allowed_g-down(15,31));continue;}
   N needed=std::max(N(0),(I(1)/(4*raw(allowed_g))-C(1,2)).lo);
   N allowed_e=std::min(cap_upper,up(1,60));
   if(needed>allowed_e){answer=std::max(answer,allowed_e-needed);continue;}
   N gain=(2*raw(needed).sq()/(I(1)+2*raw(needed))).lo;
   delta_p=delta_p+raw(gain);
   N yp=(hp+C(1,10)).hi;
   N c_right=std::max(down(4421,12000),(C(80669,93000)-c+C(64,9)*raw(needed)).lo);
   N a_right=std::max(down(59,60),(C(157,184)+C(27,92)*(Z-raw(psi_left))).lo)+2*needed;
   I endpoint_rad=Q-(raw(a_right)+C(29927,30000)).sq();
   if(endpoint_rad.hi<0){answer=std::max(answer,endpoint_rad.hi);continue;}
   c_right=std::max(c_right,SCALE-endpoint_rad.rt().hi);
   N arc=(I(4)-C(73,30000)+2*raw(needed)-(Q-(I(1)-c).sq()).rt()).lo;
   need(arc>0,"arc resource sign");
   I rad=Q-raw(arc).sq();
   if(rad.hi<0){answer=std::max(answer,rad.hi);continue;}
   c_right=std::max(c_right,SCALE-rad.rt().hi);
   if(c_right>up(1,2)){answer=std::max(answer,up(1,2)-c_right);continue;}
   for(int sr:{-1,1}){
     N rh=corner_upper(right,X,sr),rr=0;
     bool overlap=X.lo+hr.lo>up(503,480);
     N e_upper=cap_upper;
     if(overlap){
       I delta=X-A;
       rr=std::min(hr.lo,sr>0?div_lower(C(1,2)+delta*br,ar):div_lower(C(1,2)+delta*ar,br));
       e_upper=std::min(e_upper,(C(9,64)*(raw(rh)-raw(rr)-C(80669,93000)+c)).hi);
     }
     if(e_upper<0){answer=std::max(answer,e_upper);continue;}
     N e_margin=e_upper,g_main=(I(1)/(I(2)+4*raw(e_upper))).lo;
     I xx=x;
     N xmin=sp<0?(I(1)-raw(a0_upper)+raw(gain)-kp+(raw(g_main)-C(11,25))/raw(tp.hi)).lo:
       (I(1)-raw(a0_upper)+raw(gain)+kp+tp*(raw(g_main)-C(11,25))).lo;
     xx.lo=std::max(xx.lo,xmin);
     if(xx.lo>xx.hi){answer=std::max(answer,xx.hi-xx.lo);continue;}
     I dl=xx+Z,dr=X-xx;
     I main_h=C(1,2)+raw(e_upper),main_k=(C(1,2)-main_h.sq()).rt();
     auto main_support=[&](const Frame&s){return std::max(SCALE,(C(1,2)+s[1]*main_h+s[0]*main_k).lo);};
     N pl=down(-17,50)+main_clearance_lower(p,sp,(x+raw(a0_upper)-C(1,2)-raw(needed)).hi,delta_p,false,g_main,main_support(p_low));
     N rl=overlap?std::max(down(3,5),c_right+rr):down(3,5);
     N elo=std::max(-dr.hi,rl-yp),ehi=std::min(dr.hi,rh-pl);
     N right_margin=std::min({rh-rl,ehi-elo,directed_pair_upper(p,sp,right,sr,dr,elo,ehi)});
     N main_axis=sp<0?(tp*(kp-delta_p)).hi-(raw(g_main)-C(11,25)).lo:
       (-kp-delta_p-tp*(raw(g_main)-C(11,25))).hi;
     N basic=std::min({yp-pl,right_margin,main_axis,e_margin-needed,up(1,60)-needed,up(1,2)-c_right});
     if(basic<0){answer=std::max(answer,basic);continue;}
     N best_left=NEG;
     for(int sl:{-1,1}){
       N D=std::max((Z-L).hi,(raw(a0_upper)-C(1,2)-Z).hi)-needed;
       I delta_l=raw(std::min((C(59,60)-Z).lo,(Z+I(1)-raw(a0_upper)).lo)+gain);
       N clearance=main_clearance_lower(left,-sl,D,delta_l,Z.lo<up(8,15),g_main,main_support(left_low));
       N ll=endpoint_lower(left,-sl,Z,down(-17,50)+clearance,c.lo),lh=corner_upper(left,Z,-sl);
       N lo=std::max(-dl.hi,pl-lh),hi=std::min(dl.hi,yp-ll);
       N gap_left=physical_gap_lower(left,sl,p,sp,lo,hi);
       N gap_right=physical_gap_lower(p,sp,right,sr,std::max(-dr.hi,rl-yp),std::min(dr.hi,rh-pl));
       N new_lo=std::max(xx.lo,gap_left-Z.hi),new_hi=std::min(xx.hi,X.hi-gap_right);
       if(new_lo>new_hi){best_left=std::max(best_left,new_hi-new_lo);continue;}
       I xxx=I::raw(new_lo,new_hi),ddl=xxx+Z,ddr=X-xxx;
       lo=std::max(-ddl.hi,pl-lh);hi=std::min(ddl.hi,yp-ll);
       N left_margin=std::min({lh-ll,hi-lo,directed_pair_upper(left,sl,p,sp,ddl,lo,hi),
         directed_pair_upper(p,sp,right,sr,ddr,std::max(-ddr.hi,rl-yp),std::min(ddr.hi,rh-pl))});
       if(left_margin>=0)left_margin=std::min(left_margin,shared_height_owner_upper(left,sl,p,sp,right,sr,ddl,ddr,Z,xxx,X,pl,yp,ll,lh,rl,rh));
       best_left=std::max(best_left,left_margin);
       N chart=std::min({yp-pl,left_margin,right_margin,main_axis,e_margin-needed,up(1,60)-needed,up(1,2)-c_right});
       if(chart>=0){union_lo=std::min(union_lo,xxx.lo);union_hi=std::max(union_hi,xxx.hi);}
     }
     N branch=std::min({yp-pl,best_left,right_margin,main_axis,e_margin-needed,up(1,60)-needed,up(1,2)-c_right});
     answer=std::max(answer,branch);
   }
 }
 if(pass_number<3&&answer>=0&&union_lo<=union_hi&&(union_lo>x.lo||union_hi<x.hi)){
   return low_floor_upper(left,p,right,Z,I::raw(std::max(x.lo,union_lo),std::min(x.hi,union_hi)),X,c,tl,tp,tr,pass_number+1);
 }
 return answer;
}

N margin(std::array<I,7> box){
 I tl=box[0],tp=box[1],tr=box[2],Z=box[3],x=box[4],X=box[5],c=box[6];
 Frame left=shape(tl),p=shape(tp),right=shape(tr);
 if(!contract_low_floor(left,p,right,Z,x,X,c,tl,tr))return NEG;
 return low_floor_upper(left,p,right,Z,x,X,c,tl,tp,tr);
}

struct Certificate {
 std::string kind,status;
 std::uint64_t nodes=0,leaves=0,depth=0;
 std::vector<std::int8_t> events;
};
class Parser {
 const std::string&text;std::size_t at=0;
 void space(){while(at<text.size()&&(text[at]==' '||text[at]=='\n'||text[at]=='\r'||text[at]=='\t'))++at;}
 char peek(){space();need(at<text.size(),"unexpected end of JSON");return text[at];}
 void take(char c){need(peek()==c,"unexpected JSON punctuation");++at;}
 std::string word(){
   take('"');std::string s;
   while(at<text.size()&&text[at]!='"'){
     unsigned char c=text[at++];need(c>=32&&c!='\\',"escaped or control string not in certificate schema");s.push_back(char(c));
   }
   need(at<text.size(),"unterminated JSON string");++at;return s;
 }
 std::int64_t integer(){
   space();bool neg=false;if(at<text.size()&&text[at]=='-'){neg=true;++at;}
   need(at<text.size()&&text[at]>='0'&&text[at]<='9',"expected JSON integer");
   bool zero=text[at]=='0';std::uint64_t n=0;unsigned digits=0;
   while(at<text.size()&&text[at]>='0'&&text[at]<='9'){
     need(n<=100000000,"certificate integer is too large");n=10*n+unsigned(text[at++]-'0');++digits;
   }
   need(!zero||digits==1,"leading zero in JSON integer");
   need(n<=1000000000,"certificate integer exceeds supported counts");
   return neg?-std::int64_t(n):std::int64_t(n);
 }
public:
 explicit Parser(const std::string&s):text(s){}
 Certificate parse(){
   Certificate c;std::set<std::string> fields;take('{');
   for(;;){
     std::string key=word();need(fields.insert(key).second,"duplicate certificate field");take(':');
     if(key=="kind")c.kind=word();
     else if(key=="status")c.status=word();
     else if(key=="nodes"||key=="leaves"||key=="max_depth"){
       auto n=integer();need(n>=0,"negative certificate count");
       if(key=="nodes")c.nodes=n;else if(key=="leaves")c.leaves=n;else c.depth=n;
     }else if(key=="events"){
       take('[');if(c.nodes)c.events.reserve(c.nodes);
       if(peek()!=']')for(;;){
         auto tag=integer();need((tag>=0&&tag<7)||tag==-6,"unsupported split/leaf tag");
         c.events.push_back(std::int8_t(tag));
         if(peek()==']')break;
         take(',');
       }
       take(']');
     }else need(false,"unknown certificate field");
     if(peek()=='}')break;
     take(',');
   }
   take('}');space();need(at==text.size(),"trailing JSON data");
   need(fields==std::set<std::string>{"kind","status","nodes","leaves","max_depth","events"},"missing certificate field");
   need(c.kind=="low_floor","wrong root family");
   need(c.status=="COMPLETE_UNTRUSTED_DISCOVERY","wrong certificate status");
   need(c.events.size()==c.nodes&&c.nodes>0&&c.nodes==2*c.leaves-1,"inconsistent certificate counts");
   need(c.depth<=60,"certificate exceeds exact cell-depth budget");
   return c;
 }
};

// The exact root endpoints use a common rational denominator in each
// coordinate. A cell is its dyadic subinterval, represented by integer
// level/index data. Rounded interval endpoints never define the partition.
constexpr std::array<N,7> ROOT_LEFT={0,1,0,29,-23,29,4421};
constexpr std::array<N,7> ROOT_RIGHT={1,27,1,65,23,65,6000};
constexpr std::array<N,7> ROOT_DEN={1,27,1,60,60,60,12000};
struct Cell {
 std::array<unsigned,7> level{};
 std::array<std::uint64_t,7> index{};
 unsigned depth=0;
 std::array<I,7> enclosure()const{
   std::array<I,7> box;
   for(unsigned j=0;j<7;++j){
     need(level[j]<=60,"cell coordinate depth");W power=W(1)<<level[j];
     need(W(index[j])<power,"cell index outside root");
     W width=ROOT_RIGHT[j]-ROOT_LEFT[j];
     W n=W(ROOT_LEFT[j])*power+width*index[j],d=W(ROOT_DEN[j])*power;
     box[j]=I::raw(narrow(floorq(n*SCALE,d)),narrow(ceilq((n+width)*SCALE,d)));
   }
   return box;
 }
};

std::string cell_description(const Cell&c){
 std::ostringstream out;out<<"[";
 for(int i=0;i<7;++i){if(i)out<<",";out<<"["<<c.level[i]<<","<<c.index[i]<<"]";}return out.str()+"]";
}

int main(int argc,char**argv){
 try{
   need(argc>=2&&argc<=4,"usage: checker certificate.json [maximum_nodes_for_benchmark] [progress_nodes]");
   std::uint64_t limit=argc>=3?std::stoull(argv[2]):0,progress=argc>=4?std::stoull(argv[3]):100000;
   std::ifstream input(argv[1],std::ios::binary);need(bool(input),"cannot read certificate");
   std::string text((std::istreambuf_iterator<char>(input)),std::istreambuf_iterator<char>());
   Certificate cert=Parser(text).parse();
   auto start=std::chrono::steady_clock::now();
   std::vector<Cell> stack(1);std::uint64_t leaves=0,processed=0;unsigned depth=0;N least=std::numeric_limits<N>::max();
   for(auto tag:cert.events){
     need(!stack.empty(),"trailing event after complete root");
     Cell cell=stack.back();stack.pop_back();depth=std::max(depth,cell.depth);
     if(tag>=0){
       need(cell.depth<60&&cell.level[tag]<60,"split exceeds exact depth budget");
       Cell left=cell,right=cell;left.depth=right.depth=cell.depth+1;
       ++left.level[tag];++right.level[tag];left.index[tag]=2*cell.index[tag];right.index[tag]=2*cell.index[tag]+1;
       stack.push_back(right);stack.push_back(left);
     }else{
       need(tag==-6,"unknown leaf rule");N m=margin(cell.enclosure());
       if(m>=0){std::cerr<<"Unproved leaf at event "<<processed<<" with margin "<<m<<"/"<<SCALE<<", cell "<<cell_description(cell)<<"\n";throw std::runtime_error("exact arithmetic did not exclude leaf");}
       least=std::min(least,-m);++leaves;
     }
     ++processed;
     if(progress&&processed%progress==0){
       auto ms=std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now()-start).count();
       std::cout<<"{\"progress_nodes\":"<<processed<<",\"leaves\":"<<leaves<<",\"frontier\":"<<stack.size()<<",\"elapsed_ms\":"<<ms<<"}"<<std::endl;
     }
     if(limit&&processed>=limit){
       auto ms=std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now()-start).count();
       std::cout<<"{\"status\":\"BENCHMARK_ONLY_INCOMPLETE\",\"nodes\":"<<processed<<",\"leaves\":"<<leaves<<",\"frontier\":"<<stack.size()<<",\"elapsed_ms\":"<<ms<<"}"<<std::endl;return 0;
     }
   }
   need(stack.empty(),"missing child or unfinished root cover");
   need(leaves==cert.leaves&&processed==cert.nodes&&processed==2*leaves-1,"replayed count mismatch");
   need(depth==cert.depth,"replayed depth mismatch");
   auto ms=std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now()-start).count();
   std::cout<<"{\"status\":\"EXACT_REPLAY_PASSED\",\"kind\":\"low_floor\",\"nodes\":"<<processed
     <<",\"leaves\":"<<leaves<<",\"maximum_depth\":"<<depth<<",\"scale\":"<<SCALE
     <<",\"minimum_exact_reserve\":\""<<least<<"/"<<SCALE<<"\",\"elapsed_ms\":"<<ms
     <<",\"arithmetic\":\"48-bit directed dyadics, checked signed __int128 arithmetic, integer-only radicals, exact rational root cells\"}"<<std::endl;
   return 0;
 }catch(const std::exception&e){std::cerr<<"REJECTED: "<<e.what()<<"\n";return 1;}
}
