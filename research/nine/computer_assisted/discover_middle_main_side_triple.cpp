// UNTRUSTED FLOATING DISCOVERY ONLY. Every accepted row requires exact replay.
#include <algorithm>
#include <array>
#include <cmath>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <string>
#include <vector>
using namespace std;
using ld=long double;
struct I {ld lo,hi; I(ld a=0):lo(a),hi(a){} I(ld a,ld b):lo(a),hi(b){} };
I operator+(I a,I b){return {a.lo+b.lo,a.hi+b.hi};} I operator-(I a){return {-a.hi,-a.lo};} I operator-(I a,I b){return a+-b;}
I operator*(I a,I b){ld p[]={a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi};return {*min_element(p,p+4),*max_element(p,p+4)};}
I operator/(I a,ld b){return {a.lo/b,a.hi/b};}
I sq(I a){return {(a.lo<=0&&a.hi>=0)?0:min(a.lo*a.lo,a.hi*a.hi),max(a.lo*a.lo,a.hi*a.hi)};}
I ab(I a){return {max({0.L,a.lo,-a.hi}),max(abs(a.lo),abs(a.hi))};}
I rec(I a){return {1/a.hi,1/a.lo};}
const ld Q=1105.L/256,g=15.L/31,A=503.L/480,l=29.L/60,u=13.L/12,rho=91.L/60;
struct S {I a,b,h,k,g;};
S shape(I t){auto at=[](ld z){ld a=1/sqrtl(1+z*z),b=z*a;return array<ld,4>{a,b,(a+b)/2,(a-b)/2};};auto lo=at(t.lo),hi=at(t.hi);S s{{hi[0],lo[0]},{lo[1],hi[1]},{lo[2],hi[2]},{hi[3],lo[3]},I()};s.g=rec(s.h*I(4));return s;}
ld divlower(I n,I den){if(den.hi==0)return 1000;if(n.lo>=0)return n.lo/den.hi;if(den.lo==0)return -1000;return n.lo/den.lo;}
ld upper(S s,I X,int sign){array<I,4>dx{s.h,I(sign)*s.k,-s.h,I(-sign)*s.k};array<I,4>dy{I(-sign)*s.k,s.h,I(sign)*s.k,-s.h};ld out=rho;for(int j=0;j<4;j++){I rad=I(Q)-sq(X+dx[j]);if(rad.hi<0)return -1000;out=min(out,sqrtl(max(0.L,rad.hi))-dy[j].lo);}return out;}
ld prox(S s,int sign,ld D,I delta,bool generic=false){ld reach=s.h.lo;if(generic||sign<0)reach=min(reach,divlower(I(.5)+delta*s.b,s.a));if(generic||sign>0)reach=min(reach,divlower(I(.5)+delta*s.a,s.b));ld sig=max(1.L,s.h.lo+12.L/25);return max(g+reach,sqrtl(max(0.L,sig*sig-D*D)));}
ld ep(S s,int sign,I X,ld base,ld c){ld edge=min(A,rho-c);if(X.lo+s.h.lo<=edge)return base;I delta=X-I(edge);auto reach=[&](int q){return min(s.h.lo,q>0?divlower(I(.5)+delta*s.b,s.a):divlower(I(.5)+delta*s.a,s.b));};ld wp=c+reach(sign),wm=c+reach(-sign);if(base+wm>0)return max(base,wp);return base;}
ld physical(S s,int ss,S t,int st,I D,ld elo,ld ehi){if(elo>ehi)return ehi-elo;I E{elo,ehi};I cos=s.a*t.a+I(ss*st)*s.b*t.b;I sin=I(ss)*s.b*t.a-I(st)*s.a*t.b;ld sigma=max(1.L,(1+ab(cos).lo+ab(sin).lo)/2);ld best=max({(s.a*D+I(ss)*s.b*E).hi,(s.b*D-I(ss)*s.a*E).hi,(t.a*D+I(st)*t.b*E).hi,(t.b*D-I(st)*t.a*E).hi});return best-sigma;}


struct Owner {I nx,mag;int sign;};
array<Owner,4> owners(S a,int sa,S b,int sb){return {{{a.a,a.b,sa},{a.b,a.a,-sa},{b.a,b.b,sb},{b.b,b.a,-sb}}};}
ld supportlower(S a,int sa,S b,int sb){I co=a.a*b.a+I(sa*sb)*a.b*b.b;I si=I(sa)*a.b*b.a-I(sb)*a.a*b.b;return max(1.L,(1+ab(co).lo+ab(si).lo)/2);}
ld gaplower(S a,int sa,S b,int sb,ld elo,ld ehi){
 if(elo>ehi)return 1000;I E(elo,ehi);ld sig=supportlower(a,sa,b,sb),bound=1000;
 for(auto n:owners(a,sa,b,sb)){I need=I(sig)-I(n.sign)*n.mag*E;
  ld candidate=n.nx.hi==0?(need.lo>0?1000:-1000):divlower(need,n.nx);
  bound=min(bound,candidate);
 }return bound;
}
ld jointowners(S L,int sl,S P,int sp,S R,int sr,I dl,I dr,I Z,I x,I X,ld pl,ld yp,ld ll,ld lh,ld rl,ld rh){
 ld elo=max(-dl.hi,pl-lh),ehi=min(dl.hi,yp-ll),flo=max(-dr.hi,rl-yp),fhi=min(dr.hi,rh-pl);
 if(elo>ehi||flo>fhi)return min(ehi-elo,fhi-flo);
 I E(elo,ehi),F(flo,fhi);auto aa=owners(L,sl,P,sp),bb=owners(P,sp,R,sr);
 ld suppL=supportlower(L,sl,P,sp),suppR=supportlower(P,sp,R,sr),out=-1000;
 for(int ia=0;ia<4;ia++)for(int ib=0;ib<4;ib++){auto a=aa[ia],b=bb[ib];I ny=I(a.sign)*a.mag,my=I(b.sign)*b.mag;
  ld ma=(a.nx*dl+ny*E).hi-suppL,mb=(b.nx*dr+my*F).hi-suppR,comb=1000;
  I ac=a.nx*b.nx,cb=b.nx*ny,ad=a.nx*my;
  I cross=ac*(Z+X)+(cb-ad)*I(pl,yp)-cb*I(a.sign>0?ll:lh)+ad*I(b.sign>0?rh:rl)-b.nx*I(suppL)-a.nx*I(suppR);
  ld horizontal=cross.hi;
  if(a.sign==b.sign){I al=I(suppL)-a.nx*dl+ny*I(a.sign>0?ll:lh);I ar=I(suppR)-b.nx*dr-my*I(b.sign>0?rh:rl);comb=-(b.mag*al+a.mag*ar).lo;ld yl=a.sign>0?ll:lh,yr=b.sign>0?rh:rl;
    I expanded=b.mag*I(suppL)+a.mag*I(suppR)-b.mag*a.nx*Z-a.mag*b.nx*X+(a.mag*b.nx-b.mag*a.nx)*x+I(a.sign)*a.mag*b.mag*I(yl-yr);
    comb=min(comb,-expanded.lo);
    if(ia==ib+2 && ib<2)comb=min(comb,(a.nx*(Z+X)+ny*I(yr-yl)).hi-suppL-suppR);
  }
  out=max(out,min({ma,mb,comb,horizontal}));
 }
 return out;
}
ld psiupper(S s){
 ld pl=max(.5L*s.a.hi+(19.L/54)*s.b.lo,.5L*s.a.lo+(19.L/54)*s.b.hi);
 if(s.b.lo/s.a.hi<=19.L/27 && s.b.hi/s.a.lo>=19.L/27)pl=max(pl,sqrtl(1090.L)/54);
 return min(pl,1-.5L*s.a.lo+s.b.hi/18);
}
ld lfcommon(S L,S P,S R,I Z,I x,I X,I cL,S L0,S P0,I tP,int pass=0){
 I dl=x+Z,dr=X-x;ld psiL=psiupper(L),psiR=psiupper(R);
 ld eCap=min({1.L/60,(27.L/184)*(451.L/810-Z.lo+psiL),(27.L/184)*(451.L/810-X.lo+psiR),(27.L/184)*(1-Z.lo-X.lo+psiL+psiR)});
 ld aLeft=max(59.L/60,157.L/184+(27.L/92)*(X.lo-psiR));ld emax=min(8.L/15,1/(4*cL.lo));ld jLeft=emax+sqrtl(.5L-emax*emax);ld A0max=min(61.L/60,sqrtl(Q-(1-cL.hi)*(1-cL.hi))-jLeft);eCap=min(eCap,(A0max-aLeft)/2);if(eCap< -1e-8L)return eCap;ld out=-1000,unionlo=1000,unionhi=-1000;ld dP=x.hi+A0max-.5L;
 ld sigP=max(1.L,P.h.lo+12.L/25),diskP=sqrtl(max(0.L,sigP*sigP-dP*dP));
 for(int sp:{-1,1}){
  I deltaP=I(1-A0max)-x;
  ld reachP=min(P.h.lo,sp<0?divlower(I(.5)+deltaP*P.b,P.a):divlower(I(.5)+deltaP*P.a,P.b));
  ld axisAllowed=sp<0?(I((11.L/25))+tP*(P.k-deltaP)).hi:(11.L/25)-divlower(P.k+deltaP,tP);ld allowed=min(P.h.hi+(11.L/25)-reachP,axisAllowed);if(allowed<=0){out=max(out,allowed);continue;}ld need=max(0.L,1/(4*allowed)-.5L),gain=2*need*need/(1+2*need),yp=P.h.hi+.1L;deltaP=deltaP+I(gain);reachP=min(P.h.lo,sp<0?divlower(I(.5)+deltaP*P.b,P.a):divlower(I(.5)+deltaP*P.a,P.b));
  ld cR=max(4421.L/12000,80669.L/93000-cL.hi+(64.L/9)*need);ld aRight=max(59.L/60,157.L/184+(27.L/92)*(Z.lo-psiL))+2*need;ld rradius=Q-(aRight+29927.L/30000)*(aRight+29927.L/30000);cR=rradius<0?1000:max(cR,1-sqrtl(rradius));
  ld arc=4-73.L/30000+2*need-sqrtl(Q-(1-cL.hi)*(1-cL.hi));ld rad=Q-arc*arc;
  cR=rad<0?1000:max(cR,1-sqrtl(rad));
  for(int sr:{-1,1}){
   ld rh=upper(R,X,sr);I de=X-I(A);
   ld rr=min(R.h.lo,sr>0?divlower(I(.5)+de*R.b,R.a):divlower(I(.5)+de*R.a,R.b));
   bool overlap=X.lo+R.h.lo>A;
   ld eu=eCap;if(overlap)eu=min(eu,(9.L/64)*(rh-rr-80669.L/93000+cL.hi));
   if(eu< -1e-8L){out=max(out,eu);continue;}ld emargin=eu;eu=max(0.L,eu);
   ld gm=1/(2+4*eu);I xx=x;
   ld xmin=sp<0?(tP.hi==0?1000:1-A0max+gain-P.k.hi+(gm-(11.L/25))/tP.hi):1-A0max+gain+P.k.lo+tP.lo*(gm-(11.L/25));
   xx.lo=max(xx.lo,xmin);if(xx.lo>xx.hi){out=max(out,xx.hi-xx.lo);continue;}
   I dl=xx+Z,dr=X-xx;
   ld hm=.5L+eu,km=sqrtl(.5L-hm*hm),am=hm+km,bm=hm-km;ld sigP2=max(1.L,.5L+P0.b.lo*hm+P0.a.lo*km),dp=dP-need;ld pl=-17.L/50+max(gm+reachP,sqrtl(max(0.L,sigP2*sigP2-dp*dp)));
   ld rl=overlap?max(.6L,cR+rr):.6L;
   ld elo=max(-dr.hi,rl-yp),ehi=min(dr.hi,rh-pl);
   ld right=min({rh-rl,ehi-elo,physical(P,sp,R,sr,dr,elo,ehi)});
   ld mainAxis=sp<0?(tP*(P.k-deltaP)).hi-(gm-(11.L/25)):(-P.k-deltaP-tP*I(gm-(11.L/25))).hi;ld basic=min({yp-pl,right,mainAxis,emargin-need,1.L/60-need,.5L-cR});
   if(basic< -1e-9L){out=max(out,basic);continue;}
   ld left=-1000;
   for(int sl:{-1,1}){
    I delta(min(59.L/60-Z.hi,Z.lo+1-A0max)+gain);ld reach=L.h.lo;
    if(Z.lo<8.L/15||-sl<0)reach=min(reach,divlower(I(.5)+delta*L.b,L.a));
    if(Z.lo<8.L/15||-sl>0)reach=min(reach,divlower(I(.5)+delta*L.a,L.b));
    ld d=max(Z.hi-l,A0max-.5L-Z.lo)-need,sig=max(1.L,.5L+L0.b.lo*hm+L0.a.lo*km);
    ld base=-17.L/50+max(gm+reach,sqrtl(max(0.L,sig*sig-d*d)));
    ld ll=ep(L,-sl,Z,base,cL.lo),lh=upper(L,Z,-sl);
    ld lo=max(-dl.hi,pl-lh),hi=min(dl.hi,yp-ll);
    ld ql=gaplower(L,sl,P,sp,lo,hi),qr=gaplower(P,sp,R,sr,max(-dr.hi,rl-yp),min(dr.hi,rh-pl));
    I xxx(max(xx.lo,ql-Z.hi),min(xx.hi,X.hi-qr));
    if(xxx.lo>xxx.hi){left=max(left,xxx.hi-xxx.lo);continue;}
    I ddl=xxx+Z,ddr=X-xxx;lo=max(-ddl.hi,pl-lh);hi=min(ddl.hi,yp-ll);
    ld lm=min({lh-ll,hi-lo,physical(L,sl,P,sp,ddl,lo,hi),physical(P,sp,R,sr,ddr,max(-ddr.hi,rl-yp),min(ddr.hi,rh-pl))});
    if(lm>=-1e-9L)lm=min(lm,jointowners(L,sl,P,sp,R,sr,ddl,ddr,Z,xxx,X,pl,yp,ll,lh,rl,rh));
    left=max(left,lm);
    ld chart=min({yp-pl,lm,right,mainAxis,emargin-need,1.L/60-need,.5L-cR});
    if(chart>=-1e-9L){unionlo=min(unionlo,xxx.lo);unionhi=max(unionhi,xxx.hi);}
   }
   out=max(out,min({yp-pl,left,right,mainAxis,emargin-need,1.L/60-need,.5L-cR}));
  }
 }
 if(pass<3 && out>=-1e-9L && unionlo<=unionhi && (unionlo>x.lo+1e-15L||unionhi<x.hi-1e-15L))
  return lfcommon(L,P,R,Z,I(max(x.lo,unionlo),min(x.hi,unionhi)),X,cL,L0,P0,tP,pass+1);
 return out;
}
using Box=array<I,7>;
vector<ld> values(Box box,bool lowright){I Z=box[3],x=box[4],X=box[5],w=box[6];S L=shape(box[0]),P=shape(box[1]),R=shape(box[2]);
 if(!lowright){ld psL=psiupper(L),psR=psiupper(R);ld hm=min(8.L/15,1/(4*w.lo)),jl=hm+sqrtl(.5L-hm*hm),a0=min(61.L/60,sqrtl(Q-(1-w.hi)*(1-w.hi))-jl);
  for(int sweep=0;sweep<3;sweep++){
   x.lo=max({x.lo,-.2L,23.L/150-P.g.hi,P.g.lo+L.g.lo-Z.hi,X.lo-P.h.hi-R.h.hi});
   x.hi=min({x.hi,L.h.hi+P.h.hi-Z.lo,X.hi-P.g.lo-R.g.lo});
   Z.lo=max(Z.lo,L.g.lo+P.g.lo-x.hi);X.lo=max(X.lo,x.lo+P.g.lo+R.g.lo);
   Z.hi=min({Z.hi,L.h.hi+P.h.hi-x.lo,451.L/810+psL,1+psL+psR-X.lo});
   X.hi=min({X.hi,x.hi+P.h.hi+R.h.hi,451.L/810+psR,1+psL+psR-Z.lo,psR+(92.L/27)*(a0-157.L/184)});
   if(x.lo>x.hi||Z.lo>Z.hi||X.lo>X.hi)return {1000,1000,1000,1000,1000,-1};
  }
 }
 I dl=x+Z,dr=X-x;vector<ld> rows; if(!lowright)rows.push_back((x+P.g-I(23.L/150)).hi);rows.push_back((dl-P.g-L.g).hi);rows.push_back((dr-P.g-R.g).hi);rows.push_back((L.h+P.h-dl).hi);rows.push_back((P.h+R.h-dr).hi);for(ld v:rows)if(v< -1e-9L)return rows;
 if(!lowright){rows.push_back(lfcommon(L,P,R,Z,x,X,w,shape(I(box[0].lo)),shape(I(box[1].lo)),box[1]));return rows;} ld common=-1000;for(int sp:{-1,1}){ld need=0; if(!lowright){I delta=I(-1.L/60)-x; ld reach=P.h.lo; reach=min(reach,sp<0?divlower(I(.5)+delta*P.b,P.a):divlower(I(.5)+delta*P.a,P.b));need=max(0.L,.05L+reach-P.h.hi);} ld cR=max(4421.L/12000,80669.L/93000-w.hi+(64.L/9)*need);ld hor=4-73.L/30000+2*need;ld arc=hor-sqrtl(Q-(1-w.hi)*(1-w.hi));ld crad=Q-arc*arc;if(crad>=0)cR=max(cR,1-sqrtl(crad));else cR=1000;ld yp=lowright?upper(P,x,sp):P.h.hi+.1L;ld pl=-.35L+prox(P,sp,x.hi+31.L/60,I(-1.L/60)-x);ld left=-1000,right=-1000;for(int sl:{-1,1}){ld D=max(Z.hi-l,31.L/60-Z.lo);ld cl=-.35L+prox(L,-sl,D,I(min(59.L/60-Z.hi,Z.lo-1.L/60)),Z.lo<8.L/15);ld ll=ep(L,-sl,Z,cl,w.lo);ld lh=upper(L,Z,-sl);ld elo=max(-dl.hi,pl-lh),ehi=min(dl.hi,yp-ll);ld m=min({lh-ll,ehi-elo,physical(L,sl,P,sp,dl,elo,ehi)});left=max(left,m);}for(int sr:{-1,1}){ld rl=ep(R,sr,X,-113.L/600,cR);ld rh=upper(R,X,sr);if(lowright)rh=min(rh,.6L);ld elo=max(-dr.hi,rl-yp),ehi=min(dr.hi,rh-pl);ld m=min({rh-rl,ehi-elo,physical(P,sp,R,sr,dr,elo,ehi)});right=max(right,m);}ld m=min({yp-pl,left,right,.5L-cR});if(!lowright)m=min({m,1.L/60-need,.5L-(80669.L/93000-w.hi+(64.L/9)*need)});common=max(common,m);}rows.push_back(common);return rows;}
struct Node {Box b;int depth;};
int main(int argc,char**argv){bool lr=argc>1&&string(argv[1])=="low_right";string outfile=argc>2?argv[2]:(lr?"middle_main_low_right_candidate.json":"middle_main_low_floor_candidate.json");long long limit=argc>3?stoll(argv[3]):5000000;Box root={I(0,1),I(lr?0:1.L/27,1),I(0,1),I(l,u),I(-23.L/60,23.L/60),I(l,lr?49.L/80:u),I(4421.L/12000,.5L)};array<ld,7> width;for(int j=0;j<7;j++)width[j]=lr?1:root[j].hi-root[j].lo;vector<Node>stack{{root,0}};vector<int>ev;long long leaves=0;int maxdep=0;ld least=1000;while(!stack.empty()&&(long long)ev.size()<limit){auto node=stack.back();stack.pop_back();maxdep=max(maxdep,node.depth);auto rows=values(node.b,lr);int rule=-1;for(int j=0;j<(int)rows.size();j++)if(rows[j]<-1e-9L&&(rule<0||rows[j]<rows[rule]))rule=j;if(rule>=0){ev.push_back(-rule-1);leaves++;least=min(least,-rows[rule]);}else{if(!lr && node.depth>=21){Box pp;for(int q=0;q<7;q++)pp[q]=I((node.b[q].lo+node.b[q].hi)/2);auto vv=values(pp,lr);ld ff=*min_element(vv.begin(),vv.end());if(ff>=-1e-12L){cerr<<"POSSIBLE RELAXATION POINT depth "<<node.depth<<" min "<<setprecision(20)<<ff<<"\n";for(int q=0;q<7;q++)cerr<<pp[q].lo<<" ";cerr<<"\n";for(ld v:vv)cerr<<v<<" ";cerr<<"\n";return 3;}}int axis=0;ld score=-1;for(int j=0;j<7;j++){ld z=(node.b[j].hi-node.b[j].lo)/width[j];if(z>score){score=z;axis=j;}}if(false){ld best=numeric_limits<ld>::infinity();int choice=axis;for(int q=0;q<7;q++){ld wid=node.b[q].hi-node.b[q].lo;if(wid<score/16)continue;ld midq=(node.b[q].lo+node.b[q].hi)/2;Box aa=node.b,bb=node.b;aa[q].hi=midq;bb[q].lo=midq;auto va=values(aa,lr),vb=values(bb,lr);ld fa=*min_element(va.begin(),va.end()),fb=*min_element(vb.begin(),vb.end());ld sc=max(0.L,fa)+max(0.L,fb);if(sc<best-1e-15L){best=sc;choice=q;}}axis=choice;}ld mid=(node.b[axis].lo+node.b[axis].hi)/2;if(mid==node.b[axis].lo||mid==node.b[axis].hi||node.depth>90){cerr<<"UNRESOLVED box depth "<<node.depth<<"\n"; Box midbox; for(int q=0;q<7;q++){ld v=(node.b[q].lo+node.b[q].hi)/2;midbox[q]=I(v);cerr<<setprecision(20)<<node.b[q].lo<<" "<<node.b[q].hi<<" mid "<<v<<"\n";} auto vv=values(midbox,lr);for(ld v:vv)cerr<<"margin "<<setprecision(20)<<v<<"\n";break;}Box a=node.b,b=node.b;a[axis].hi=mid;b[axis].lo=mid;ev.push_back(axis);stack.push_back({b,node.depth+1});stack.push_back({a,node.depth+1});}if(ev.size()%100000==0)cerr<<"nodes "<<ev.size()<<" leaves "<<leaves<<" frontier "<<stack.size()<<" depth "<<maxdep<<"\n";if(ev.size()%500000==0){ld pv=0;for(auto nd:stack){ld vv=1;for(int q=0;q<7;q++)vv*=(nd.b[q].hi-nd.b[q].lo)/(root[q].hi-root[q].lo);pv+=vv;}cerr<<"pending_volume "<<setprecision(10)<<pv<<" active_mid ";for(int q=0;q<7;q++)cerr<<"["<<node.b[q].lo<<","<<node.b[q].hi<<"] ";cerr<<"\n";}}
 if(!stack.empty()){ld pending=0;for(auto nd:stack){ld vv=1;for(int q=0;q<7;q++)vv*=(nd.b[q].hi-nd.b[q].lo)/(root[q].hi-root[q].lo);pending+=vv;}cerr<<"PENDING_VOLUME "<<setprecision(20)<<pending<<"\n";cerr<<"INCOMPLETE nodes "<<ev.size()<<" leaves "<<leaves<<" frontier "<<stack.size()<<" depth "<<maxdep<<"\n";return 2;}
 ofstream out(outfile);out<<"{\n\"status\":\"COMPLETE_UNTRUSTED_DISCOVERY\",\n\"kind\":\""<<(lr?"low_right":"low_floor")<<"\",\n\"nodes\":"<<ev.size()<<",\n\"leaves\":"<<leaves<<",\n\"max_depth\":"<<maxdep<<",\n\"events\":[";for(size_t j=0;j<ev.size();j++){if(j)out<<',';out<<ev[j];}out<<"]\n}\n";cerr<<"COMPLETE nodes "<<ev.size()<<" leaves "<<leaves<<" depth "<<maxdep<<" reserve "<<setprecision(18)<<least<<"\n";}
