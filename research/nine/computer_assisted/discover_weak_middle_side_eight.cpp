// Untrusted floating interval discovery. Every leaf needs separate exact replay.
#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
using ld=long double;
struct I {
    ld lo,hi;
    I(ld a=0):lo(a),hi(a){}
    I(ld a,ld b):lo(a),hi(b){}
};
I operator+(I a,I b){return {a.lo+b.lo,a.hi+b.hi};}
I operator-(I a){return {-a.hi,-a.lo};}
I operator-(I a,I b){return a+-b;}
I operator*(I a,I b){
    ld p[]={a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi};
    return {*min_element(p,p+4),*max_element(p,p+4)};
}
I operator/(I a,ld b){return {a.lo/b,a.hi/b};}
I sq(I a){return {(a.lo<=0&&a.hi>=0)?0:min(a.lo*a.lo,a.hi*a.hi),max(a.lo*a.lo,a.hi*a.hi)};}
I ab(I a){return {max({0.L,a.lo,-a.hi}),max(abs(a.lo),abs(a.hi))};}
I rec(I a){return {1/a.hi,1/a.lo};}
I rt(I a){return {sqrtl(max(0.L,a.lo)),sqrtl(max(0.L,a.hi))};}
const ld Q=1105.L/256,L=29.L/60,U=13.L/12,RHO=91.L/60;
const ld A=503.L/480,K=80669.L/93000,CSTAR=4421.L/12000;
const ld NEG=-1000,POS=1000;
struct S{I a,b,h,k,g;};

S shape(I t){
    auto at=[](ld z){ld a=1/sqrtl(1+z*z),b=z*a;return array<ld,4>{a,b,(a+b)/2,(a-b)/2};};
    auto lo=at(t.lo),hi=at(t.hi);
    S s{{hi[0],lo[0]},{lo[1],hi[1]},{lo[2],hi[2]},{hi[3],lo[3]},I()};
    s.g=rec(4*s.h);return s;
}
S shape_h(I h){
    ld kl=sqrtl(.5L-h.lo*h.lo),kh=sqrtl(.5L-h.hi*h.hi);
    return {{h.hi+kh,h.lo+kl},{h.lo-kl,h.hi-kh},h,{kh,kl},rec(4*h)};
}
I eta(I h){
    auto v=[](ld z){return (z-.5L)*(z-.5L)/z;};
    return {v(h.lo),v(h.hi)};
}
ld floor_main(I h){
    ld z=h.hi;
    return -2*z/3+max(0.L,min((z-.5L)/6,(.54L-z)/3))+.0025L;
}
ld divlower(I n,I d){
    if(d.hi==0)return POS;
    if(n.lo>=0)return n.lo/d.hi;
    if(d.lo==0)return NEG;
    return n.lo/d.lo;
}
ld support(S s,int ss,S t,int st){
    I co=s.a*t.a+(ss*st)*s.b*t.b;
    I si=ss*s.b*t.a-st*s.a*t.b;
    return max(1.L,(1+ab(co).lo+ab(si).lo)/2);
}
ld psiupper(I t){
    S lo=shape(I(t.lo)),hi=shape(I(t.hi));
    ld lin=max((lo.a/2+(19.L/54)*lo.b).hi,(hi.a/2+(19.L/54)*hi.b).hi);
    if(t.lo<=19.L/27&&t.hi>=19.L/27)lin=max(lin,sqrtl(1090.L)/54);
    return min(lin,(1-hi.a/2+hi.b/18).hi);
}
ld corner(S s,I x,int sign){
    array<I,4> dx{s.h,sign*s.k,-s.h,-sign*s.k};
    array<I,4> dy{-sign*s.k,s.h,sign*s.k,-s.h};
    ld out=RHO;
    for(int j=0;j<4;j++){
        I rad=Q-sq(x+dx[j]);if(rad.hi<0)return NEG;
        out=min(out,sqrtl(rad.hi)-dy[j].lo);
    }
    return out;
}
ld clear_main(S s,int ss,S m,int sm,I d){
    ld sig=support(s,ss,m,sm),D=max(abs(d.lo),abs(d.hi));
    I delta=m.g-I(D);
    ld reach=min({s.h.lo,divlower(.5L+delta*s.b,s.a),divlower(.5L+delta*s.a,s.b)});
    ld own=POS;
    array<pair<I,I>,4> axes{{{sm*m.a,m.b},{-sm*m.b,m.a},{ss*s.a,s.b},{-ss*s.b,s.a}}};
    for(auto n:axes)if(n.second.hi>0)own=min(own,divlower(I(sig)-n.first*d,n.second));
    ld disk=sqrtl(max(0.L,sig*sig-D*D));
    return max({m.g.lo+reach,own,disk});
}
ld endpoint(S s,int sign,I x,ld base,ld c){
    ld edge=min(A,RHO-c);if(x.lo+s.h.lo<=edge)return base;
    I delta=x-I(edge);
    auto reach=[&](int q){return min(s.h.lo,q>0?divlower(.5L+delta*s.b,s.a):divlower(.5L+delta*s.a,s.b));};
    ld wp=c+reach(sign),wm=c+reach(-sign);
    return base+wm>0?max(base,wp):base;
}
struct Owner{I nx,mag;int sign;};
vector<pair<ld,ld>> ranges(S s,int ss,S t,int st,I d,ld lo,ld hi,bool first){
    vector<pair<ld,ld>> out;if(lo>hi)return out;
    ld sig=support(s,ss,t,st);
    array<Owner,4> axes{{{s.a,s.b,ss},{s.b,s.a,-ss},{t.a,t.b,st},{t.b,t.a,-st}}};
    for(auto n:axes){
        ld low=-d.hi,high=d.hi;I num=I(sig)-n.nx*d;
        if(n.mag.hi==0){if(num.lo>0)continue;}
        else if(n.sign>0)low=max(low,divlower(num,n.mag));
        else high=min(high,-divlower(num,n.mag));
        if(low>high)continue;
        out.push_back(first?make_pair(lo-high,hi-low):make_pair(lo+low,hi+high));
    }
    return out;
}

using Box=array<I,9>;
ld margin(Box box,bool lowright){
    auto [tl,tp,tr,Z,x,X,c0,hb,hc]=box;
    S left=shape(tl),p=shape(tp),right=shape(tr),bm=shape_h(hb),cm=shape_h(hc);
    I eb=eta(hb),ec=eta(hc),V=eb+ec;
    ld psL=psiupper(tl),psR=psiupper(tr);
    ld hmax=min(8.L/15,1/(4*c0.lo)),jlo=hmax+sqrtl(.5L-hmax*hmax);
    ld a0max=min(61.L/60,sqrtl(Q-(1-c0.hi)*(1-c0.hi))-jlo);
    ld a0min=(157.L/184+V+(27.L/92)*(X-I(psR))).lo;
    ld vcap=min({1.L/30,(27.L/92)*(451.L/810-Z.lo+psL),
        (27.L/92)*(451.L/810-X.lo+psR),(27.L/92)*(1-Z.lo-X.lo+psL+psR)});
    I dl=x+Z,dr=X-x;
    ld basic=min({vcap-V.lo,a0max-a0min,(c0-CSTAR-(32.L/9)*V).hi,
        (dl-left.g-p.g).hi,(dr-p.g-right.g).hi,(left.h+p.h-dl).hi,(p.h+right.h-dr).hi});
    if(basic<0)return basic;
    ld c3=max((CSTAR+(32.L/9)*V).lo,(K-c0+(32.L/9)*V).lo);
    ld arc=4-73.L/30000+V.lo-sqrtl(Q-(1-c0.hi)*(1-c0.hi));
    ld rad=Q-arc*arc;if(rad<0)return rad;
    c3=max(c3,1-sqrtl(rad));
    ld a3min=(157.L/184+V+(27.L/92)*(Z-I(psL))).lo;
    rad=Q-(a3min+29927.L/30000)*(a3min+29927.L/30000);if(rad<0)return rad;
    c3=max(c3,1-sqrtl(rad));
    ld blo=(hb-I(a0max)).lo,bhi=(1.L/60-bm.g-ec).hi;
    ld clo=(cm.g+eb-1.L/60).lo,chi=61.L/60-hc.lo;
    ld dmain=min(chi-blo,(hb+hc).hi);
    basic=min({basic,.5L-c3,bhi-blo,chi-clo,dmain-(bm.g+cm.g).lo});
    if(basic<0)return basic;
    ld bo=(bm.g+ec-199.L/120+(32.L/9)*V).lo;
    ld co=(cm.g+eb-199.L/120+(32.L/9)*V).lo;
    ld by=max({floor_main(hb),bo,c0.lo-121.L/60-bhi});
    ld cy=max(co,c3+clo-121.L/60);
    I bx(blo,bhi),cx(clo,chi);ld answer=NEG;
    for(int sb:{-1,1})for(int sc:{-1,1}){
        ld sig=support(bm,sb,cm,sc);
        array<pair<I,I>,4> axes{{{bm.a,sb*bm.b},{bm.b,-sb*bm.a},{cm.a,sc*cm.b},{cm.b,-sc*cm.a}}};
        for(int sp:{-1,1}){
            ld cbp=clear_main(p,sp,bm,sb,x-bx),ccp=clear_main(p,sp,cm,sc,x-cx);
            ld pl=max(by+cbp,cy+ccp),ph=corner(p,x,sp);
            if(!lowright)ph=min(ph,p.h.hi+.1L);
            if(ph<pl){answer=max(answer,ph-pl);continue;}
            for(int sl:{-1,1}){
                ld cbl=clear_main(left,sl,bm,sb,-Z-bx);
                ld ll=endpoint(left,-sl,Z,by+cbl,c0.lo),lh=corner(left,Z,-sl);
                if(lh<ll){answer=max(answer,lh-ll);continue;}
                auto lr=ranges(left,sl,p,sp,dl,ll,lh,false);
                for(int sr:{-1,1}){
                    ld ccr=clear_main(right,sr,cm,sc,X-cx);
                    ld rl=endpoint(right,sr,X,max(-.45L,cy+ccr),c3),rh=corner(right,X,sr);
                    if(lowright)rh=min(rh,.6L);
                    if(rh<rl){answer=max(answer,rh-rl);continue;}
                    auto rr=ranges(p,sp,right,sr,dr,rl,rh,true);ld best=NEG;
                    for(auto p0:lr)for(auto p1:rr){
                        ld pylo=max({pl,p0.first,p1.first}),pyhi=min({ph,p0.second,p1.second});
                        ld Bhi=min({pyhi-cbp,lh-cbl,-bo}),Chi=min({pyhi-ccp,rh-ccr,-co});
                        ld elo=max(-dmain,cy-Bhi),ehi=min(dmain,Chi-by);
                        ld overlap=min({pyhi-pylo,ehi-elo,Bhi-by,Chi-cy});
                        if(overlap>=0){
                            I E(elo,ehi);ld sep=NEG;
                            for(auto n:axes)sep=max(sep,(n.first*I(dmain)+n.second*E).hi-sig);
                            overlap=min(overlap,sep);
                        }
                        best=max(best,overlap);
                    }
                    answer=max(answer,min({ph-pl,lh-ll,rh-rl,best}));
                }
            }
        }
    }
    return min(basic,answer);
}

struct Task{Box box;int depth;};
Box root(){return {{{0,1},{0,1},{0,1},{L,U},{-23.L/60,23.L/60},{L,U},{CSTAR,.5L},{.5L,.65L},{.5L,.65L}}};}

int main(int argc,char**argv){
    string kind=argc>1?argv[1]:"low_right";bool lowright=kind=="low_right";
    long long limit=argc>2?stoll(argv[2]):1000000;
    string path=argc>3?argv[3]:"weak_middle_side_eight_"+kind+"_candidate.json";
    vector<Task> todo{{root(),0}};vector<int> events;long long leaves=0;int depth=0;
    ld least=POS;auto begin=chrono::steady_clock::now();
    const array<ld,9> weights{1,1,1,1.4L,1.4L,1.4L,4,4,4};
    while(!todo.empty()&&(long long)events.size()<limit){
        Task cur=todo.back();todo.pop_back();depth=max(depth,cur.depth);
        ld v=margin(cur.box,lowright);
        if(v< -1e-8L){events.push_back(9);leaves++;least=min(least,-v);}
        else{
            int axis=0;ld width=-1;
            for(int j=0;j<9;j++){
                ld w=(cur.box[j].hi-cur.box[j].lo)*weights[j];
                if(w>width){width=w;axis=j;}
            }
            if(cur.depth>=95){todo.push_back(cur);break;}
            ld mid=(cur.box[axis].lo+cur.box[axis].hi)/2;
            Task a=cur,b=cur;a.depth++;b.depth++;a.box[axis].hi=mid;b.box[axis].lo=mid;
            events.push_back(axis);todo.push_back(b);todo.push_back(a);
        }
        if(events.size()%10000==0){
            double sec=chrono::duration<double>(chrono::steady_clock::now()-begin).count();
            cerr<<"nodes="<<events.size()<<" leaves="<<leaves<<" pending="<<todo.size()<<" depth="<<depth<<" seconds="<<sec<<"\n";
        }
    }
    ofstream out(path);out<<setprecision(21);
    out<<"{\"status\":\""<<(todo.empty()?"COMPLETE_DISCOVERY":"INCOMPLETE_DISCOVERY")<<"\",\"kind\":\""<<kind<<"\",\"events\":[";
    for(size_t j=0;j<events.size();j++){if(j)out<<',';out<<events[j];}
    out<<"],\"nodes\":"<<events.size()<<",\"leaves\":"<<leaves<<",\"max_depth\":"<<depth<<",\"least_float_reserve\":"<<least<<",\"frontier\":[";
    for(size_t i=0;i<todo.size();i++){
        if(i)out<<',';out<<"{\"depth\":"<<todo[i].depth<<",\"box\":[";
        for(int j=0;j<9;j++){if(j)out<<',';out<<'['<<todo[i].box[j].lo<<','<<todo[i].box[j].hi<<']';}
        out<<"]}";
    }
    double sec=chrono::duration<double>(chrono::steady_clock::now()-begin).count();
    out<<"],\"seconds\":"<<sec<<"}\n";
    cout<<"status="<<(todo.empty()?"COMPLETE_DISCOVERY":"INCOMPLETE_DISCOVERY")<<" nodes="<<events.size()<<" leaves="<<leaves<<" pending="<<todo.size()<<" depth="<<depth<<" seconds="<<sec<<"\n";
}
