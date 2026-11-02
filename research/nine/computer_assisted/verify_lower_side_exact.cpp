// Independent exact replay of the signed lower-side original-square exclusion.
// The arithmetic kernel is retained from the previously audited independent checker.
// The new physical formulas and finite root family are reconstructed below.
// All arithmetic below is integral. No producer code or floating kernel
// is included. The JSON wrapper supplies only the preorder integer tags.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

using i64=std::int64_t;
using i128=__int128_t;
using u128=__uint128_t;
constexpr int BITS=48;
constexpr i64 SCALE=i64(1)<<BITS;

void need(bool value,const char* message){if(!value)throw std::runtime_error(message);}
i64 narrow(i128 value){
    need(value>std::numeric_limits<i64>::min()&&value<=std::numeric_limits<i64>::max(),"integer range exceeded");
    return static_cast<i64>(value);
}
i128 floor_div(i128 n,i128 d){need(d>0,"nonpositive divisor");i128 q=n/d,r=n%d;return q-(r<0);}
i128 ceil_div(i128 n,i128 d){need(d>0,"nonpositive divisor");i128 q=n/d,r=n%d;return q+(r>0);}
std::string integer_text(i128 n){
    if(n==0)return "0";bool neg=n<0;if(neg)n=-n;std::string s;
    while(n){s.push_back(char('0'+n%10));n/=10;}if(neg)s.push_back('-');std::reverse(s.begin(),s.end());return s;
}
u128 isqrt(u128 n){
    if(!n)return 0;
    unsigned bits=0;u128 q=n;while(q){++bits;q>>=1;}
    u128 x=u128(1)<<((bits+1)/2);
    for(;;){u128 y=(x+n/x)/2;if(y>=x)break;x=y;}
    need(x*x<=n&&(x+1)*(x+1)>n,"integer square-root enclosure failed");return x;
}

struct I{
    i64 lo,hi;
    static I raw(i64 l,i64 h){need(l<=h,"reversed interval");return {l,h};}
    static I rational(i128 n,i128 d=1){
        need(d>0,"nonpositive rational denominator");
        // Exact root coordinates have at most 70 dyadic subdivisions.
        // Their scaled numerators are below 2^126, so this multiplication
        // is safe in the signed 128-bit workspace.
        need(n>-(i128(1)<<78)&&n<(i128(1)<<78),"rational numerator range exceeded");
        i128 z=n*SCALE;return raw(narrow(floor_div(z,d)),narrow(ceil_div(z,d)));
    }
};
I q(i64 n,i64 d=1){return I::rational(n,d);}
I operator+(I a,I b){return I::raw(narrow(i128(a.lo)+b.lo),narrow(i128(a.hi)+b.hi));}
I operator-(I a){return I::raw(-a.hi,-a.lo);}
I operator-(I a,I b){return a+-b;}
I operator*(I a,I b){
    std::array<i128,4> z={i128(a.lo)*b.lo,i128(a.lo)*b.hi,i128(a.hi)*b.lo,i128(a.hi)*b.hi};
    auto m=std::minmax_element(z.begin(),z.end());
    return I::raw(narrow(floor_div(*m.first,SCALE)),narrow(ceil_div(*m.second,SCALE)));
}
I operator/(I a,I b){
    need(b.lo>0,"division interval reaches zero");
    std::array<i128,4> lows,highs;int n=0;
    for(i64 x:{a.lo,a.hi})for(i64 y:{b.lo,b.hi}){
        lows[n]=floor_div(i128(x)*SCALE,y);highs[n]=ceil_div(i128(x)*SCALE,y);++n;
    }
    return I::raw(narrow(*std::min_element(lows.begin(),lows.end())),narrow(*std::max_element(highs.begin(),highs.end())));
}
I operator+(I a,i64 b){return a+q(b);} I operator+(i64 a,I b){return q(a)+b;}
I operator-(I a,i64 b){return a-q(b);} I operator-(i64 a,I b){return q(a)-b;}
I operator*(I a,i64 b){return a*q(b);} I operator*(i64 a,I b){return q(a)*b;}
I operator/(I a,i64 b){return a/q(b);} I operator/(i64 a,I b){return q(a)/b;}
I square(I a){
    i128 low=a.lo<=0&&a.hi>=0?0:std::min(i128(a.lo)*a.lo,i128(a.hi)*a.hi);
    i128 high=std::max(i128(a.lo)*a.lo,i128(a.hi)*a.hi);
    return I::raw(narrow(floor_div(low,SCALE)),narrow(ceil_div(high,SCALE)));
}
I absolute(I a){return I::raw(a.lo<=0&&a.hi>=0?0:std::min(std::llabs(a.lo),std::llabs(a.hi)),std::max(std::llabs(a.lo),std::llabs(a.hi)));}
I radical(I a){
    need(a.lo>=0,"negative radicand");u128 l=u128(a.lo)*SCALE,h=u128(a.hi)*SCALE;
    u128 low=isqrt(l),high=isqrt(h);if(high*high<h)++high;
    return I::raw(narrow(i128(low)),narrow(i128(high)));
}
I minimum(std::initializer_list<I> args){
    need(args.size()>0,"empty minimum");i64 l=args.begin()->lo,h=args.begin()->hi;
    for(I a:args){l=std::min(l,a.lo);h=std::min(h,a.hi);}return I::raw(l,h);
}
I maximum(std::initializer_list<I> args){
    need(args.size()>0,"empty maximum");i64 l=args.begin()->lo,h=args.begin()->hi;
    for(I a:args){l=std::max(l,a.lo);h=std::max(h,a.hi);}return I::raw(l,h);
}
I intersection(I a,I b){return I::raw(std::max(a.lo,b.lo),std::min(a.hi,b.hi));}

// A coordinate is an exact dyadic subdivision of one fixed rational root.
// It is never reconstructed from a floating midpoint.
struct Coordinate{
    i64 base,width,den;
    u128 index=0;
    int level=0;
    std::pair<i128,i128> endpoint(bool upper)const{
        need(level<=70,"unsupported subdivision depth");i128 power=i128(1)<<level;
        return {base*power+width*i128(index+(upper?1:0)),den*power};
    }
    I point(bool upper)const{auto[n,d]=endpoint(upper);return I::rational(n,d);}
    I range()const{I a=point(false),b=point(true);return I::raw(a.lo,b.hi);}
    Coordinate child(bool right)const{Coordinate c=*this;c.index=2*index+(right?1:0);++c.level;return c;}
};
using Box=std::array<Coordinate,7>;
Box root(int id){
    return {{{0,1,1},{0,1,1},{0,1,1},{0,1129,3000},
             {id%2?36:19,id%2?29:17,60},{42,23,60},
             {(id/2)%2?57:50,(id/2)%2?5:7,100}}};
}
struct Frame{I a,b,h,k;};
Frame point_frame(I t){I a=1/radical(1+square(t)),b=t*a;return {a,b,(a+b)/2,(a-b)/2};}
Frame folded(const Coordinate& t){
    Frame left=point_frame(t.point(false)),right=point_frame(t.point(true));
    // a,k decrease; b,h increase on the entire closed folded interval.
    return {I::raw(right.a.lo,std::min(SCALE,left.a.hi)),
            I::raw(std::max(i64(0),left.b.lo),right.b.hi),
            I::raw(std::max(SCALE/2,left.h.lo),right.h.hi),
            I::raw(std::max(i64(0),right.k.lo),left.k.hi)};
}
struct Main{I a,b,g,eta,k;};
Main point_main(I h){I k=radical(q(1,2)-square(h)),g=1/(4*h);return {h+k,h-k,g,h+g-1,k};}
Main main_frame(const Coordinate& h){
    Main left=point_main(h.point(false)),right=point_main(h.point(true));
    return {I::raw(right.a.lo,std::min(SCALE,left.a.hi)),
            I::raw(std::max(i64(0),left.b.lo),right.b.hi),
            I::raw(right.g.lo,left.g.hi),
            I::raw(std::max(i64(0),left.eta.lo),right.eta.hi),
            I::raw(right.k.lo,left.k.hi)};
}
I curve(I t){Frame f=point_frame(t);return 6*f.b-q(27,2)*(1-f.a);}
I toll(const Coordinate& t,Frame f){
    I first=curve(t.point(false)),last=curve(t.point(true));
    i64 lower=std::min(first.lo,last.lo),upper=std::max(first.hi,last.hi);
    auto [ln,ld]=t.endpoint(false);auto [hn,hd]=t.endpoint(true);
    // d/dt Phi(t)=(6-(27/2)t)/(1+t^2)^(3/2).
    if(9*ln<=4*ld&&9*hn>=4*hd)upper=std::max(upper,(radical(q(873,4))-q(27,2)).hi);
    return maximum({2*f.b,I::raw(lower,upper)});
}
I upper_corners(I x,Frame f,int sign){
    I answer=q(3); // larger than every containing disk center height.
    // These are the four original signed vertices. Keeping their exact
    // h,k identities avoids treating correlated a+b as a wider interval.
    std::array<std::pair<I,I>,4> offsets=sign>0?
        std::array<std::pair<I,I>,4>{{{f.k,f.h},{f.h,-f.k},{-f.k,-f.h},{-f.h,f.k}}}:
        std::array<std::pair<I,I>,4>{{{f.h,f.k},{f.k,-f.h},{-f.h,-f.k},{-f.k,f.h}}};
    for(auto [dx,dy]:offsets){
        answer=minimum({answer,radical(q(1105,256)-square(x+dx))-dy});
    }
    return answer;
}

I support_point(I t,I u,int parity){
    Frame f=point_frame(t),g=point_frame(u);
    return (1+absolute(f.a*g.a+parity*f.b*g.b)+absolute(f.a*g.b-parity*f.b*g.a))/2;
}
I signed_support(I t,I u,int parity){
    I a,b;
    if(parity>0){
        a=support_point(I::raw(t.lo,t.lo),I::raw(u.hi,u.hi),parity);
        b=support_point(I::raw(t.hi,t.hi),I::raw(u.lo,u.lo),parity);
        i64 lo=std::min(a.lo,b.lo);
        if(t.lo<=u.hi&&u.lo<=t.hi)lo=SCALE;
        return I::raw(lo,std::max(a.hi,b.hi));
    }
    a=support_point(I::raw(t.lo,t.lo),I::raw(u.lo,u.lo),parity);
    b=support_point(I::raw(t.hi,t.hi),I::raw(u.hi,u.hi),parity);
    I cross=t+u+t*u;i64 hi=std::max(a.hi,b.hi);
    if(cross.lo<=SCALE&&cross.hi>=SCALE)hi=std::max(hi,((1+radical(q(2)))/2).hi);
    return I::raw(std::min(a.lo,b.lo),hi);
}
I old_profile(I h){return -q(2,3)*h+maximum({q(0),minimum({(h-q(1,2))/6,(q(27,50)-h)/3})})+q(1,400);}
I improved_profile(I h){I d=h-q(1,2);return -q(331,1000)-q(9,20)*d-q(7,4)*square(d);}
std::array<I,23> evaluate(const Box& box,int root_id,int chosen){
    int bits=root_id/4;
    int sp=(bits&16)?1:-1,sl=(bits&8)?1:-1,sr=(bits&4)?1:-1,sm=(bits&2)?1:-1,side=(bits&1)?1:-1;
    bool raised=root_id%2,wide=(root_id/2)%2;
    Frame p=folded(box[0]),l=folded(box[1]),r=folded(box[2]);
    I tp=box[0].range(),tl=box[1].range(),tr=box[2].range(),x=box[3].range(),zl=box[4].range(),zr=box[5].range(),h=box[6].range();
    Main m=main_frame(box[6]);Main mlo=point_main(box[6].point(false)),mhi=point_main(box[6].point(true));
    I tm=I::raw(std::max(i64(0),(mlo.b/mlo.a).lo),(mhi.b/mhi.a).hi);
    I thleft=old_profile(box[6].point(false)),thright=old_profile(box[6].point(true));
    I threshold=I::raw(thright.lo,thleft.hi);
    if(sm*side<0)threshold=maximum({threshold,q(-1,3)});
    else {
        I fl=improved_profile(box[6].point(false)),fr=improved_profile(box[6].point(true));
        threshold=maximum({threshold,I::raw(fr.lo,fl.hi)});
    }
    if(wide)threshold=maximum({threshold,3*h-q(211,100)});
    I wlo=m.g-q(1,60),whi=q(61,60)-h;
    I xmlo=side>0?wlo:-whi,xmhi=side>0?whi:-wlo;
    I dxlo=x-xmhi,dxhi=x-xmlo,dmax=maximum({absolute(dxlo),absolute(dxhi)});
    I sigma=maximum({1+absolute(h-p.h),signed_support(tm,tp,sm*sp)});
    std::array<std::pair<I,I>,4> normals={{{sm*m.a,m.b},{-sm*m.b,m.a},{sp*p.a,p.b},{-sp*p.b,p.a}}};
    I physical=q(100),inset=p.h;
    for(int j=0;j<4;++j){
        auto[nx,ny]=normals[j];I projection=maximum({nx*dxlo,nx*dxhi});
        physical=minimum({physical,maximum({q(1,10),sigma-projection})/maximum({ny,q(1,40)})});
        if(j>=2)inset=minimum({inset,maximum({q(1,10),q(1,2)+m.g*absolute(nx)-projection})/maximum({ny,q(1,40)})});
    }
    I plow=threshold+maximum({m.g+inset,physical,radical(maximum({q(0),square(sigma)-square(dmax)}))});
    I phigh=minimum({p.h+q(1,10),upper_corners(x,p,sp)});
    I taul=toll(box[1],l),taur=toll(box[2],r);
    I AL=maximum({q(59,60),q(157,184)+q(27,92)*(zr-r.h)+taur/46})+m.eta;
    I AR=maximum({q(59,60),q(157,184)+q(27,92)*(zl-l.h)+taul/46})+m.eta;
    auto lower_endpoint=[&](I z,Frame f,I t,int sign,I A,I cut){
        I c=maximum({q(4421,12000)+q(32,9)*m.eta,
             1-radical(q(1105,256)-square(minimum({A,q(61,60)})+q(29927,30000)))});
        I offset=q(503,480)-z;
        I loss=sign>0?maximum({q(0),t*(f.k+offset)}):maximum({q(0),(offset-f.k)/maximum({t,cut})});
        return c+f.h-loss;
    };
    I llow=raised?lower_endpoint(zl,l,tl,-sl,AL,q(1,16)):q(-1,4);
    I rlow=lower_endpoint(zr,r,tr,sr,AR,q(1,4));
    I lhigh=upper_corners(-zl,l,sl),rhigh=upper_corners(zr,r,sr);
    I DL=zl+x,DR=zr-x;
    plow=maximum({plow,llow-DL,rlow-DR});phigh=minimum({phigh,lhigh+DL,rhigh+DR});
    llow=maximum({llow,plow-DL});lhigh=minimum({lhigh,phigh+DL});
    rlow=maximum({rlow,plow-DR});rhigh=minimum({rhigh,phigh+DR});
    std::array<I,23> vals;
    vals[0]=phigh-plow;vals[1]=lhigh-llow;vals[2]=rhigh-rlow;vals[3]=q(1,30)-m.eta;
    vals[4]=q(61,60)-AL;vals[5]=q(61,60)-AR;
    vals[6]=1+l.h+r.h-zl-zr-(taul+taur)/q(27,2)-q(92,27)*m.eta;
    vals[7]=l.h+q(451,810)-zl-q(92,27)*m.eta-taul/q(27,2);
    vals[8]=r.h+q(451,810)-zr-q(92,27)*m.eta-taur/q(27,2);
    if(chosen<=8)return vals;
    auto pair_rows=[&](int index,I D,I lower,I upper,Frame f,I tf,int sf,Frame g,I tg,int sg){
        I lo=maximum({lower,-D}),hi=minimum({upper,D});
        I support=maximum({1+absolute(f.h-g.h),signed_support(tf,tg,sf*sg)});
        I projection=q(0);
        std::array<std::pair<I,I>,4> owners={{{f.a,sf*f.b},{-sf*f.b,f.a},{g.a,sg*g.b},{-sg*g.b,g.a}}};
        for(auto[nx,ny]:owners)for(I e:{lo,hi})projection=maximum({projection,absolute(nx*D+ny*e)});
        vals[index]=hi-lo;vals[index+1]=D-q(707,1000);vals[index+2]=f.h+g.h-D;
        vals[index+3]=D-1/(4*f.h)-1/(4*g.h);vals[index+4]=projection-support;
        vals[index+5]=square(D)+maximum({square(lo),square(hi)})-square(support);
    };
    if(chosen>=9&&chosen<15)pair_rows(9,DL,plow-lhigh,phigh-llow,l,tl,sl,p,tp,sp);
    if(chosen>=15&&chosen<21)pair_rows(15,DR,rlow-phigh,rhigh-plow,p,tp,sp,r,tr,sr);
    if(chosen<21)return vals;
    // Necessary owner-height intervals; each contains every true height
    // difference for that owned axis throughout this closed parameter box.
    if(chosen==21){
    auto owned_intervals=[&](I D,i64 elo,i64 ehi,Frame f,I tf,int sf,Frame g,I tg,int sg){
        std::array<std::pair<i64,i64>,4> out;
        I support=maximum({1+absolute(f.h-g.h),signed_support(tf,tg,sf*sg)});
        std::array<std::pair<I,I>,4> owners={{{f.a,sf*f.b},{f.b,-sf*f.a},{g.a,sg*g.b},{g.b,-sg*g.a}}};
        for(int j=0;j<4;++j){
            auto[nx,ny]=owners[j];i64 low=std::max(elo,-D.hi),high=std::min(ehi,D.hi);
            I numerator=support-nx*D,denominator=absolute(ny);
            if(denominator.hi==0){if(numerator.lo>0){low=SCALE;high=0;}}
            else if(denominator.lo>0||numerator.lo>0){
                i64 den=numerator.lo>=0?denominator.hi:denominator.lo;
                i64 bound=narrow(floor_div(i128(numerator.lo)*SCALE,den));
                if(ny.lo>=0)low=std::max(low,bound);else high=std::min(high,-bound);
            }
            out[j]={low,high};
        }
        return out;
    };
    auto left=owned_intervals(DL,(plow-lhigh).lo,(phigh-llow).hi,l,tl,sl,p,tp,sp);
    auto right=owned_intervals(DR,(rlow-phigh).lo,(rhigh-plow).hi,p,tp,sp,r,tr,sr);
    i64 shared=-100*SCALE;
    for(auto[el,eh]:left)for(auto[fl,fh]:right){
        i64 lo=std::max({plow.lo,narrow(i128(llow.lo)+el),narrow(i128(rlow.lo)-fh)});
        i64 hi=std::min({phigh.hi,narrow(i128(lhigh.hi)+eh),narrow(i128(rhigh.hi)-fl)});
        shared=std::max(shared,std::min({eh-el,fh-fl,hi-lo}));
    }
    vals[21]=I::raw(shared,shared);
    return vals;
    }
    // Same-P cancellation, retaining the same actual main owner on both sides.
    I sigL=signed_support(tl,tp,sl*sp),sigR=signed_support(tp,tr,sp*sr);
    i64 coupled_union=-100*SCALE;
    for(int mi=0;mi<4;++mi){
        auto[nx,ny]=normals[mi];
        I mainrow=maximum({nx*dxlo,nx*dxhi})+ny*(phigh-threshold)-sigma;
        auto side_union=[&](int epsilon,Frame f,int sf,I z,I low,I high,I support){
            std::array<std::pair<I,I>,4> owners=epsilon>0?
                std::array<std::pair<I,I>,4>{{{p.a,sp*p.b},{p.b,-sp*p.a},{f.a,sf*f.b},{f.b,-sf*f.a}}}:
                std::array<std::pair<I,I>,4>{{{f.a,sf*f.b},{f.b,-sf*f.a},{p.a,sp*p.b},{p.b,-sp*p.a}}};
            I xpos=epsilon*z,displacement=xpos-x;i64 best=-100*SCALE;
            for(int qi=0;qi<4;++qi){
                I mx=epsilon*owners[qi].first,my=epsilon*owners[qi].second;
                I basic=mx*displacement+maximum({my*(low-phigh),my*(high-plow)})-support;
                i64 bound=basic.hi;
                if(my.lo>=0){
                    I coefficient=my*nx-ny*mx;
                    bool owned_by_p=epsilon>0?qi<2:qi>=2;
                    if(mi>=2&&owned_by_p){
                        int ni=mi-2,qj=epsilon>0?qi:qi-2;
                        coefficient=q(ni==qj?0:-epsilon);
                    }
                    I mainterm=maximum({(-my*nx)*xmlo,(-my*nx)*xmhi});
                    I combined=coefficient*x+ny*mx*xpos+mainterm+ny*my*(high-threshold)-my*sigma-ny*support;
                    bound=std::min(bound,combined.hi);
                }
                best=std::max(best,bound);
            }
            return best;
        };
        i64 lmax=side_union(-1,l,sl,zl,llow,lhigh,sigL),rmax=side_union(1,r,sr,zr,rlow,rhigh,sigR);
        coupled_union=std::max(coupled_union,std::min({mainrow.hi,lmax,rmax}));
    }
    vals[22]=I::raw(coupled_union,coupled_union);
    return vals;
}
struct Pending{int depth;Box box;};
int main(){
    try{
        int root_id;std::uint64_t count,expected;std::cin>>root_id>>count>>expected;
        need(bool(std::cin),"missing proof header");need(std::cin.get()=='\n',"invalid proof header");
        need(root_id>=0&&root_id<128,"unrecognized fixed root");need(count==2*expected-1&&expected>=1,"invalid binary counts");
        std::vector<std::int8_t> events(count);std::cin.read(reinterpret_cast<char*>(events.data()),count);
        need(std::uint64_t(std::cin.gcount())==count,"truncated event stream");need(std::cin.peek()==std::char_traits<char>::eof(),"trailing bytes");
        std::vector<Pending> pending={{0,root(root_id)}};std::array<std::uint64_t,23> rules{};
        std::uint64_t at=0,leaves=0;int maxdepth=0;i64 reserve=std::numeric_limits<i64>::max();
        auto start=std::chrono::steady_clock::now(),last=start;
        while(!pending.empty()){
            Pending node=pending.back();pending.pop_back();need(at<count,"missing preorder node");int tag=events[at++];
            maxdepth=std::max(maxdepth,node.depth);need(node.depth<=70,"depth exceeds exact coordinate workspace");
            if(tag>=0){
                need(tag<7,"unknown axis");Box left=node.box,right=node.box;left[tag]=node.box[tag].child(false);right[tag]=node.box[tag].child(true);
                pending.push_back({node.depth+1,right});pending.push_back({node.depth+1,left});
            }else{
                int rule=-tag-1;need(rule>=0&&rule<23,"unknown terminal");auto values=evaluate(node.box,root_id,rule);
                if(values[rule].hi>=0){std::cerr<<"failed root "<<root_id<<" event "<<at<<" rule "<<rule<<" upper "<<values[rule].hi<<'\n';throw std::runtime_error("nonnegative leaf");}
                reserve=std::min(reserve,-values[rule].hi);++rules[rule];++leaves;
            }
            if(std::chrono::duration<double>(std::chrono::steady_clock::now()-last).count()>20){last=std::chrono::steady_clock::now();std::cerr<<"root "<<root_id<<" replayed "<<leaves<<" leaves\n";}
        }
        need(at==count&&leaves==expected,"trailing nodes or wrong leaf count");
        std::cout<<"{\"result\":\"PASS\",\"complete\":true,\"root\":"<<root_id<<",\"leaves\":"<<leaves<<",\"nodes\":"<<count<<",\"depth\":"<<maxdepth<<",\"minimum_reserve_numerator\":"<<reserve<<",\"denominator\":\"2^48\",\"rules\":[";
        for(int j=0;j<23;j++){if(j)std::cout<<',';std::cout<<rules[j];}std::cout<<"],\"seconds\":"<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<"}\n";
        return 0;
    }catch(const std::exception& e){std::cerr<<"REJECT: "<<e.what()<<'\n';return 1;}
}
