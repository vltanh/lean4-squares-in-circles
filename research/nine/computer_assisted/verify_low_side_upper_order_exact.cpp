// Independent exact replay of the lower-central / low-side upper-order cover.
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
using Box=std::array<Coordinate,6>;
Box root(int){return {{{0,1,1},{0,1,1},{0,1,1},{0,1129,3000},{42,23,60},{50,7,100}}};}
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

// Two pointwise identities for the support at the folded-angle difference.
// Their interval intersection contains the same exact expression.  The
// absolute width increment is a second, independently valid lower support.
I lower_support(Frame f,Frame g){
    I difference=(1+f.a*g.a+f.b*g.b+absolute(f.a*g.b-f.b*g.a))/2;
    I folded_identity=q(1,2)+maximum({f.k*g.a+f.h*g.b,f.h*g.a-f.k*g.b});
    return maximum({1+absolute(f.h-g.h),intersection(difference,folded_identity)});
}

I vertical_clearance(Frame f,Frame g,I d){
    I support=lower_support(f,g);
    I axes=minimum({(support-f.a*d)/maximum({f.b,q(1,40)}),
                    (support-f.b*d)/f.a,
                    (support-g.a*d)/maximum({g.b,q(1,40)}),
                    (support-g.b*d)/g.a});
    I center=radical(maximum({q(0),square(support)-square(d)}));
    return maximum({axes,center});
}

std::array<I,13> necessary_rows(const Box& box,int chart){
    need(chart>=0&&chart<8,"invalid chirality chart");
    int main_side=(chart&4)?1:-1;
    int signP=(chart&2)?1:-1;
    int signR=(chart&1)?1:-1;
    I tR=box[1].range(),x=box[3].range(),X=box[4].range(),h=box[5].range();
    Frame p=folded(box[0]),r=folded(box[1]),s=folded(box[2]);
    Main main=main_frame(box[5]);
    Frame m{main.a,main.b,h,main.k};
    I g=main.g,eta=main.eta;
    I tau=toll(box[1],r);
    I AL=eta+maximum({q(59,60),q(157,184)+q(27,92)*(X-r.h)+tau/46});
    I AR=q(59,60)+eta;
    auto endpoint_height=[&](I A){
        I edge=minimum({A,q(61,60)});
        return maximum({q(4421,12000)+q(32,9)*eta,
                        1-radical(q(1105,256)-square(edge+q(29927,30000)))});
    };
    I cL=endpoint_height(AL),cR=endpoint_height(AR),e=q(3,5)-cL;
    I qmin=minimum({s.h,(q(1,2)-s.b*e)/s.a,
                       (q(1,2)-s.a*e)/maximum({s.b,q(1,40)})});
    I zmax=minimum({q(121,200),q(503,480)-qmin});
    I dPS=maximum({q(0),x+zmax});
    I KPS=vertical_clearance(p,s,dPS);
    I delta=q(331,20000);
    I dMP=main_side<0?x+1+delta-h:
        maximum({absolute(x-(g-delta)),absolute(x-(1+delta-h))});
    I inset=g+minimum({p.h,(q(1,2)+(g-dMP)*p.b)/p.a,
                          (q(1,2)+(g-dMP)*p.a)/maximum({p.b,q(1,40)})});
    I Pminus=-q(1823,3000)+maximum({vertical_clearance(m,p,dMP),inset});
    I Pplus=minimum({p.h+q(1,10),upper_corners(x,p,signP),q(3,5)-KPS});
    I qR=q(503,480)-X;
    I loss=signR>0?maximum({q(0),tR*(r.k+qR)}):
        maximum({q(0),(qR-r.k)/maximum({tR,q(1,4)})});
    I Rminus=maximum({q(3,5),cR+r.h-loss});
    I Rplus=upper_corners(X,r,signR),D=X-x;

    // Each contraction preserves the same original P and R height pair.
    Pminus=maximum({Pminus,Rminus-D});
    Pplus=minimum({Pplus,Rplus+D});
    Rminus=maximum({Rminus,Pminus-D});
    Rplus=minimum({Rplus,Pplus+D});
    I Eminus=maximum({Rminus-Pplus,-D});
    I Eplus=minimum({Rplus-Pminus,D});

    I dot=p.a*r.a+(signP*signR)*p.b*r.b;
    I det=signR*p.a*r.b-signP*p.b*r.a;
    I support=(1+absolute(dot)+absolute(det))/2;
    std::array<std::pair<I,I>,4> axes={{{p.a,signP*p.b},
            {-signP*p.b,p.a},{r.a,signR*r.b},{-signR*r.b,r.a}}};
    I projection=q(0);
    for(auto [nx,ny]:axes)for(I E:{Eminus,Eplus})
        projection=maximum({projection,absolute(nx*D+ny*E)});
    return {Pplus-Pminus,Rplus-Rminus,zmax-q(29,60),q(61,60)-AL,
            q(61,60)-AR,q(1,30)-eta,
            r.h+q(451,810)-X-q(92,27)*eta-q(2,27)*tau,
            Eplus-Eminus,D-q(707,1000),p.h+r.h-D,
            D-1/(4*p.h)-1/(4*r.h),projection-support,
            square(D)+maximum({square(Eminus),square(Eplus)})-square(support)};
}

struct Pending{int chart,depth;Box box;};
int main(){
    try{
        const auto started=std::chrono::steady_clock::now();
        std::uint64_t declared_nodes=0,declared_leaves=0;
        need(bool(std::cin>>declared_nodes>>declared_leaves),"missing event header");
        need(declared_leaves>=8&&declared_leaves<=50000000,"invalid declared leaf count");
        need(declared_nodes==2*declared_leaves-8,"forest node/leaf identity failed");
        need(std::cin.get()=='\n',"event header requires newline");
        std::vector<Pending> pending;
        for(int chart=7;chart>=0;--chart)pending.push_back({chart,0,root(chart)});
        std::array<std::uint64_t,13> counts{};
        std::array<std::uint64_t,8> per_root{};
        std::uint64_t leaves=0,nodes=0;
        int maxdepth=0;
        i64 minimum_reserve=std::numeric_limits<i64>::max();
        while(nodes<declared_nodes){
            need(!pending.empty(),"event after completed forest");
            int raw=std::cin.get();need(raw!=EOF,"truncated event stream");
            int tag=raw<=127?raw:raw-256;
            Pending p=pending.back();pending.pop_back();
            ++nodes;maxdepth=std::max(maxdepth,p.depth);
            need(p.depth<=70,"forest depth exceeds limit");
            if(tag>=0){
                need(tag<6,"invalid split coordinate");
                need(p.depth<70,"split exceeds depth limit");
                Box left=p.box,right=p.box;
                left[tag]=left[tag].child(false);right[tag]=right[tag].child(true);
                pending.push_back({p.chart,p.depth+1,right});
                pending.push_back({p.chart,p.depth+1,left});
            }else{
                int code=-tag-1;need(code>=0&&code<13,"invalid scalar code");
                I expression=necessary_rows(p.box,p.chart)[code];
                if(expression.hi>=0){
                    std::cerr<<"non-strict leaf at node "<<nodes-1<<", chart "
                             <<p.chart<<", scalar "<<code<<", upper "
                             <<expression.hi<<" / 2^48\n";
                    throw std::runtime_error("a claimed leaf is not strictly excluded");
                }
                minimum_reserve=std::min(minimum_reserve,-expression.hi);
                ++counts[code];++per_root[p.chart];++leaves;
            }
        }
        need(pending.empty(),"uncovered forest frontier");
        need(std::cin.get()==EOF,"trailing event bytes");
        need(leaves==declared_leaves,"declared leaf count differs from replay");
        need(minimum_reserve>0,"nonpositive reserve");
        const double seconds=std::chrono::duration<double>(
            std::chrono::steady_clock::now()-started).count();
        std::cout<<"{\"result\":\"PASS\",\"complete\":true,\"roots\":8,\"nodes\":"
                 <<nodes<<",\"strict_leaves\":"<<leaves<<",\"maximum_depth\":"
                 <<maxdepth<<",\"minimum_positive_reserve_numerator\":\""
                 <<minimum_reserve<<"\",\"scale_bits\":48,\"counts\":[";
        for(int j=0;j<13;++j){if(j)std::cout<<',';std::cout<<counts[j];}
        std::cout<<"],\"leaves_per_root\":[";
        for(int j=0;j<8;++j){if(j)std::cout<<',';std::cout<<per_root[j];}
        std::cout<<"],\"seconds\":"<<seconds<<"}\n";
        return 0;
    }catch(const std::exception& e){
        std::cerr<<"REJECTED: "<<e.what()<<'\n';return 1;
    }
}

