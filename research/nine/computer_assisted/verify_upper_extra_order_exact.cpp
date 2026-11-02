// Independent exact replay of the 010/11 upper-central-extra ordering cover.
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
        // Exact root coordinates have at most 60 dyadic subdivisions.
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
        need(level<=60,"unsupported subdivision depth");i128 power=i128(1)<<level;
        return {base*power+width*i128(index+(upper?1:0)),den*power};
    }
    I point(bool upper)const{auto[n,d]=endpoint(upper);return I::rational(n,d);}
    I range()const{I a=point(false),b=point(true);return I::raw(a.lo,b.hi);}
    Coordinate child(bool right)const{Coordinate c=*this;c.index=2*index+(right?1:0);++c.level;return c;}
};
using Box=std::array<Coordinate,7>;
Box root(int id){
    return {{{0,1,1},{0,1,1},{0,1,1},{0,1129,3000},
             {id%2?36:19,id%2?29:17,60},{42,23,60},{10,3,20}}};
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

// Convex original outer-cone lower-height function. Both endpoint
// values bound its maximum; its only minimum is h=sqrt(41/128).
// The fixed-point interval comparison includes the critical point
// whenever it could lie in the exact rational box.
I main_height_range(const Coordinate& coord){
    auto value=[](I h){return q(32,9)*h+q(41,36)/h-q(32,9)-q(199,120);};
    I left=value(coord.point(false)),right=value(coord.point(true));
    i64 low=std::min(left.lo,right.lo),high=std::max(left.hi,right.hi);
    I hsquared=square(coord.range()),critical=q(41,128);
    if(hsquared.lo<=critical.hi&&hsquared.hi>=critical.lo){
        I global_min=4*radical(q(82))/9-q(32,9)-q(199,120);
        low=std::min(low,global_min.lo);
    }
    return I::raw(low,high);
}

std::array<I,21> evaluate(const Box& box,int root_id){
    int bits=root_id/2,sp=(bits&4)?1:-1,sl=(bits&2)?1:-1,sr=(bits&1)?1:-1;
    bool raised=root_id%2;
    Frame p=folded(box[0]),l=folded(box[1]),r=folded(box[2]);
    I tp=box[0].range(),tl=box[1].range(),tr=box[2].range();
    I x=box[3].range(),zl=box[4].range(),zr=box[5].range(),h=box[6].range();
    Main m=main_frame(box[6]);
    // Eliminate the actual intermediate U by concavity in its position
    // and halfwidth, then retain all four endpoint radical sums.
    I difference=absolute(h-p.h),separation_support=1+difference;
    auto endpoint_sum=[&](I z){
        I d1=maximum({z-m.g+q(1,60),q(61,60)-h-z});
        I d2=x+z;
        I first=radical(1-square(d1))+radical(square(separation_support)-square(d2));
        I second=radical(square(separation_support)-square(d1))+radical(1-square(d2));
        return minimum({first,second});
    };
    I plow=main_height_range(box[6])+minimum({endpoint_sum(q(0)),endpoint_sum(q(29,60))});
    I phigh=minimum({p.h+q(1,10),upper_corners(x,p,sp)});
    I taul=toll(box[1],l),taur=toll(box[2],r);
    I AL=maximum({q(59,60),q(157,184)+q(27,92)*(zr-r.h)+taur/46})+m.eta;
    I AR=maximum({q(59,60),q(157,184)+q(27,92)*(zl-l.h)+taul/46})+m.eta;
    auto low_endpoint=[&](I z,Frame f,I t,int local_sign,I load,I cut){
        I c=maximum({q(4421,12000)+q(32,9)*m.eta,
             1-radical(q(1105,256)-square(minimum({load,q(61,60)})+q(29927,30000)))});
        I s=q(503,480)-z;
        I loss=local_sign>0?maximum({q(0),t*(f.k+s)}):
                            maximum({q(0),(s-f.k)/maximum({t,cut})});
        return c+f.h-loss;
    };
    I llow=raised?low_endpoint(zl,l,tl,-sl,AL,q(1,16)):q(-9,20);
    I rlow=low_endpoint(zr,r,tr,sr,AR,q(1,4));
    // The left unit's actual global frame is used at its negative x.
    I lhigh=upper_corners(-zl,l,sl),rhigh=upper_corners(zr,r,sr);
    // Every contraction follows one of the two retained original cone
    // edges. The displayed order is part of the exact scalar definition.
    I DL=zl+x,DR=zr-x;
    plow=maximum({plow,llow-DL,rlow-DR});
    phigh=minimum({phigh,lhigh+DL,rhigh+DR});
    llow=maximum({llow,plow-DL});
    lhigh=minimum({lhigh,phigh+DL});
    rlow=maximum({rlow,plow-DR});
    rhigh=minimum({rhigh,phigh+DR});
    std::array<I,21> vals;
    vals[0]=phigh-plow;vals[1]=lhigh-llow;vals[2]=rhigh-rlow;
    vals[3]=q(1,30)-m.eta;vals[4]=q(61,60)-AL;vals[5]=q(61,60)-AR;
    vals[6]=1+l.h+r.h-zl-zr-(taul+taur)/q(27,2)-q(92,27)*m.eta;
    vals[7]=l.h+q(451,810)-zl-q(92,27)*m.eta-taul/q(27,2);
    vals[8]=r.h+q(451,810)-zr-q(92,27)*m.eta-taur/q(27,2);
    auto pair=[&](int start,I D,I lower,I upper,Frame a,int sa,Frame b,int sb){
        I lo=maximum({lower,-D}),hi=minimum({upper,D});
        I cos=a.a*b.a+(sa*sb)*a.b*b.b;
        I sin=sb*a.a*b.b-sa*a.b*b.a;
        I sigma=maximum({q(1),(1+absolute(cos)+absolute(sin))/2});
        I projection=q(0);
        std::array<std::pair<I,I>,4> axes={{{a.a,sa*a.b},{-sa*a.b,a.a},
                                           {b.a,sb*b.b},{-sb*b.b,b.a}}};
        for(auto [nx,ny]:axes)for(I e:{lo,hi})projection=maximum({projection,absolute(nx*D+ny*e)});
        vals[start]=hi-lo;vals[start+1]=D-q(707,1000);vals[start+2]=a.h+b.h-D;
        vals[start+3]=D-1/(4*a.h)-1/(4*b.h);vals[start+4]=projection-sigma;
        vals[start+5]=square(D)+maximum({square(lo),square(hi)})-square(sigma);
    };
    pair(9,zl+x,plow-lhigh,phigh-llow,l,sl,p,sp);
    pair(15,zr-x,rlow-phigh,rhigh-plow,p,sp,r,sr);
    return vals;
}

struct Pending{int root_id,depth;Box box;};
void print_box(const Box& box){
    std::cout<<'[';for(int i=0;i<7;++i){if(i)std::cout<<',';auto[l,d]=box[i].endpoint(false);auto[h,e]=box[i].endpoint(true);
        std::cout<<"[\""<<integer_text(l)<<'/'<<integer_text(d)<<"\",\""<<integer_text(h)<<'/'<<integer_text(e)<<"\"]";}
    std::cout<<']';
}
int main(){
    try{
        std::uint64_t count,expected;std::cin>>count>>expected;
        need(bool(std::cin),"missing binary proof header");need(std::cin.get()=='\n',"invalid binary proof header");
        need(count==2*expected-16&&expected>=16,"invalid forest counts");
        std::vector<std::int8_t> events(count);std::cin.read(reinterpret_cast<char*>(events.data()),count);
        need(std::uint64_t(std::cin.gcount())==count,"truncated event stream");need(std::cin.peek()==std::char_traits<char>::eof(),"trailing event bytes");
        std::vector<Pending> pending;for(int i=15;i>=0;--i)pending.push_back({i,0,root(i)});
        std::array<std::uint64_t,21> rules{};std::array<std::uint64_t,16> per_root{};
        std::uint64_t at=0,leaves=0;int depth=0;i64 reserve=std::numeric_limits<i64>::max();
        auto start=std::chrono::steady_clock::now(),last=start;
        while(!pending.empty()){
            Pending node=pending.back();pending.pop_back();
            need(at<count,"missing preorder node");std::uint64_t index=at;int tag=events[at++];depth=std::max(depth,node.depth);
            need(node.depth<=60,"certificate depth exceeds exact rational workspace");
            if(tag>=0){
                need(tag<7,"invalid split coordinate");Pending left=node,right=node;
                left.depth=right.depth=node.depth+1;
                left.box[tag]=node.box[tag].child(false);right.box[tag]=node.box[tag].child(true);
                pending.push_back(right);pending.push_back(left);
            }else{
                int code=-tag-1;need(code>=0&&code<21,"invalid necessary scalar channel");
                auto vals=evaluate(node.box,node.root_id);
                if(vals[code].hi>=0){
                    std::cout<<"{\"complete\":false,\"failed_event\":"<<index<<",\"root\":"<<node.root_id<<",\"depth\":"<<node.depth
                             <<",\"code\":"<<code<<",\"upper_numerator\":\""<<vals[code].hi<<"\",\"scale_bits\":"<<BITS<<",\"box\":";
                    print_box(node.box);std::cout<<",\"all_upper_numerators\":[";
                    for(int j=0;j<21;++j){if(j)std::cout<<',';std::cout<<'\"'<<vals[j].hi<<'\"';}std::cout<<"]}\n";return 2;
                }
                reserve=std::min(reserve,-vals[code].hi);++leaves;++rules[code];++per_root[node.root_id];
            }
            if(leaves%20000==0){auto now=std::chrono::steady_clock::now();if(std::chrono::duration_cast<std::chrono::seconds>(now-last).count()>=20){
                std::cerr<<"exact 01011 upper-extra ordering replay: "<<leaves<<" leaves, root "<<node.root_id<<", event "<<at<<'\n';last=now;}}
        }
        need(at==count&&leaves==expected,"incomplete or trailing forest");
        std::cout<<"{\"complete\":true,\"nodes\":"<<at<<",\"strict_leaves\":"<<leaves<<",\"maximum_depth\":"<<depth
                 <<",\"scale_bits\":"<<BITS<<",\"least_positive_reserve_numerator\":\""<<reserve<<"\",\"counts\":[";
        for(int i=0;i<21;++i){if(i)std::cout<<',';std::cout<<rules[i];}std::cout<<"],\"leaves_per_root\":[";
        for(int i=0;i<16;++i){if(i)std::cout<<',';std::cout<<per_root[i];}
        std::cout<<"],\"seconds\":"<<std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now()-start).count()/1000.0<<"}\n";
        return 0;
    }catch(const std::exception& e){std::cerr<<"exact checker rejected: "<<e.what()<<'\n';return 3;}
}
