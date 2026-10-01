// Exact dyadic interval certificate for exterior marker separation > 7/8.
// Build: g++ -O3 -std=c++17 verify_sharp_exterior_markers.cpp -o /tmp/n8marker
// Run: /tmp/n8marker                 (all four sign choices)
// This is NOT an unrestricted proof of the eight-square optimal radius.
// See SHARP_MARKER_RING.md for domains, arithmetic soundness and consequences.
#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <vector>

using Wide = __int128_t;
using Integer = int64_t;
constexpr Integer SCALE = Integer(1) << 48;
constexpr Integer HALF = SCALE / 2;

Integer floor_div(Wide a, Wide b) {
    if (b <= 0) throw std::runtime_error("Nonpositive denominator");
    Wide q = a / b, r = a % b;
    if (r < 0) --q;
    return Integer(q);
}
Integer ceil_div(Wide a, Wide b) { return -floor_div(-a, b); }

struct Interval {
    Integer lo, hi;
    Interval() : lo(0), hi(0) {}
    Interval(Integer a, Integer b) : lo(a), hi(b) {
        if (a > b) throw std::runtime_error("Reversed interval endpoints");
    }
};
using I = Interval;
I rational(Integer p, Integer q = 1) {
    return {floor_div(Wide(p) * SCALE, q), ceil_div(Wide(p) * SCALE, q)};
}
I operator+(I a, I b) { return {a.lo + b.lo, a.hi + b.hi}; }
I operator-(I a) { return {-a.hi, -a.lo}; }
I operator-(I a, I b) { return a + -b; }
I operator*(I a, I b) {
    Wide w[] = {Wide(a.lo)*b.lo, Wide(a.lo)*b.hi,
                Wide(a.hi)*b.lo, Wide(a.hi)*b.hi};
    auto mm = std::minmax_element(w, w+4);
    return {floor_div(*mm.first, SCALE), ceil_div(*mm.second, SCALE)};
}
I square(I a) {
    Wide v = Wide(a.lo)*a.lo, w = Wide(a.hi)*a.hi;
    return {(a.lo <= 0 && 0 <= a.hi) ? 0 : floor_div(std::min(v,w), SCALE),
            ceil_div(std::max(v,w), SCALE)};
}
Integer integer_sqrt(Wide n) {
    if (n < 0) throw std::runtime_error("Negative square-root input");
    // Floating point supplies ONLY an initial integer guess. The exact loops
    // establish r^2 <= n < (r+1)^2, even if that guess is inaccurate.
    Integer r = Integer(std::sqrt((long double)n));
    while (Wide(r)*r > n) --r;
    while (Wide(r+1)*(r+1) <= n) ++r;
    return r;
}
I root(I a) {
    if (a.hi < 0) throw std::runtime_error("Empty radicand");
    Integer lo = integer_sqrt(Wide(std::max(Integer(0),a.lo))*SCALE);
    Integer hi = integer_sqrt(Wide(a.hi)*SCALE);
    return {lo, hi + (Wide(hi)*hi != Wide(a.hi)*SCALE)};
}
const I CEILING = rational(98,25), CAP = rational(157,200);
std::vector<I> sine17, sine19, cosine16, cosine18;
I polynomial(const std::vector<I>& coefficients, I x) {
    I out = coefficients.back();
    for (int k=int(coefficients.size())-2; k>=0; --k)
        out = out*x + coefficients[k];
    return out;
}
struct Trig { Integer sl, sh, cl, ch; };
Trig point_trig(Integer v) {
    I x(std::abs(v),std::abs(v)), xx=square(x);
    I sl=x*polynomial(sine19,xx), sh=x*polynomial(sine17,xx);
    I cl=polynomial(cosine18,xx), ch=polynomial(cosine16,xx);
    if (v<0) return {-sh.hi,-sl.lo,cl.lo,ch.hi};
    return {sl.lo,sh.hi,cl.lo,ch.hi};
}
Trig trig_bounds(I d) {
    if (d.lo < -5*SCALE/2 || d.hi > 5*SCALE/2)
        throw std::runtime_error("Trigonometric domain exceeded");
    auto a=point_trig(d.lo), b=point_trig(d.hi);
    Trig out{std::min(a.sl,b.sl),std::max(a.sh,b.sh),
             std::min(a.cl,b.cl),std::max(a.ch,b.ch)};
    // 157/50 < pi < 22/7: include every possible interior extremum.
    if (d.lo<=rational(-157,100).hi && d.hi>=rational(-11,7).lo) out.sl=-SCALE;
    if (d.lo<=rational(11,7).hi && d.hi>=rational(157,100).lo) out.sh=SCALE;
    if (d.lo<=0 && d.hi>=0) out.ch=SCALE;
    return out;
}
I label(I a,I u) {
    I x=rational(11,10)*u;
    I y=rational(5,9)+rational(3,5)*u-rational(17,50)*a;
    return {std::min({x.lo,y.lo,CAP.lo}),std::min({x.hi,y.hi,CAP.hi})};
}
Integer minimum_term(Integer al,Integer ah,Integer xl,Integer xh) {
    // Minimum of alpha*x+|x|/2: four rectangle corners and possibly x=0.
    Wide n=std::min({Wide(al)*xl+Wide(HALF)*std::abs(xl),
                     Wide(al)*xh+Wide(HALF)*std::abs(xh),
                     Wide(ah)*xl+Wide(HALF)*std::abs(xl),
                     Wide(ah)*xh+Wide(HALF)*std::abs(xh)});
    if (xl<=0 && 0<=xh) n=std::min(n,Wide(0));
    return floor_div(n,SCALE);
}
using Box=std::array<I,5>;
Integer margin_bound(const Box& b,int sg,int tg) {
    I a=b[0],u=b[1],A=b[2],v=b[3];
    I d=b[4]+rational(sg)*label(a,u)-rational(tg)*label(A,v);
    auto r=trig_bounds(d);
    I tv=tg>0?v:-v, su=sg>0?u:-u;
    return std::min({
        a.lo+HALF+minimum_term(-A.hi,-A.lo,r.cl,r.ch)+minimum_term(tv.lo,tv.hi,r.sl,r.sh),
        HALF+su.lo+minimum_term(-A.hi,-A.lo,r.sl,r.sh)+minimum_term(-tv.hi,-tv.lo,r.cl,r.ch),
        HALF-a.hi+minimum_term(A.lo,A.hi,r.cl,r.ch)+minimum_term(-tv.hi,-tv.lo,r.sl,r.sh),
        HALF-su.hi+minimum_term(A.lo,A.hi,r.sl,r.sh)+minimum_term(tv.lo,tv.hi,r.cl,r.ch)});
}
bool contract(Box& b) {
    for (int j : {0,2}) {
        I &a=b[j], &u=b[j+1];
        a.lo=std::max(a.lo,u.lo);
        if (a.lo>a.hi) return false;
        for (int k=0;k<2;++k) {
            I r=CEILING-square(I(u.lo+HALF,u.lo+HALF));
            if (r.hi<0) return false;
            a.hi=std::min(a.hi,root(r).hi-HALF);
            r=CEILING-square(I(a.lo+HALF,a.lo+HALF));
            if (r.hi<0) return false;
            u.hi=std::min({u.hi,a.hi,root(r).hi-HALF});
        }
        if (a.lo>a.hi || u.lo>u.hi) return false;
        I disk=square(I(a.lo+HALF,a.lo+HALF))+square(I(u.lo+HALF,u.lo+HALF));
        if (disk.lo>CEILING.hi) return false;
    }
    return true;
}
struct Node { Box box; unsigned depth; };
void verify(int sg,int tg,uint64_t limit) {
    Box initial{{I(HALF,3*SCALE/2),I(0,SCALE),I(HALF,3*SCALE/2),
                 I(0,SCALE),I(0,7*SCALE/8)}};
    std::vector<Node> pending{{initial,0}};
    uint64_t nodes=0,empty=0,positive=0;
    unsigned max_depth=0;
    Integer minimum=INT64_MAX;
    const int weights[]={17,25,17,25,18};
    auto start=std::chrono::steady_clock::now();
    while (!pending.empty()) {
        Node n=pending.back(); pending.pop_back();
        if (++nodes>limit) throw std::runtime_error("Node budget exhausted: NO certificate");
        max_depth=std::max(max_depth,n.depth);
        if (!contract(n.box)) { ++empty; continue; }
        Integer margin=margin_bound(n.box,sg,tg);
        if (margin>0) { ++positive; minimum=std::min(minimum,margin); continue; }
        if (n.depth>150) throw std::runtime_error("Depth budget exhausted: NO certificate");
        int axis=0;
        for (int k=1;k<5;++k)
            if ((n.box[k].hi-n.box[k].lo)*weights[k] >
                (n.box[axis].hi-n.box[axis].lo)*weights[axis]) axis=k;
        Integer mid=n.box[axis].lo+(n.box[axis].hi-n.box[axis].lo)/2;
        if (mid==n.box[axis].lo) throw std::runtime_error("Resolution exhausted: NO certificate");
        Node left=n,right=n;
        left.box[axis].hi=mid; right.box[axis].lo=mid;
        ++left.depth; ++right.depth;
        pending.push_back(left); pending.push_back(right);
    }
    if (nodes!=2*(empty+positive)-1) throw std::runtime_error("Partition accounting failed");
    std::cout << "VERIFIED " << sg << " " << tg << " nodes=" << nodes
              << " empty=" << empty << " positive=" << positive
              << " depth=" << max_depth << " minimum_margin=" << minimum
              << "/" << SCALE << " seconds="
              << std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()
              << std::endl;
}
int main(int argc,char** argv) {
    try {
        Integer factorial[20]; factorial[0]=1;
        for (int k=1;k<20;++k) factorial[k]=factorial[k-1]*k;
        for (int k=0;k<10;++k) {
            I sn=rational(k%2?-1:1,factorial[2*k+1]);
            sine19.push_back(sn); if (k<9) sine17.push_back(sn);
            I cn=rational(k%2?-1:1,factorial[2*k]);
            cosine18.push_back(cn); if (k<9) cosine16.push_back(cn);
        }
        constexpr uint64_t limit=100000000;
        if (argc==3) {
            int s=std::atoi(argv[1]),t=std::atoi(argv[2]);
            if (std::abs(s)!=1 || std::abs(t)!=1) throw std::runtime_error("Signs must be +/-1");
            verify(s,t,limit);
        } else if (argc==1) {
            for (int s : {-1,1}) for (int t : {-1,1}) verify(s,t,limit);
        } else throw std::runtime_error("Usage: verifier [source-sign target-sign]");
        return 0;
    } catch (const std::exception& e) {
        std::cerr << e.what() << std::endl;
        return 1;
    }
}
