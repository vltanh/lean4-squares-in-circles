// Proves the pair lemma used in CENTRAL_CORE_CERTIFICATE.md.
// Build: g++ -O3 -std=c++17 research/eight/verify_central_core.cpp -o /tmp/n8core
// Run: /tmp/n8core
// Arithmetic and support primitives are shared with the existing verifier.
#define main sharp_marker_verifier_main
#include "verify_sharp_exterior_markers.cpp"
#undef main

I core_label(I a,I u) {
    if (a.lo <= 0) throw std::runtime_error("Positive radial coordinate required");
    // The theorem domain includes 0<=u<=a, so clipping u/a above at 1 is sound.
    I ratio(floor_div(Wide(u.lo)*SCALE,a.hi),
            std::min(SCALE,ceil_div(Wide(u.hi)*SCALE,a.lo)));
    I axial=rational(11,10)*u+rational(1,5)*square(square(ratio));
    I side=rational(5,9)+rational(3,5)*u-rational(17,50)*a;
    return {std::min({axial.lo,side.lo,CAP.lo}),
            std::min({axial.hi,side.hi,CAP.hi})};
}

Integer core_margin(const Box& b,int sg,int tg) {
    I a=b[0],u=b[1],A=b[2],v=b[3];
    I d=b[4]+rational(sg)*core_label(a,u)-rational(tg)*core_label(A,v);
    auto r=trig_bounds(d);
    I tv=tg>0?v:-v, su=sg>0?u:-u;
    return std::min({
        a.lo+HALF+minimum_term(-A.hi,-A.lo,r.cl,r.ch)+minimum_term(tv.lo,tv.hi,r.sl,r.sh),
        HALF+su.lo+minimum_term(-A.hi,-A.lo,r.sl,r.sh)+minimum_term(-tv.hi,-tv.lo,r.cl,r.ch),
        HALF-a.hi+minimum_term(A.lo,A.hi,r.cl,r.ch)+minimum_term(-tv.hi,-tv.lo,r.sl,r.sh),
        HALF-su.hi+minimum_term(A.lo,A.hi,r.sl,r.sh)+minimum_term(tv.lo,tv.hi,r.cl,r.ch)});
}

void verify_core_signs(int sg,int tg) {
    const Integer amin=rational(5,12).lo, gap=rational(11,14).hi;
    Box initial{{I(amin,3*SCALE/2),I(0,SCALE),I(amin,3*SCALE/2),
                 I(0,SCALE),I(0,gap)}};
    std::vector<Node> pending{{initial,0}};
    uint64_t nodes=0,empty=0,positive=0;
    unsigned max_depth=0;
    Integer minimum=INT64_MAX;
    const int weights[]={17,25,17,25,18};
    while (!pending.empty()) {
        Node n=pending.back(); pending.pop_back();
        if (++nodes>100000000)
            throw std::runtime_error("Node budget exhausted: NO certificate");
        max_depth=std::max(max_depth,n.depth);
        if (!contract(n.box)) { ++empty; continue; }
        Integer margin=core_margin(n.box,sg,tg);
        if (margin>0) { ++positive; minimum=std::min(minimum,margin); continue; }
        if (n.depth>150)
            throw std::runtime_error("Depth budget exhausted: NO certificate");
        int axis=0;
        for (int k=1;k<5;++k)
            if ((n.box[k].hi-n.box[k].lo)*weights[k] >
                (n.box[axis].hi-n.box[axis].lo)*weights[axis]) axis=k;
        Integer mid=n.box[axis].lo+(n.box[axis].hi-n.box[axis].lo)/2;
        if (mid==n.box[axis].lo)
            throw std::runtime_error("Resolution exhausted: NO certificate");
        Node left=n,right=n;
        left.box[axis].hi=mid; right.box[axis].lo=mid;
        ++left.depth; ++right.depth;
        pending.push_back(left); pending.push_back(right);
    }
    if (nodes!=2*(empty+positive)-1)
        throw std::runtime_error("Partition accounting failed");
    std::cout << "VERIFIED CORE " << sg << " " << tg << " nodes=" << nodes
              << " empty=" << empty << " positive=" << positive
              << " depth=" << max_depth << " minimum_margin=" << minimum
              << "/" << SCALE << std::endl;
}

int main() {
    try {
        static_assert(N8_Q_NUM==98 && N8_Q_DEN==25,
                      "The central-core certificate uses squared radius 98/25");
        Integer factorial[20]; factorial[0]=1;
        for (int k=1;k<20;++k) factorial[k]=factorial[k-1]*k;
        for (int k=0;k<10;++k) {
            I sn=rational(k%2?-1:1,factorial[2*k+1]);
            sine19.push_back(sn); if (k<9) sine17.push_back(sn);
            I cn=rational(k%2?-1:1,factorial[2*k]);
            cosine18.push_back(cn); if (k<9) cosine16.push_back(cn);
        }
        for (int s : {-1,1}) for (int t : {-1,1}) verify_core_signs(s,t);
        std::cout << "All four core-label sign cases passed. "
                  << "See the note for the eight-square counting consequence." << std::endl;
        return 0;
    } catch (const std::exception& e) {
        std::cerr << e.what() << std::endl;
        return 1;
    }
}
