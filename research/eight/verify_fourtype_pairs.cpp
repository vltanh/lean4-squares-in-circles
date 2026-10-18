// Candidate validator. This program is a proof only if every closed branch passes.
// Its arithmetic is the audited 2^-48 dyadic interval arithmetic from PR #9.
#define main original_dyadic_main
#include "exact_dyadic_base.cpp"
#undef main
#include <fstream>
#include <string>

I quotient(I a,I b) {
    if(b.lo<=0) throw std::runtime_error("Nonpositive interval divisor");
    Wide n[]={Wide(a.lo)*SCALE,Wide(a.hi)*SCALE};
    Integer ls[]={floor_div(n[0],b.lo),floor_div(n[0],b.hi),floor_div(n[1],b.lo),floor_div(n[1],b.hi)};
    Integer hs[]={ceil_div(n[0],b.lo),ceil_div(n[0],b.hi),ceil_div(n[1],b.lo),ceil_div(n[1],b.hi)};
    return {*std::min_element(ls,ls+4),*std::max_element(hs,hs+4)};
}
I absolute(I a) {
    if(a.lo>=0)return a;
    if(a.hi<=0)return -a;
    return {0,std::max(-a.lo,a.hi)};
}
I point(Integer x){return {x,x};}
I enclosed(I a,I b){return {a.lo,b.hi};}
const I QQ=rational(9789,2500),BETA=rational(9,50),DMIN=rational(3,5);
const Integer VALUES[4][9]={
 {0,4963699,8978948,12327199,14841828,8212593,-5496777,-2591030,0},
 {0,-1166957,-2242117,-3190746,-3838175,-4292398,-4663542,-4951387,-5168609},
 {-5846760,-6217415,-5611024,-6755028,-6673340,-6247421,-5827636,-5445707,-5034897},
 {-6028360,-5413423,-4267209,-3424593,-2597544,-1806376,-1103832,-526867,0}};
const Integer GAMMAS[4][4]={{910793,910782,900470,883157},{910782,910793,900481,883146},{900470,900481,890169,893458},{883157,883146,893458,910793}};

struct Segment {int type,sign,piece; I left,right,slope,intercept;};
I knot(int type,int k) {
    if(type==0)return rational(k,8);
    if(type==1)return rational(k,32);
    if(type==2)return rational(14+5*k,56);
    return rational(3+k,7);
}
// Fix the rational knots: type2 goes from 1/4 to3/7 in8steps;
// type3 goes from3/7 to1 in8steps.
I actual_knot(int type,int k) {
    if(type==2)return rational(56+5*k,224);
    if(type==3)return rational(6+k,14);
    return knot(type,k);
}
Segment segment(int ty,int sign,int k) {
    I l=actual_knot(ty,k),r=actual_knot(ty,k+1);
    // Difference in knots is positive and rational; use its explicit reciprocal.
    I inverse= ty==0?rational(8):ty==1?rational(32):ty==2?rational(224,5):rational(14);
    I m=rational(VALUES[ty][k+1]-VALUES[ty][k],100000000)*inverse;
    I b=rational(VALUES[ty][k],100000000)-m*l;
    return {ty,sign,k,l,r,m,b};
}
I potential(const Segment& s,I x) {return rational(s.sign)*(s.slope*x+s.intercept);}
I local_a_point(int type,Integer x) {
    I t=point(x);
    if(type>0){
        I A=rational(1)+square(t),L=rational(1)+t;
        return quotient(root(square(L)+rational(4)*A*(QQ-rational(1,2)))-L,rational(2)*A);
    }
    I cut=rational(6,7);
    if(x<=cut.lo)return rational(7,12);
    I A=rational(1)+square(t),L=rational(1)+t;
    I result=quotient(L+root(square(L)-rational(4)*A*rational(71,144)),rational(2)*A);
    if(x<cut.hi){I side=rational(7,12);result.lo=std::min(result.lo,side.lo);result.hi=std::max(result.hi,side.hi);}
    return result;
}
I local_a(int type,I x) {
    // On every boundary local a decreases with |t|; the core side is constant.
    return enclosed(local_a_point(type,x.hi),local_a_point(type,x.lo));
}

struct PairBox {I x,y;unsigned depth;};
struct Algebra {I t,u,aa,ab,A,B,Z,K,L,dpsi;std::array<I,4> X,Y,C;};
Algebra algebra(const Segment& sa,const Segment& sb,const PairBox& box) {
    Algebra g;g.t=rational(sa.sign)*box.x;g.u=rational(sb.sign)*box.y;
    g.aa=local_a(sa.type,box.x);g.ab=local_a(sb.type,box.y);
    g.A=rational(1)+square(g.t);g.B=rational(1)+square(g.u);
    g.Z=root(g.A*g.B);g.K=rational(1)+g.t*g.u;g.L=g.u-g.t;
    g.dpsi=potential(sb,box.y)-potential(sa,box.x);
    I V=g.ab*g.B,W=g.aa*g.A;
    g.X={V,-V*g.t,-W,W*g.u};
    g.Y={V*g.t,V,W*g.u,W};
    g.C={-g.aa*g.Z,g.aa*g.t*g.Z,g.ab*g.Z,-g.ab*g.u*g.Z};
    return g;
}
I cost_at(const Algebra& g,Integer d,I gamma) {
    Trig q=point_trig(d);I C(q.cl,q.ch),S(q.sl,q.sh);
    I width=quotient(absolute(g.K*C-g.L*S)+absolute(g.K*S+g.L*C),rational(2)*g.Z)-rational(1,2);
    return point(d)-BETA*width+g.dpsi-gamma;
}
Integer delta_upper(const Algebra& g,I gamma,Integer resolution) {
    I excess=(root(rational(2))-rational(1))*rational(1,2);
    Integer hi=(gamma-g.dpsi+BETA*excess).hi;
    if(hi<=DMIN.lo)return hi;
    if(hi>5*SCALE/2)throw std::runtime_error("Cost gap exceeds trig domain");
    Integer lo=DMIN.lo;
    for(int k=0;k<22 && hi-lo>resolution;++k){
        Integer mid=lo+(hi-lo)/2;
        if(cost_at(g,mid,gamma).lo>=0)hi=mid;else lo=mid;
    }
    return hi;
}

Integer scalar_trig_max(Integer x,Integer y,I d) {
    // d in[3/5,5/2], where sin ispositive. Max ofxcos+y sin.
    Trig ql=point_trig(d.lo),qh=point_trig(d.hi);
    I X=point(x),Y=point(y);
    I vl=X*I(ql.cl,ql.ch)+Y*I(ql.sl,ql.sh);
    I vh=X*I(qh.cl,qh.ch)+Y*I(qh.sl,qh.sh);
    Integer out=std::max(vl.hi,vh.hi);
    // An interior maximum has xcos+y sin>0 and equals hypot(x,y).
    // It has derivative positive at left andnegative at right. Endpoint
    // derivative signs also exclude stationary minima. This is sufficient
    // because aninterval oflength<pi contains atmostone zero of derivative.
    I dl=-X*I(ql.sl,ql.sh)+Y*I(ql.cl,ql.ch);
    I dh=-X*I(qh.sl,qh.sh)+Y*I(qh.cl,qh.ch);
    if(dl.hi>=0 && dh.lo<=0)out=std::max(out,root(square(X)+square(Y)).hi);
    return out;
}
Integer trig_max(I x,I y,I z,I d) {
    // sin(d)>=0 throughoutthedeclared domain, so theupper yendpoint suffices.
    if(d.hi<rational(157,100).lo)return scalar_trig_max(x.hi,y.hi,d)+z.hi;
    return std::max(scalar_trig_max(x.lo,y.hi,d),scalar_trig_max(x.hi,y.hi,d))+z.hi;
}
Integer sat_upper(const Algebra& g,I d) {
    Integer result=INT64_MIN;
    for(int axis=0;axis<4;++axis)for(int sign:{-1,1}){
        Integer best=INT64_MAX;
        for(int sc:{-1,1})for(int ss:{-1,1}){
            I X=rational(2*sign)*g.X[axis]-rational(sc)*g.K-rational(ss)*g.L;
            I Y=rational(2*sign)*g.Y[axis]-rational(ss)*g.K+rational(sc)*g.L;
            I C=rational(2*sign)*g.C[axis]-g.Z;
            best=std::min(best,trig_max(X,Y,C,d));
        }
        result=std::max(result,best);
    }
    return result;
}
bool reject_all_gaps(const Algebra& g,Integer hi,int gap_depth,Integer& worst) {
    if(hi<DMIN.lo){worst=-1;return true;}
    struct D {I d;int depth;};
    std::vector<D> pending{{I(DMIN.lo,hi),0}};
    Integer all=INT64_MIN;
    while(!pending.empty()){
        D n=pending.back();pending.pop_back();
        Integer upper=sat_upper(g,n.d);
        if(upper<0){all=std::max(all,upper);continue;}
        if(n.depth==gap_depth){worst=upper;return false;}
        Integer mid=n.d.lo+(n.d.hi-n.d.lo)/2;
        pending.push_back({I(n.d.lo,mid),n.depth+1});
        pending.push_back({I(mid,n.d.hi),n.depth+1});
    }
    worst=all;return true;
}

void verify_branch(int at,int bt,int as,int bs,uint64_t limit,int selected_a=-1,int selected_b=-1) {
    uint64_t nodes=0,leaves=0;unsigned deepest=0;Integer worstmargin=INT64_MIN;
    auto start=std::chrono::steady_clock::now();
    for(int ap=0;ap<8;++ap)for(int bp=0;bp<8;++bp){
        if(selected_a>=0 && ap!=selected_a)continue;
        if(selected_b>=0 && bp!=selected_b)continue;
        Segment sa=segment(at,as,ap),sb=segment(bt,bs,bp);
        std::vector<PairBox> pending{{enclosed(sa.left,sa.right),enclosed(sb.left,sb.right),0}};
        uint64_t localnodes=0,localleaves=0;
        while(!pending.empty()){
            PairBox b=pending.back();pending.pop_back();++nodes;++localnodes;
            if(nodes>limit)throw std::runtime_error("Node budget exhausted: NO certificate");
            deepest=std::max(deepest,b.depth);
            Algebra g=algebra(sa,sb,b);Integer wx=b.x.hi-b.x.lo,wy=b.y.hi-b.y.lo;
            Integer resolution=std::max(rational(1,10000000).hi,std::max(wx,wy)/16);
            Integer hi=delta_upper(g,rational(GAMMAS[at][bt],1000000),resolution),margin;
            int gap_depth=b.depth>28?12:b.depth>12?6:2;
            if(reject_all_gaps(g,hi,gap_depth,margin)){
                ++leaves;++localleaves;worstmargin=std::max(worstmargin,margin);continue;
            }
            if(b.depth>70){
                std::cerr<<"UNRESOLVED "<<at<<" "<<bt<<" "<<as<<" "<<bs<<" pieces="<<ap<<","<<bp<<" x="<<b.x.lo<<","<<b.x.hi<<" y="<<b.y.lo<<","<<b.y.hi<<" gap_hi="<<hi<<" margin="<<margin<<" scale="<<SCALE<<std::endl;
                throw std::runtime_error("Depth budget exhausted: NO certificate");
            }
            bool choose_x=wx>wy;
            PairBox left=b,right=b;Integer mid;
            if(choose_x){mid=b.x.lo+wx/2;if(mid==b.x.lo)throw std::runtime_error("Resolution exhausted");left.x.hi=mid;right.x.lo=mid;}
            else{mid=b.y.lo+wy/2;if(mid==b.y.lo)throw std::runtime_error("Resolution exhausted");left.y.hi=mid;right.y.lo=mid;}
            ++left.depth;++right.depth;pending.push_back(left);pending.push_back(right);
        }
        if(localnodes!=2*localleaves-1)throw std::runtime_error("Binary cover accounting failed");
        std::cout<<"PIECE "<<at<<" "<<bt<<" "<<as<<" "<<bs<<" "<<ap<<" "<<bp<<" nodes="<<localnodes<<" total="<<nodes<<std::endl;
    }
    std::cout<<"VERIFIED "<<at<<" "<<bt<<" "<<as<<" "<<bs<<" nodes="<<nodes<<" leaves="<<leaves<<" depth="<<deepest<<" margin_upper="<<worstmargin<<"/"<<SCALE<<" seconds="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<std::endl;
}
int main(int argc,char**argv){
 try{
    Integer factorial[20];factorial[0]=1;for(int k=1;k<20;++k)factorial[k]=factorial[k-1]*k;
    for(int k=0;k<10;++k){I sn=rational(k%2?-1:1,factorial[2*k+1]);sine19.push_back(sn);if(k<9)sine17.push_back(sn);I cn=rational(k%2?-1:1,factorial[2*k]);cosine18.push_back(cn);if(k<9)cosine16.push_back(cn);}
    if(argc!=5 && argc!=7)throw std::runtime_error("Usage: verifier at bt as bs [ap bp]");
    int at=std::atoi(argv[1]),bt=std::atoi(argv[2]),as=std::atoi(argv[3]),bs=std::atoi(argv[4]);
    if(at<0||at>3||bt<0||bt>3||std::abs(as)!=1||std::abs(bs)!=1)throw std::runtime_error("Invalid branch");
    int ap=argc==7?std::atoi(argv[5]):-1,bp=argc==7?std::atoi(argv[6]):-1;
    if(argc==7 && (ap<0||ap>7||bp<0||bp>7))throw std::runtime_error("Invalid affine piece");
    verify_branch(at,bt,as,bs,100000000,ap,bp);
    return 0;
 }catch(const std::exception&e){std::cerr<<e.what()<<std::endl;return 1;}
}
