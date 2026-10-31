# An intact petal's shallow adjacent strip has no other boundary neighbor

Date: October 27, 2026.

**Status: accepted complete hand geometric implication after full-source
root and separate independent reviews in
REVIEW_SHALLOW_INTACT_STRIP_AND_C3_333_B1_ROOT_2026_10_27.md and
REVIEW_INTACT_PETAL_SHALLOW_STRIP_HEXAGON_2026_10_27.md.**
This is a reusable restriction at arbitrary true root degree.
It does not close C3.333.b1 or assign a circle-clear status to a higher-
degree articulation without proving its actual contact lies in the
specified strip.

Keep all original nine physical squares and the compatible selected
certificate. Suppose an actual root H has an intact petal H,U,V,
with both tips of true positive degree two. Write

    d=sqrt(R^2-1/4)-1=1+epsilon,
    0<epsilon<1/60,      R<=sqrt(1105)/16.

Suppose H has an actual side whose positive height sigma is at most
epsilon. The intact-origin theorem gives O in int H. The actual common
petal side has height between 1/5 and 39/40, so it cannot be this
shallow side or its opposite side. Choose H's own axes and a reflection
so the actual chart and common petal side are

    H=[-sigma,1-sigma] times [-P,1-P],
    0<sigma<=epsilon<1/60,       1/5<P<39/40,

with the petal on the bottom. Strict transverse straddling supplies
one true port

    p=(-w,-P),       0<w<=sigma,

belonging to U. The other actual petal port has positive horizontal
coordinate. No actual normal or mean is changed by this coordinate
choice.

**Theorem.** P<=11/15. The tip U has exactly one physical circle corner
Z; p and Z are opposite vertices of U. Moreover no distinct physical
circle-touching square can meet H's whole shallow strip

    [-sigma,0] times [-P,1-P].                          (1)

This concerns physical boundary contact even with zero circle weight.
Every other actual unit and all additional forces at H remain.

## 1. Complete low-port classification

If P>11/15, the small-port lemma in Section 1 of
GLOBAL_CLOSURE_INTACT_ROOT_S_LEAF_CENTRAL_DISK_EXCLUSION.md applies
directly and excludes the configuration. That lemma only requires
d>1, the displayed port/height bounds, and the true intact-petal
equations; it does not require an S leaf at H. Therefore

    P<=11/15.                                          (2)

Put r=R-sqrt(2). Since d>1, R>sqrt(17)/2>103/50 and
sqrt(2)<283/200, so r>129/200. The physical boundary-point bound
at p gives P^2+w^2>=r^2. Consequently

    P^2>(129/200)^2-(1/60)^2>(16/25)^2,
    P>16/25.                                           (3)

The last squared surplus is 2213/360000>0.

Write the actual H-to-U normal as n=(-s,-c), s>=0,c>0,
s^2+c^2=1. The same unchanged root-intersection identity used
in the cited small-port lemma gives

    s/c<w/P<5/192<1/38.                                (4)

For completeness, if s=0 the first inequality is immediate. Otherwise
the root pair is nonparallel. Its actual intersection is q_0=-t M,
t>0. With v=(-c,s) and the other actual normal (s',-c'), s'>=0,c'>0,

    p.v=-t M.v=t mu'(c s'+s c')>0.

This is wc-Ps>0, proving (4) for every original owner.

The actual proper loaded-tip concurrence is

    q_U=p+ell n=tau F_U,
    ell>=0, tau>0,

and hence its horizontal-to-downward ratio is at most w/P. Also
|p|^2=P^2+w^2<1<d^2. The complete physical two-circle-corner mask
is radial S with every point of norm at least d; thus that mask
is impossible. U has one physical circle corner. Write it as

    Z=(-X,-Y),       X>=0,Y>0,
    X/Y<=w/P<1/38,   X^2+Y^2=R^2.

In particular R<25/12 gives

    X<25/456<1/18.                                    (5)

The actual port cannot belong to the relative interior of a U side.
In that case n is U's own inward side axis. Put

    p_n=ws+Pc,       p_v=wc-Ps.

Equation (4) gives c>15/16, so p_n>(16/25)(15/16)=3/5,
whereas 0<p_v<=w<1/60. The unique far corner has normal coordinate
p_n+1 and positive transverse coordinate at least 1/2. Positive
radial concurrence instead gives its transverse coordinate at most

    p_v(1+1/p_n)<(1/60)(8/3)=2/45<1/2,

a contradiction. The complete calculation retains the original
support-side interval and makes no midpoint substitution.

Thus p is a U vertex. Since R>2 and |p|<1,

    |Z-p|>=R-|p|>1.

Distances between different unit-square vertices are 1 and sqrt(2).
The vertices p,Z must therefore be opposite. This proves the full
classification, including all possible actual endpoint means.

## 2. The opposite tip vertices pin its center in a narrow vertical strip

Let c_U be U's actual center. Opposite vertices give

    c_U=(p+Z)/2,
    -1/25<(c_U)_x<0,
    (c_U)_y<0,                                        (6)

because (w+X)/2<(1/60+1/18)/2=13/360<1/25.

Every physical boundary-square center c has

    |c|>=R-1/sqrt(2),
    |c|<=d+1/2<91/60.

Throughout the present d>1 domain,

    (R-1/sqrt(2))^2
      >19/4-sqrt(17/2)>1833/1000,                     (7)

using sqrt(17/2)<2917/1000. Combining (6)--(7) gives

    (c_U)_y<-4/3<-37/30.                              (8)

For the first comparison it suffices to square:
1833/1000-1/625>16/9.

## 3. Any other boundary body meeting the shallow strip has a nearby center

Suppose a physical circle-touching square B distinct from U meets
the strip (1) at q=(-z,t), where 0<=z<=sigma. From (3), the
nonnegative-height part of that strip has

    |q|^2<=sigma^2+(1-P)^2
          <(1/60)^2+(9/25)^2<r^2.

No boundary unit can contain such a point. Hence t<0. Put T=-t;
then 0<T<=P<=11/15.

Let c=(c_x,c_y) be B's center. Its circumradius gives
|c-q|^2<=1/2. Suppose c_y>=-37/30. Using (7), the universal center
bound, 0<=z<1/60 and c_x>-91/60, we obtain

    0 >= |c-q|^2-1/2
      = |c|^2-1/2+z^2+T^2+2z c_x+2T c_y
      > 1833/1000-1/2-91/1800+T^2-(37/15)T
      = 5771/4500+T^2-(37/15)T.                       (9)

The last quadratic decreases throughout 0<=T<=11/15, and its value
at 11/15 is

    5771/4500-286/225=17/1500>0.

This contradicts (9). Thus every such B has

    c_y<-37/30,
    |c_x|^2<(91/60)^2-(37/30)^2=2805/3600
                <(53/60)^2.                           (10)

Both c and c_U now have vertical coordinates strictly between
-91/60 and -37/30. Their vertical difference is less than 17/60,
and (6), (10) bound their horizontal difference by

    53/60+1/25=277/300.

Consequently

    |c-c_U|^2<(277/300)^2+(17/60)^2
                  =83954/90000<1.                    (11)

Distinct interior-disjoint unit squares have center distance at least
one, because their open inscribed disks of radius 1/2 are disjoint.
Equation (11) is impossible. This proves the theorem for every point
of the entire closed strip, with no force or load assumption on B.

## 4. Exact intended scope

A distinct genuine leaf root makes an intact-petal root H have some
side of height at most epsilon, since that leaf root meets D_epsilon
and cannot meet int H. A D leaf at the distinct root is already
impossible through O; an S leaf forces d>1. The theorem therefore
applies to the actual small side in this situation.

For the last three-triangle-chain layout of C3.333.b1, write the
triangles H,U,V; H,A,B; A,C,D, with a genuine leaf at C. Then B is
a true loaded degree-two square distinct from U. The theorem proves
that B cannot physically meet the shallow strip of H. This does not
yet route the entire H-A-B interface or prove A circle-clear; those
remaining original owner and load alternatives are retained.

No circle force, normal, actual mean or physical square is removed or
changed. The proof uses no sampled pose, scalar sign packet, numerical
certificate, Lean compilation, CI, or shared-ledger edit.
