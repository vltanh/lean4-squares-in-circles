# Independent full review: the negative-support adjacent-left-vertex diamond

Date: October 28, 2026 UTC. Reviewer: /root/pentagon_audit.

## 1. Exact frozen target, independence, and verdict

**PASS.** I read and independently checked the entire frozen source
ADJACENT_LEFT_VERTEX_BOUNDARY_DIAMOND_NEGATIVE_SUPPORT_EXCLUSION.md,
15,485 bytes, 412 lines, SHA-256

    381fa4a31b27e620025e21eaa39f14342bea8114e926dc1d7f91d6c54da34a13.

I did not construct the theorem, provide construction advice, or edit
its source. The full manuscript was frozen before this independent
audit. I checked the complete physical domain, every vertex/side-owner
alternative, the entire U circle mask, the continuous right-reach
maximum, both complete screen height bands, all original points and
side means, and every closed endpoint. No mathematical blocker remains.

The accepted primary result is a complete force-free exclusion for four
actual unit squares X,U,K,W at the stated negative support, with strict
Northwest and Southwest root-vertex normals and the real U--K and K--W
contacts. It needs no force, torque, degree, load, selected-graph,
radial-leaf or upper-radius premise. Both U and W must physically touch
their common containing circle of radius R>=2.

The separately printed shallow-reach screen is also proved completely.
A whole original low-fan or original S-family caller still requires
its own exhaustive chart/normal cover and independent review. No
whole original gate follows from this kernel alone.

## 2. Exact physical domain and unchanged original points

The actual distinct closed units have pairwise disjoint open interiors
and are contained in the same origin-centered disk of radius R>=2.
In the unchanged orthonormal frame,

    X=[epsilon,epsilon+1] x [-b,a],
    -1/15<=epsilon<=0, a+b=1, 1/3<=b<=21/50.

Thus 29/50<=a<=2/3. The original strict Northwest X-to-U normal
exposes Q=(epsilon,a), and the original strict Southwest X-to-K
normal exposes P=(epsilon,-b). Because the X support points are
unique, the physical intersections with X are exactly {Q} and {P}.
No strictness on the external unit at those points is presumed.

The other premises are the actual contacts U intersect K nonempty,
X intersect W nonempty, K intersect W nonempty, and the entire
support W subset {y<=-b}. Both U and W physically touch the
containing circle. There is no inferred positive coefficient for
any additional contact, no degree bound, and no chosen mean.

The main proof includes epsilon=-1/15, epsilon=0, both b endpoints,
and R=2. A West-axis X-to-K normal is a different domain and is
not silently included in this strict Southwest root feature.

## 3. The complete shallow-reach screen: all frames and point positions

The screen treats an actual unit V with

    min_V y=b, 1/3<=b<=21/50, -1/15<=epsilon<=0,

an actual minimum-height point (x,b) with x>=epsilon, and another
actual point with x coordinate at most epsilon+D. Its complete
reach premises are

    0<=D<=27/1000,
    b>=81/200 implies D<=1/500.

The two points may be side means, endpoints, or the same point.
No upper bound on the first point's x coordinate is assumed.

For an aligned V=[z,z+1] x [b,b+1], actual membership gives
epsilon-1<=z<=epsilon+D. Since D<1/15, all corner x coordinates
have magnitude at most 16/15; heights lie between zero and 71/50.
Thus their squared norms are at most

    (16/15)^2+(71/50)^2=70969/22500<4.

This includes every location on the full minimum side.

Otherwise (x,b) is the actual unique lowest vertex, and the full
nonaligned frame is

    u=(p,q), v=(-q,p), p,q>0, p^2+q^2=1,
    V=(x,b)+[0,1]u+[0,1]v.

Resolving the actual second point in this frame gives exactly

    epsilon<=x<=epsilon+D+q.

The actual point and its mean have not moved; this interval is a
necessary consequence of membership and its printed x bound.

## 4. Whole-frame inequalities and the first three actual corners

The complete frame satisfies p+q<=sqrt(2)<17/12. I checked the
two sum-of-squares identities directly:

    13/8-(p^2+2pq)=((13q-8p)^2+p^2)/104>0,
    13/8-(q^2+2pq)=((13p-8q)^2+q^2)/104>0.

These hold on the entire nonnegative quarter-circle, with strict
positive right sides even at its axis endpoints. The aligned
physical frames were already treated separately.

Write B=21/50 and E=1/15. At the lowest corner, the full x interval
gives |x|<=16/15: its lower endpoint is at least -E and its upper
endpoint is at most 1+D<16/15. Thus

    |(x,b)|^2<=29569/22500<4.

At the left adjacent corner (x-q,b+p), the x interval is
[epsilon-q,epsilon+D], contained in [-16/15,16/15], and its
height is at most 71/50. The same 70969/22500 bound applies.

At the right adjacent corner (x+p,b+q), the possible negative
lower endpoint has magnitude at most E, while p+q>=1. Therefore
the full sign-inclusive bound is |x+p|<=D+p+q. Expansion gives

    |(x,b)+u|^2
       <D^2+(17/6)D+1+B^2+13/8+2B
       <=3718629/1000000<4.

I checked the exact final total at D=27/1000. Its positive
reserve is 281371/1000000. No sign of the original x+p is
assumed in squaring the bound.

## 5. Opposite corner, both x endpoints, and both closed height bands

The last corner is Z=(x+p-q,b+p+q). Its squared norm is convex
in the original x, so the complete interval is controlled by its
two scalar endpoints. These are comparison values, not new
physical positions of V.

At x=epsilon, the exact expansion is

    |Z|^2=2+b^2+epsilon^2+2b(p+q)+2epsilon(p-q).

Using |p-q|<=1 gives the complete bound

    |Z|^2<=2+B^2+E^2+(17/6)B+2E
            =19711/5625<4.

At x=epsilon+D+q, its first coordinate is epsilon+D+p.
The possible negative sign is expressly retained:

    (epsilon+D+p)^2<=epsilon^2+(D+p)^2
                      <=E^2+D^2+2D+p^2.

Here epsilon<=0, D+p>=0, and p<=1 justify both comparisons.
The remaining complete bound is

    |Z|^2<E^2+D^2+2D+1+b^2+13/8+(17/6)b.

This expression increases in each of the actual nonnegative
parameters D and b. On the entire first band
1/3<=b<=81/200, D<=27/1000 gives

    |Z|^2<17980643/4500000
           =4-19357/4500000<4.

On the entire second band 81/200<=b<=21/50, the required
D<=1/500 gives

    |Z|^2<8999659/2250000
           =4-341/2250000<4.

I checked both rational totals and reserves. The common height
endpoint is included in both estimates; at that endpoint the
hypothesis supplies the stronger D bound, while the first bound
is still a valid weaker estimate. D=0 and both epsilon endpoints
are included. There is no sampled orientation or omitted limiting
side position.

All four actual corners are strictly inside radius two. Their
finite maximum norm is below two, so convexity puts the whole
closed V strictly inside the open radius-two disk.

## 6. Full support-span conclusions and the entire leftward vertex frame

The source rederives the strict unit support-span theorem at every
actual vertex, relative side point, and original mean. If Y is a
minimum-m support and a unit direction w has m.w<0, then the
entire unit has w reach from Y strictly below one. At a vertex
at most one inward orthonormal axis contributes positively and
that component is below one; at a relative side point only the
full tangent interval can contribute, with projected component
strictly below one. Side endpoints are the vertex case.

Applied to U at Q in direction South, and to K at P in direction
North, this gives the exact whole-unit facts

    min_U y>a-1=-b, max_K y<-b+1=a.

These strict inequalities retain the original normals and all
external support features.

For any unit based at the upper point Q as a vertex and contained
in x<=epsilon, the complete frame, including aligned endpoints, is

    Q+[0,1](-c,s)+[0,1](-s,-c),
    c,s>=0, c^2+s^2=1.

Put delta=-epsilon. Since a>=29/50>delta,

    |Q|^2=delta^2+a^2<=101/225<(67/100)^2.

The last exact reserve is 1/90000. Each adjacent corner is at
distance one from Q, so has norm below 167/100<2. For the
opposite corner, expansion gives

    delta^2+a^2+2+2(delta+a)s+2(delta-a)c
       <=(1+delta)^2+(1+a)^2
       <=881/225<4.

The term with c is nonpositive and s<=1 bounds the remaining
positive term. The final reserve is 19/225. This proves the
entire leftward frame is circle-clear, including either aligned
axis endpoint; it cannot be the physical boundary U.

## 7. Both root contacts are forced into genuine external side interiors

At P, X occupies the Northeast tangent quadrant. If P were a
K vertex, its right-angle tangent sector cannot meet that open
quadrant. Every such complete sector is contained in the closed
left half-plane or the closed lower half-plane. This can be
seen by taking its angular start in [pi/2,3pi/2] and splitting
at pi. Because P is a vertex, its whole actual square lies in
the resulting half-plane.

The lower alternative puts K in y<=-b, incompatible with actual
UK and min_U y>-b. The left alternative puts K in x<=epsilon.
Reflecting the actual W in the horizontal axis then supplies
the full shallow screen with D=0: its actual X contact is a
minimum-height point at height b with x>=epsilon, and its
actual K contact has x<=epsilon. W would be circle-clear,
contrary to its physical boundary status.

Thus P is not a K vertex. It is not an interior point either,
since the actual X interior approaches P and would overlap K.
It is a relative K-side-interior point. Its original normal
is therefore the unique actual K side axis, with no reselection.

At Q, X instead occupies the Southeast quadrant. If Q were
a U vertex, its entire sector would put U in the left
half-plane or in y>=a. The left alternative is excluded by
Section 6; the upper alternative cannot touch K, whose whole
height is below a. The same interior-point argument excludes
int U. Thus Q is in a relative U-side interior too.

This is the entire vertex/side/interior cover, with every aligned
vertex endpoint included. The exact actual frames are consequently

    K=P+[0,1]n+[-kappa,1-kappa]j,
    n=(-r,-t), j=(t,-r),
    r,t>0, r^2+t^2=1, 0<kappa<1;

    U=Q+[0,1]m+[-rho,1-rho]k,
    m=(-c,s), k=(-s,-c),
    c,s>0, c^2+s^2=1, 0<rho<1.

All strict parameter signs come from the given strict root
normals and the proved relative side interiors. No force
equilibrium or chosen side mean supplies them.

## 8. Complete U circle-mask inference and both rho bounds

The near-side corners Q-rho k and Q+(1-rho)k are within
distance one of Q, so their norms are below two. The lower
far corner Q+m+(1-rho)k has squared norm convex in 1-rho
on [0,1]. Its endpoint Q+m is also within one of Q; its
other endpoint Q+m+k is the entire leftward opposite corner
already bounded in Section 6. Thus this third corner is
strictly inside radius two for the whole actual rho interval.

A unit physically touching its containing circle has a corner
on that circle: the maximum norm over its convex hull is
attained at a vertex. The other three corners are inside
radius two and hence strictly inside R>=2. Therefore the
sole possible physical circle corner is exactly

    Z_+=Q+m-rho k, |Z_+|=R>=2.

This conclusion concerns the physical mask, independently of
every individual circle coefficient. No second corner is
discarded because its weight might vanish.

The exact displacement length is sqrt(1+rho^2). The triangle
inequality and |Q|<67/100 give

    sqrt(1+rho^2)>=2-|Q|>133/100,
    rho^2>7689/10000>49/64,
    rho>7/8.

The second reserve is 131/40000. In the complete band
b>=81/200, one also has a<=119/200, so

    |Q|^2<=1/225+(119/200)^2<(3/5)^2,

with reserve 551/360000. The same argument gives
sqrt(1+rho^2)>7/5 and rho^2>24/25. Both band endpoints
are included in these strict inequalities.

## 9. The real UK contact and the whole continuous reach maximum

The exact extrema of the unchanged whole units are

    max_K y=-b+kappa r, min_U y=a-(1-rho)c.

Their actual contact implies

    kappa r+(1-rho)c>=1.

Since c<1 and 1-rho>0, this gives kappa r>rho. In particular
r>rho because kappa<1. The complete rightward K reach is

    max_K x=epsilon+D, D=(1-kappa)t>0,
    D<(1-rho/r)sqrt(1-r^2), rho<r<1.

These are whole-square projection statements. No new UK
contact point is selected.

For fixed actual rho in (0,1), I differentiated the full
function on (rho,1):

    d/dr [(1-rho/r)sqrt(1-r^2)]
       =(rho-r^3)/(r^2 sqrt(1-r^2)).

Its derivative is positive up to r=rho^(1/3) and negative
afterward. Both continuous endpoint values on [rho,1] are
zero. Its sole maximum is therefore exactly

    (1-rho^(2/3))^(3/2).

Combining with the strict original reach inequality gives

    D<(1-rho^(2/3))^(3/2).

The first rho bound has

    rho^2>49/64>(91/100)^3,

where the cube reserve is 6027/500000. Thus
rho^(2/3)>91/100 and D<(9/100)^(3/2)=27/1000.
In the complete upper height band,

    rho^2>24/25>(197/200)^3,

with reserve 34627/8000000. Hence
D<(3/200)^(3/2)<1/500. The final squared comparison has
reserve 1/1600000. All quantities are nonnegative, so
the monotone roots and squaring preserve their order.

This covers the entire continuous rho,r,kappa domain,
including every actual UK support owner or mean. It is
one analytic maximum and two exact comparisons, not an
angular subdivision or computational certificate.

## 10. Exact W contradiction and original-caller boundary

The actual X--W contact has y=-b and x>=epsilon, since
W lies below X. It follows that max_W y=-b. Its actual
K--W contact has x<=max_K x=epsilon+D. Reflecting the
whole coordinate description across the horizontal axis
gives precisely the screen's actual unit V, minimum
height b, and two real points.

Section 9 supplies both required D bounds. The screen
puts every actual W corner strictly inside radius two,
contradicting its physical contact with the same circle
of radius R>=2. This closes every configuration in the
printed physical domain, with all four squares unchanged.

For a later fan caller, X=2, K=J and {U,W}={1,3}
have the two actual page--K edges. Either page degree is
allowed by this kernel. The root and hub retain their
true degree four, and page 3 retains degree three.
That caller must still prove the full b interval and
the original strict Northwest/Southwest/South support
cover; neither is asserted automatically here.

For the house, the short page T has DT but the long
branch is B--C--D without an original BD edge. This
kernel does not manufacture the required second page
contact or shorten that branch. No whole original
fan/house family, coarse gate or count closes by this
review alone.

## 11. Exact input and verification boundary

The sole direct source is
UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md, SHA-256

    b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207.

Its current complete bytes match the target's pin. I read
it in full in this continuous independent audit; the exact
support-span argument required here is also completely
reproved in the target. No triangle force equation is
imported into this force-free theorem.

The earlier negative-support low-transverse screen is
not a dependency of this manuscript's fully printed
shallow-reach screen. The author/root discovery disclosure
does not include this reviewer. The review's conclusions
cover the entire new source, not a restricted sampled
region or a provisional subset of its feature cover.

This audit uses complete reading and hand geometry/algebra,
plus read-only hashes for exact identity. It uses no
numerical pose, angle mesh, geometric exclusion certificate,
mathematical checker, Lean/Lake, CI or workflow. It changes
no frozen source, old review, saved checkout, metadata,
original flag or count, and performs no stage, commit,
merge or remote write. Only this complete review is new.
