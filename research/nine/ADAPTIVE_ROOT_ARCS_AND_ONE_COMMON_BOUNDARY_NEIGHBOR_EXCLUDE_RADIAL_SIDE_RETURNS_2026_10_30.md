# Adaptive genuine-root arcs and one common boundary neighbor exclude an entire radial side-return range

Date: October 30, 2026 UTC. Author: common_certificate continuation.

**Status: complete proposed physical theorem, frozen for separate full
independent review.** The main theorem constrains two real genuine leaves
simultaneously using their one actual common boundary neighbor. Its
radial-return corollary covers the entire continuous range g>4epsilon
in both stated South-root charts. No force equation at a root is reduced.
The complementary g<=4epsilon and unique-corner domains are not declared
closed here, and no original parent or flag changes.

## 1. Actual geometry and exact statements

All units below are unchanged actual closed unit squares in one disk
D_R centered at O=0, with pairwise disjoint open interiors. Put

    sqrt(17)/2<R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1=1+epsilon,
    0<epsilon<1/60.                                      (1.1)

Let A,B,C be three distinct genuine S-leaf roots, with their three
distinct actual leaves, each different from all three roots. The
complete physical genuine S geometry is retained: for X=A,B,C, its
actual leaf is

    L_X=[d,d+1]e_X+[-1/2,1/2]Je_X,                      (1.2)

and d e_X is an actual maximum-e_X support point of the full X.
Here J denotes counterclockwise rotation by pi/2. Thus epsilon e_X
belongs to X, by the actual unit inward segment at that support point.
All three roots meet the same closed D_epsilon. In original callers
each root may have any true positive degree; no root equilibrium is
assumed to be a two- or three-force equation in this manuscript.

Assume A has the actual own-axis chart

    j=Jm,
    A=[-g,1-g]m+[-b,1-b]j,
    4epsilon<g<1/2,
    1-epsilon<=b<=d.                                    (1.3)

Let N be one actual physical boundary square touching both B and C,
distinct from L_B and L_C. A zero individual or total circle coefficient
at N is permitted. The B--N and C--N contacts need not carry positive
forces. Every owner, shared segment, mean endpoint and additional actual
contact remains. Define

    rho=min(g,1/4),
    eta=asin(epsilon/rho),
    e_0=-j.                                             (1.4)

We measure lifted angles counterclockwise from e_0, so m has angle pi/2.

**Theorem 1 (one common neighbor constrains both real leaves).** After
possibly interchanging the names B,C, their actual real leaf axes have
angles satisfying

    pi/2-eta <= angle(e_B) <= pi/2+3eta,
    3pi/2-3eta <= angle(e_C) <= 3pi/2+eta.                (1.5)

This is a physical theorem. It uses the full original leaves and one
unchanged common square N, not a virtual boundary point or two different
neighbors satisfying unrelated inequalities.

For the stronger exclusion, suppose there is another actual radial S
unit P, distinct from L_A,L_B,L_C, with

    v=-Ju,
    P=[d,d+1]u+[-1/2,1/2]v,
    r=d u+v/2,
    m=cos(delta)u-sin(delta)v,
    0<delta<pi/2,
    r.m=d cos(delta)-(1/2)sin(delta)=1-g.                (1.6)

In a side-return application r is the actual P corner on the positive
m side of A. The exclusion only needs the actual units and the scalar
relation in (1.6); it does not need a chosen force or a particular side
mean there.

**Theorem 2 (uniform adaptive radial-return exclusion).** The actual
configuration satisfying (1.1)--(1.6) is impossible. It covers all
g>4epsilon under (1.3), all physical contacts and all degrees at A,B,C,N.

## 2. Both B and C have their complete small-vertex charts

Every vertex of A has m-coordinate either -g or 1-g. Both magnitudes
exceed 4epsilon by (1.3). Hence no A vertex is in the closed D_(4epsilon).

The complete force-free three-near-square lemma in [V], Section 1,
therefore makes B and C each have an actual vertex in D_(4epsilon).
Sections 3--4 of [V] apply to their full genuine S geometry and give,
for each X=B,C, perpendicular own unit axes u_X,v_X such that

    X=[alpha_X,1+alpha_X]u_X+[-beta_X,1-beta_X]v_X,
    0<alpha_X<=epsilon,
    0<=beta_X<=4epsilon.                                (2.1)

The actual small vertex is alpha_X u_X-beta_X v_X. The genuine leaf
has precisely one of the following two actual forms:

    aligned: alpha_X=epsilon, e_X=u_X;
    strict:  d e_X=(1+alpha_X)u_X-beta_X v_X.             (2.2)

The signs of the two own frames need not agree. In the aligned case the
transverse direction is chosen toward the far side from the actual small
vertex, as in [V]. In the strict case its sign is fixed by (2.2).

Let gamma_X be the nonnegative angle by which the actual e_X turns from
u_X toward -v_X. It is zero in the aligned case. In the strict case

    sin(gamma_X)=beta_X/d,
    0<=gamma_X<=asin(beta_X/rho).                        (2.3)

The complete chart extraction includes the closed-origin and endpoint
cases; it does not presume a smaller root degree. All far faces in
(2.1) lie beyond the comparison circle because rho<=1/4,
1+alpha_X>1 and 1-beta_X>14/15.

## 3. Exact actual arcs on the one adaptive comparison circle

Since rho>4epsilon, put

    a_X=asin(alpha_X/rho),
    betaAngle_X=asin(beta_X/rho).

For brevity below write a_X and b_X for these two angles. Then

    0<a_X<=eta<asin(1/4),
    0<=b_X<pi/2,
    0<=gamma_X<=b_X.                                    (3.1)

### 3.1. A supplies its full central half arc

In the (e_0,m) frame, the actual A is

    [b-1,b]e_0+[-g,1-g]m.

Every point z of |z|=rho with z.e_0>epsilon lies in int A. Indeed
b-1<=epsilon<z.e_0<=rho<b, and |z.m|<rho<=g while 1-g>rho.
The strict transverse inequality also holds at rho=g because
z.e_0>epsilon>0. Thus the other two squares' open arcs must lie in
the one complementary lifted interval

    I=[pi/2-eta,3pi/2+eta].                             (3.2)

No assumption that A occupies only this arc is made.

### 3.2. The two possible own-frame orders

For each X=B,C its entire open-square intersection with |z|=rho is
one connected open arc. Only its two near faces cut that circle.
There are exactly two possible frame orders, expressed using the
first own-axis angle theta_X:

| Order | First axis at theta_X | Second axis | Complete actual open arc | Actual real leaf angle |
| --- | --- | --- | --- | --- |
| F | u_X | v_X=Ju_X | (theta_X-b_X, theta_X+pi/2-a_X) | theta_X-gamma_X |
| S | v_X | u_X=Jv_X | (theta_X+a_X, theta_X+pi/2+b_X) | theta_X+pi/2+gamma_X |

These formulas follow directly from z.u_X>alpha_X and
z.v_X>-beta_X. In both cases the length is

    ell_X=pi/2-a_X+b_X>=pi/2-eta.                        (3.3)

Choose the B,C naming so B's arc precedes C's in I. Write their
endpoints as L_B,U_B,L_C,U_C and their intervening gap as

    G=L_C-U_B>=0.

Open interiors are disjoint, so endpoint contact is allowed but the
arcs cannot overlap. The exact total spare length gives

    G+b_B+b_C<=2eta+a_B+a_C<=4eta.                       (3.4)

Using (3.2)--(3.3) also gives

    pi/2-eta <= L_B <= pi/2+3eta,
    pi-2eta <= U_B <= pi+2eta,
    pi-2eta <= L_C <= pi+2eta,
    3pi/2-3eta <= U_C <= 3pi/2+eta.                     (3.5)

These are actual simultaneous occupied arcs, not independently moved
comparison squares. Full side and vertex tangencies are included.

## 4. One unchanged N excludes three of the four frame assignments

The complete one-tenth physical cap [C], Sections 1--5, applies to each
chart (2.1)--(2.2), since beta_X<=4epsilon<1/10. Its full normal cover
keeps the actual real leaf and puts every other physical boundary
neighbor in its Northwest cap. Undoing the coordinate interchange of
[C], Section 4, gives for the same center Z=c_N

    Z.v_X>29/25,
    |Z.u_X|<2/3,
    |Z|<91/60.                                         (4.1)

For clarity, the cap's five exact lower longitudinal constants are
97439/82800, 198367/169200, 201937/172800, 205591/176400 and
41867/36000. Their respective positive differences from 29/25 are

    1391/82800, 419/33840, 1489/172800,
    967/176400, 107/36000.

The largest allowed negative transverse magnitude is 127/200<2/3,
and the largest positive magnitude is 341/1000<2/3. Thus (4.1)
follows from the full cap, without selecting a favorable row or owner.

Also 4eta<4asin(1/4)<pi/2: sin(pi/8)>1/4, which follows by
squaring sin(pi/8)=sqrt(2-sqrt(2))/2. All cosine signs below are
therefore positive.

### 4.1. The F,F assignment

Let Delta=theta_C-theta_B-pi/2. The actual gap formula is

    Delta=G+b_C-a_B.

Equation (3.4) gives -eta<=Delta<=3eta. The actual own directions
satisfy

    v_C=-cos(Delta)u_B-sin(Delta)v_B.                    (4.2)

If Delta>=0, (4.1)--(4.2) give Z.v_C<2/3. If Delta<0, they give

    Z.v_C<2/3+(91/60)sin(eta)
          <2/3+91/240=251/240<29/25.                   (4.3)

The last reserve is 137/1200. Both cases contradict C's cap in (4.1).

### 4.2. The S,S assignment

Define Delta in the same way, with theta_X now the angle of v_X.
The exact gap formula becomes

    Delta=G+b_B-a_C,
    -eta<=Delta<=3eta.

Here

    v_C=cos(Delta)u_B-sin(Delta)v_B.

The same two cases yield exactly the bound (4.3), again impossible.
No reflection of the possibly asymmetric actual A was used.

### 4.3. The S,F assignment

Now theta_B is the angle of v_B and theta_C the angle of u_C.
The actual gap identity is

    theta_C-theta_B=pi/2+T,
    T=G+b_B+b_C,
    0<=T<=4eta<pi/2.

Consequently

    v_C=-cos(T)v_B-sin(T)u_B.

The first component of its scalar product with Z is nonpositive,
and the second is less than 2/3. Thus Z.v_C<2/3, contradicting
(4.1). This includes both nearly coincident West leaf directions;
no coarse center-distance estimate is needed.

### 4.4. The only remaining F,S assignment

B has order F and C has order S. Using the actual leaf angles in
the table, the endpoint bounds (3.5) and 0<=gamma_X<=b_X gives

    angle(e_B)=L_B+b_B-gamma_B>=pi/2-eta,
    angle(e_B)=U_B-pi/2+a_B-gamma_B<=pi/2+3eta,
    angle(e_C)=L_C+pi/2-a_C+gamma_C>=3pi/2-3eta,
    angle(e_C)=U_C-b_C+gamma_C<=3pi/2+eta.

This proves Theorem 1 with both actual genuine-leaf owners retained.

## 5. The full continuous adaptive angle inequality

Put

    phi=atan(1/(2d)).

For the unique delta in (1.6), we prove throughout 4epsilon<g<1/2

    delta+3asin(epsilon/min(g,1/4))<2phi.                (5.1)

The proof is continuous over the whole interval, including the limit
g down to 4epsilon. There is no pose or angle sampling.

### 5.1. The range g>=1/4

Set delta_0=pi/2-2phi. The double-angle formulas give

    d cos(delta_0)-(1/2)sin(delta_0)=1/2.

The left side decreases strictly on (0,pi/2). Since 1-g>1/2,
we have delta<delta_0. Also

    asin(4epsilon)<asin(1/15)<1/14,
    phi>=atan(30/61)>91/200>9/20.

The exact comparisons proving these constants are recorded in
Section 5.3. Using pi<22/7,

    pi/2+3/14<25/14<9/5<4phi.

It follows that delta+3asin(4epsilon)<2phi, proving (5.1) here.
This also controls the g=1/4 endpoint of the next interval.

### 5.2. The full interval 4epsilon<=g<=1/4

Hold epsilon fixed. Set

    K(g)=sqrt(d^2+1/4-(1-g)^2),
    f(g)=delta(g)+3asin(epsilon/g).

Differentiating the exact relation in (1.6) gives

    delta'(g)=1/K(g),
    f'(g)=1/K(g)-3epsilon/(g sqrt(g^2-epsilon^2)).       (5.2)

Thus f' has the sign of H(g)-3epsilon, where

    H(g)=g sqrt(g^2-epsilon^2)/K(g).

The function H is strictly increasing on this entire closed interval.
Indeed logarithmic differentiation reduces that assertion to

    (2g^2-epsilon^2)K^2
       >(1-g)g(g^2-epsilon^2).                         (5.3)

Here K^2>1/4 and epsilon^2<=g^2/16, so the left side is greater
than 31g^2/64. The right side is at most g^3<=g^2/4. Hence
(5.3) has a strict positive margin. The derivative f' can change
sign only from negative to positive. Therefore f has no interior
maximum and is bounded by its two endpoint values. This conclusion
includes the case of no critical point.

The upper endpoint was handled in Section 5.1. At g=4epsilon the
defining equation is

    (1+epsilon)cos(delta)-(1/2)sin(delta)=1-4epsilon.

Its delta increases with epsilon, since

    d(delta)/d(epsilon)=(4+cos(delta))/K>0.

At the analytical endpoint epsilon=1/60, delta<3/20. Also
asin(1/4)<253/1000. Consequently

    f(4epsilon)<3/20+3(253/1000)
                 =909/1000<91/100<2phi.                (5.4)

Both endpoint values are strictly below 2phi, proving (5.1) for
the entire interval.

### 5.3. Exact endpoint reserves

All estimates above have direct rational checks. For x=3/20, use
cos x<=1-x^2/2+x^4/24 and sin x>=x-x^3/6. The reserve

    14/15-[(61/60)(1-x^2/2+x^4/24)-(x-x^3/6)/2]
      =215153/76800000>0

puts the decreasing support function below 14/15 at x, and hence
the corresponding delta below 3/20.

At x=253/1000,

    x-x^3/6-1/4=1805723/6000000000>0,

which proves asin(1/4)<253/1000. At x=1/14,

    x-x^3/6-1/15=129/27440>0,

which proves asin(1/15)<1/14. Finally, at x=30/61 the alternating
arctangent lower bound gives

    x-x^3/3+x^5/5-x^7/7-91/200
      =8414624016623/4399839970429400>0.

These are fixed exact arithmetic checks of a complete analytic proof.

## 6. The actual radial P overlaps an actual real leaf

Two actual radial S units with axes making minor angle theta<2phi
have overlapping open interiors. To see this directly, take their
unit angle bisector e. For lambda just greater than d/cos(theta/2),

    d<lambda cos(theta/2)<d+1,
    lambda sin(theta/2)<1/2,

because d tan(theta/2)<1/2. Thus lambda e belongs to both open
squares. At theta=0 the same conclusion holds for their identical
radial boxes. The argument uses the entire actual squares.

In (1.6) the angle of u is pi/2-delta. Theorem 1 supplies a real
leaf axis e_B within 3eta of pi/2. Therefore its minor angle with
u is at most delta+3eta, which is strictly less than 2phi by (5.1).
The actual P and the distinct actual L_B overlap. This contradicts
the original physical packing and proves Theorem 2.

## 7. Exact conditional Type I caller and remaining scope

The accepted full prefix [P] retains the original graph

    A--P--Q--B--N--C--A,
    optional A--B and B--C,

with the three actual genuine leaves, P and N loaded true-two, Q
physically clear true-two, and all original root degrees. Its radial
P mask has P as in (1.6), with r its actual lower vertex. The A-owned
relative-side-interior branch has the original AP own normal m and
the actual positive-m support r.m.

Whenever a complete A-feature argument supplies either of the charts

    owned South:
      A=[h-1,h]m+[-d,-epsilon]j,
      1/2<h<1, g=1-h>4epsilon;

    strict South-West:
      A=[-g,1-g]m+[-b,1-b]j,
      g^2+b^2=d^2, b>=1-epsilon,
      4epsilon<g<=2sqrt(epsilon),

with 0<delta<pi/2 and h=d cos(delta)-sin(delta)/2, all hypotheses
of Theorem 2 hold literally. In the strict chart g<1/2 follows from
2sqrt(epsilon)<2/sqrt(60)<1/2. Both charts have 1-epsilon<=b<=d.
The same original N touches B,C and is physically boundary because
its original circle load is positive. It is distinct from their
real leaves. The actual P is distinct from all three genuine leaves.

Thus the whole g>4epsilon radial part of both charts is excluded,
without using a force equation at A,B,C or N and independently of
both optional root chords. In particular an A root of degree four
is not treated as degree three, and B may retain both chords.

This manuscript does not supply the complete derivation of these two
A charts from every A-owned feature. That separate feature cover,
the unique-physical-corner P domain and g<=4epsilon are not imported
from unfinished arguments. The theorem is a uniform physical kernel
with the complete conditional caller printed above, not a whole Type I
or C1.6.b3 closure by itself. All actual ninth-square and zero-contact
constraints remain throughout.

## 8. Complete frozen inputs, contributions and verification boundary

| Complete input | SHA-256 | Consumed scope |
| --- | --- | --- |
| [V] THREE_GENUINE_ROOTS_TWO_SMALL_VERTICES_AND_BOUNDARY_NEIGHBOR_BUDGET_2026_10_29.md | a81845be499f5eafb45c796cb057a46c6c85f81e59279fdac6859753079bc98b | Complete three-near physical lemma and full small-vertex genuine S charts; no independent-private graph consequence is needed |
| [RV] REVIEW_THREE_GENUINE_ROOTS_SMALL_VERTICES_AND_NEIGHBOR_BUDGET_ROOT_2026_10_29.md | fa3cfe964c26fa37558b7f9040c7aae86c34f2c4849b48800d985e89cd05aae4 | Existing separate full acceptance of [V] and its operative physical inputs |
| [C] ROOTED_GENUINE_S_LEAF_ONE_TENTH_CORNER_BOUNDARY_CAP.md | 31058df9d4e4ac6eaff1194d2b0d59565349fca885795f284c891537a1be820d | Full actual-neighbor center cap, all owners and endpoints; the five row bounds are used simultaneously for one unchanged N |
| [RC] REVIEW_GENUINE_S_LEAF_ONE_TENTH_BOUNDARY_CAP_C6_NEXT_2026_10_27.md | 38f3b928e8b22cefaa6f2cd65272072c74eafafa4eea17082335c5fd5d1428a4 | Existing separate full acceptance of [C] |
| [P] GENUINE_S_ROOT_RADIAL_RETURN_EXCLUSION_AND_LOADED_ENDPOINT_NORMAL_FORM_2026_10_30.md | 1d86c18a699aa85f1a4d5f1ca4cd32fabd3efd0f0c5dc746fd6b6db85f7a9de7 | Full unchanged Type I graph and radial P lower-corner normal form, only for Section 7's explicitly conditional caller |
| [RP] REVIEW_GENUINE_S_RADIAL_RETURN_AND_LOADED_ENDPOINT_NORMAL_FORM_ROOT_2026_10_30.md | 17da3157d09450208d927ae6354ec11903810adaddc8032ca1954b80ef246c35 | Existing separate full acceptance of the corrected [P] caller and all P masks |

All six complete files were read and their current pins checked. The
new complete arc-order/common-N proof is given in Sections 2--4. The
adaptive radius proposal came from branch_budget during discussion;
the complete continuous inequality in Section 5 was derived here and
independently reconstructed by branch_budget. Such contributor checks
do not replace a separate full noncontributor review of this source.
The root's earlier three-small and boundary-cap review is an input
review, not an advance acceptance of the new adaptive theorem.

No actual square is moved. No force, side mean, chosen normal, circle
atom, true degree, comparison-circle origin or canonical selector is
changed. There is no pose sampling, numerical packing search, new
packing certificate, Lean/Lake run, CI dispatch, remote edit or merge.
Original inventories and the unrestricted theorem/equality remain open.
