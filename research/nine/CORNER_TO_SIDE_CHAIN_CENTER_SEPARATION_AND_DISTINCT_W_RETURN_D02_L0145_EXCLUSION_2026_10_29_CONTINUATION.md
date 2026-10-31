# A corner-to-side unloaded chain separates whole centers and excludes every distinct-W return

Date: October 29, 2026 UTC. Author: hexagon continuation.

**Status: complete proposed hand theorems, frozen for separate full
independent review.** The first theorem is a radius-free geometric
center-separation inequality. It includes every side position of W,
every frame and actual support mean of C, and every forward length
at least one. Its proof uses three scalar products and one squared-norm
identity, with no angular subdivision.

The second theorem excludes the entire distinct-W-axis return feature
of a boundary triangle with a genuine unloaded outgoing path and an
actual physical-boundary unit touching W and C. W, B and C may have
arbitrary full positive degree. The literal D02.L0145 caller retains
all seven original edges, all nine squares, every original force and
mean, and every physical circle corner including zero coefficients.
No complete original L0145 row is declared closed.

## 1. Standalone radius-free center-separation theorem

Work in any fixed orthonormal plane coordinates. Let Q be an actual
point and put S=Q-(1,1). Assume

    a,b>0, a<=b, a^2+b^2=1,
    m=(b,a), r=(a,-b),
    0<=kappa<=1,
    W=Q+[0,1]m+[-kappa,1-kappa]r.                  (1)

Thus Q is any unchanged point of the actual minimum-m side of the
unit W, including either side endpoint. Its original force or mean,
if any, is not changed. No circle, force, load or degree hypothesis
at W is needed for this geometric statement.

Let

    alpha,beta>=0, alpha<=beta, alpha^2+beta^2=1,
    e=(alpha,beta), n=-e, j=(beta,-alpha)=Jn,
    Lambda>=1.                                      (2)

Let C be any actual unit square, of any orientation, with the
unchanged actual minimum-n support point

    A=S+Lambda*n.                                    (3)

A may be an actual vertex, a side-interior point or either endpoint
of an original shared-side mean. Write w,c for the actual centers
of W,C.

**Theorem A.** Throughout this entire domain,

    |w-c|^2 >= 7+3a-2b.                              (4)

In particular,

    3a>=2b  ==>  |w-c|^2>=7,                        (5)

and the useful strict range

    a>3/5, b<4/5  ==>  |w-c|^2>36/5.               (6)

The theorem needs no physical contact between W and C, and no
disjointness premise between them. It does not assert a force
equation at either square. In a physical caller, (3) will be
derived from the genuine unloaded path rather than declared to be
a new U--C edge.

## 2. Complete actual support-point-to-center coordinates

For any actual unit C and any actual minimum-n point A, its center
has a representation

    c-A=rho*n+t*j,
    rho>=1/2, |t|<=1/2.                             (7)

To verify every support feature, first suppose A is a vertex. In
its two actual inward orthonormal axes u,v, write

    n=xu+yv, x,y>=0, x^2+y^2=1.

Since c-A=(u+v)/2, the normal coordinate is rho=(x+y)/2>=1/2.
The transverse coordinate has absolute value |x-y|/2<=1/2.
This includes either axis endpoint x=0 or y=0.

If A is in a side interior, n is the actual inward side axis.
The center lies at normal distance 1/2 and at a transverse
displacement in [-1/2,1/2]. Both side endpoints are already in
the vertex proof, so (7) retains the full closed mean interval.

This is a statement about the actual center and unchanged support
point. Enlarging its possible (rho,t) values to the printed
inequalities does not replace C by a comparison square.

## 3. A single continuous comparison proves Theorem A

Set

    K=(1,1)+(m+r)/2
      =(1+(a+b)/2, 1+(a-b)/2),
    Delta_0=K+(3/2)e-(1/2)j.                       (8)

Both coordinates of K are positive. From (1), (3) and (7), the
actual center difference is

    w-c=K-kappa*r+(Lambda+rho)e-tj
        =Delta_0+u e+v j-kappa*r,
    u=Lambda+rho-3/2>=0,
    v=1/2-t>=0.                                     (9)

We prove that each of the three added directions has nonnegative
scalar product with Delta_0. First,

    Delta_0.e=K.e+3/2>0.                            (10)

Second, alpha<=1/sqrt(2)<=beta and a<=b imply b>=1/sqrt(2).
Using the positivity of both K coordinates gives

    Delta_0.j=K_x beta-K_y alpha-1/2
       >=(K_x-K_y)/sqrt(2)-1/2
       =b/sqrt(2)-1/2>=0.                           (11)

For the third direction put

    C_0=b beta-a alpha>=0,
    S_0=a beta+b alpha>=0,
    C_0^2+S_0^2=1.

Thus C_0+S_0>=1. Since m.r=0, e.r=-C_0 and j.r=S_0,

    Delta_0.(-r)
      =b-a-1/2+(3/2)C_0+(1/2)S_0
      =b-a+[3C_0+S_0-1]/2>=0.                      (12)

All these inequalities include a=b, alpha=beta, alpha=0 and
both endpoint side positions kappa=0,1. No derivative or angle
subdivision is needed.

If E=u e+v j-kappa r is the actual increment in (9), equations
(10)--(12) and u,v,kappa>=0 give Delta_0.E>=0. Hence

    |w-c|^2=|Delta_0+E|^2
            >=|Delta_0|^2.                          (13)

Cross terms between the three added directions need no sign
assumption: they are contained in the nonnegative term |E|^2.
This is why all actual side positions and all terminal frames
are treated simultaneously.

The remaining squared norm is exact:

    |K|^2=5/2+2a,
    |Delta_0|^2
      =5+2a+(4+2a+b)alpha+(2+a-2b)beta.             (14)

Let A_*=4+2a+b and B_*=2+a-2b. Since b<=1 and a>0,

    A_*>B_*>0, alpha+beta>=1.

Consequently

    A_*alpha+B_*beta>=B_*(alpha+beta)>=B_*,

and (13)--(14) give |w-c|^2>=7+3a-2b. This proves the
whole radius-free theorem, including the closed threshold in (5).
In (6), 3a-2b>9/5-8/5=1/5, so the strict bound is 36/5.

## 4. Every genuine unloaded path supplies the actual final point

The geometric theorem has the following literal force interpretation.
Let U be the actual axis-aligned unit

    U=Q+[-1,0]^2,

and suppose its original outward normal toward its actual neighbor
T_1 is n=-(alpha,beta), with alpha,beta>0. Its actual U application
is then exactly S=Q-(1,1). Assume the real positive path is

    U-T_1-T_2-...-T_m-C, m>=1,                      (15)

where every T_i is unloaded with exactly its two displayed positive
neighbors. No force at a larger-degree unit is discarded. Every
T_i, its original incoming/outgoing points or means, and every
physical circle corner with zero coefficient remain.

For any such actual T_i, full force balance makes its original
outgoing normal equal to the original incoming normal n and the
two magnitudes equal. Full torque about the origin gives

    P_i-P_(i-1)=ell_i*n,

where ell_i is its positive physical width. The complete actual
unit calculation gives ell_i=1 for side transmission and ell_i=sqrt(2)
for diagonal transmission. In the side case the original means have
matching transverse coordinates; neither endpoint is discarded.

Applying these unchanged equations successively gives the original
final C application

    A=S+Lambda*n,
    Lambda=sum_i ell_i>=1.                           (16)

The actual edge into C makes A a minimum-n support point of the
real C. Thus (3) follows literally. This is an identity along the
actual path, not a contracted direct U--C force. No load, boundary
mask, degree or equilibrium premise at C is needed by Theorem A.

The high-radius application below does not require first proving
that T_1 is a side transmitter or that m=1. Every genuine unloaded
path length and every internal side/diagonal orientation already
satisfies (16). The low/critical theorem will be used only for its
entire low/critical exclusion, not to manufacture the high argument.

## 5. The entire window bridge-clearance consequence

The wider force-free bridge-center theorem in afb1c5ae and its
separate full review have already been frozen. For completeness,
the exact window corollary used here is rederived in full.

Let actual contained unit squares W,C,B have real contacts B--W
and B--C, with centers w,c,b. Assume

    79/40<=R<=sqrt(1105)/16,
    |w-c|^2>=7.                                     (17)

Every contained unit center z obeys

    |z|<=sqrt(R^2-1/4)-1/2<91/60.                   (18)

Indeed its farthest actual squared corner norm is at least
|z|^2+|z|+1/2, and
(121/60)^2-1041/256=31/57600>0. This is a full actual-frame
bound and retains every physical circle mask.

Each actual contact point and the two half-diagonals give

    |b-w|<=sqrt(2), |b-c|<=sqrt(2).

Put M=(w+c)/2. The exact parallelogram identities yield

    |b-M|^2+|w-c|^2/4
        =(|b-w|^2+|b-c|^2)/2<=2,

    |M|^2=(|w|^2+|c|^2)/2-|w-c|^2/4
          <(91/60)^2-7/4=1981/3600<9/16.           (19)

Thus |b-M|<=1/2 and |M|<3/4, so |b|<5/4. If a
proposed separation exceeded 2sqrt(2), the first identity already
excludes B; no negative square root is used. At the closed threshold
|w-c|^2=7 the strict center bound still gives the strict conclusion.

Every point of the actual B is at distance at most 1/sqrt(2)
from its center. Since 1/sqrt(2)<29/40,

    B subset int D_R,
    |b|+1/sqrt(2)<5/4+29/40=79/40<=R.              (20)

Therefore an actual physical-boundary B cannot touch both W and C
in (17). B's true degree, loads and force equations have not been
used. If it has zero total circle weight but physically touches the
circle, the contradiction is just as valid.

Combining (5) and (17)--(20) gives a broad complete consequence:
in the radius window, any physical-boundary unit joining the two
actual units in Theorem A is impossible whenever 3a>=2b. Every
W side position, final C support mean and genuine unloaded path in
Section 4 is included. No allocation or completion capacity enters.

## 6. The full distinct-W return interface at genuine true degrees

We now state the whole feature theorem without any initial frame
or physical-mask restriction at V, W or C.

Retain actual contained units with the same nine-square radius
window, their disjoint open interiors, the common original physical
certificate, all original positive magnitudes and normals, actual
applications and shared means, and full physical circle masks.
Assume the original positive edges include UV,UW,VW and the genuine
path (15). The complete positive neighborhood of U is exactly
V,W,T_1 and U is unloaded. V is positively loaded true degree two
with complete neighbors U,W. W physically touches the circle and
may have arbitrary full positive degree and circle load. C is the
actual last contained unit with arbitrary full degree and load.

Let B be an actual distinct contained unit physically touching both
W and C and physically touching the containing circle. All its
other actual neighbors and force terms remain arbitrary. In the
literal row these contacts are positive edges, but only their
physical existence is needed here.

The exact original ownership feature is

1. n_UV is an own side axis of U.
2. m=n_UW is an own side axis of W and is not a U axis.
3. r_VW=n_VW is an own W axis, differs from m, and is not a V axis.

**Theorem B.** This entire situation is impossible.

This includes every initial parallel/shared UV alternative and
every physical V or W mask before their local exits. A shared VW
interval would make its normal a V axis and is outside the exact
third feature. Equal W axes, V-owned VW and free VW are separate
features; none is silently renamed to satisfy the statement.

## 7. Literal broad-scope local entry, without a loaded T premise

First suppose R>=sqrt(17)/2. The complete local theorem
MIXED_HUB_AXIS_DISTINCT_W_SIDE_NEAR_ORIGIN_INJECTION.md at
71a5b91d has precisely the four-body hypotheses just stated:
unloaded true U3, loaded true V2, physical-boundary W of arbitrary
degree/load, and an arbitrary actual contained fourth neighbor T.
It does not require T to touch the circle or to be loaded. Apply
it to the actual T=T_1, without changing any path or equation.

For clarity, its complete local support and mask cover is recalled
here. Rotate and reflect the whole configuration so UV points North
and UW points Northeast. Then

    U=[L-1,L] times[H-1,H],
    Q=(L,H), m=(b,a), f=(-a,b),
    a,b>0, a^2+b^2=1.

The UW contact is the strict U vertex Q and the relative interior
of a real W side. The possible W axes for VW other than m are
-m,f,-f. Actual V membership of its UV point excludes -m and f,
so the unchanged original VW normal is exactly -f. The complete
parallel V case, including every shared UV mean, is impossible by
the actual height of that W side.

For the remaining actual V, write

    P=(L-D,H), 0<D<1,
    e_1=(c,s), e_2=(-s,c), c,s>0, c^2+s^2=1.

The full loaded V2 common-application exit and the declared non-V
owner exclude the two inappropriate relative-angle signs. The
actual VW point is M=P+e_1. Full U3 force and torque give

    delta=1-D in(0,1), a<b,
    n_UT is a positive multiple of -(1,q),
    q=a/b+(1-a/b)/delta>1,                          (21)

and its unchanged U point is S=(L-1,H-1). Thus n_UT=-(alpha,beta)
has 0<alpha<beta and meets (2). This deduction uses all three
original U forces, not a transmitter equation at U.

The complete V-mask proof excludes every physically unique corner
and both horizontal physical-two orientations, retaining all zero
coefficient endpoints. It leaves the actual radial physical-two V
in its own e_1,e_2 coordinates about the unchanged origin:

    V=[-1/2,1/2] times[d,d+1],
    P=(-1/2,d), M=(1/2,d),
    d=sqrt(R^2-1/4)-1.                              (22)

Both actual circle corners remain, independent of their coefficients.
The exact relative angle order is

    0<theta_V<theta_W<pi/4,

where e_1=(cos theta_V,sin theta_V) and m=(cos theta_W,sin theta_W).

Put

    g=bc+as>0, h=ac-bs>0, g^2+h^2=1.

In the actual V frame, the whole actual W is

    m=(g,h), r_VW=(h,-g),
    W=M+[-zeta,1-zeta]m+[0,1]r_VW,
    0<zeta<1, tau=1-zeta in(0,1).                  (23)

These strict locations follow from actual relative-interior contacts,
not from choosing new means. The full force-free radial-inner-corner
theorem first treats every W physical mask and then proves its unique
actual circle corner M+tau*m+r_VW. Its exact circle equation is

    d=F(g,tau)
      =(tau^2+tau*g+h)/[2(1+g-tau*h)].               (24)

This is valid for arbitrary W degree and even zero total W circle
load. The local source, its full independent review, and the complete
force-free radial-corner source were read at these exact scopes.
None of the older loaded-T path or pocket conclusions is imported.

## 8. The high/critical circle equation gives a whole slope gap

In the present radius range d>=1. For fixed actual g,h>0, the
denominator in (24) is positive for 0<=tau<=1. The exact derivative
numerator, after removing its positive denominator factor, is

    (2tau+g)(1+g-tau*h)
       +h(tau^2+tau*g+h)>0.

Therefore the actual tau<1 gives

    1<=d=F(g,tau)<F(g,1)
          =(1+g+h)/[2(1+g-h)].                      (25)

The last denominator is positive. Multiplying by it gives

    3h>1+g.                                         (26)

This implies h>3/5. Otherwise h<=3/5 and g=sqrt(1-h^2)>=4/5
would give 3h<=9/5<=1+g, contrary to (26). Consequently g<4/5.

The actual strict angle order in Section 7 gives

    a=sin(theta_W)>sin(theta_W-theta_V)=h>3/5,
    b=cos(theta_W)<4/5,                              (27)

the latter also following from a^2+b^2=1. The sine comparison is
strict on the whole actual first-quadrant interval. It does not
choose an angle or compare a physical W to another orientation.

At the original U-to-W point Q, rewrite its unchanged whole W
in U coordinates with r=-f=(a,-b):

    W=Q+[0,1]m+[-kappa,1-kappa]r,
    0<kappa<1.                                      (28)

It is exactly (1). Reversing the tangent merely changes the
coordinate name kappa for the same actual side position; it does
not move Q or its physical application.

The original n_UT and the full actual path supply (2)--(3) by
(21) and Section 4. Theorem A and (27) now give

    |c_W-c_C|^2>=7+3a-2b>36/5>7.                   (29)

The entire B in Section 6 must therefore be strictly circle-clear
by Section 5, contradicting its physical boundary status. This
excludes every frame, owner, actual mean, physical mask and path
length in the whole distinct-W return feature at R>=sqrt(17)/2.
The equality radius is included: the strict tau<1 in (25) retains
the same strict slope gap there.

## 9. Entire low-radius join and literal D02.L0145 instance

For R<=sqrt(17)/2, the complete corrected boundary-triangle
unloaded-terminal theorem a967bb48 applies literally to Section 6:
U is true unloaded degree three, V is true degree two, V and W
are physically boundary, the original VW edge exists, and the
whole outgoing path has genuine unloaded true-two internal bodies.
C has arbitrary degree and load in that theorem. Its complete
low/critical conclusion excludes all owners and masks in this
domain. Thus the low and high proofs overlap at the critical
radius and leave no gap. This proves Theorem B on the entire
79/40<=R<=sqrt(1105)/16 window.

For the original D02.L0145 row retain exactly

    positive rim: 01,12,23,34,45,50,
    positive chord: 02,
    loads: {0,1,4,5},
    U=2, V=1, W=0, T_1=3, C=4, B=5.               (30)

The actual degrees and loads are

| Unit | True positive neighbors | Actual load status used |
| --- | --- | --- |
| U=2 | 1,0,3 | Unloaded true degree three |
| V=1 | 2,0 | Positively loaded true degree two |
| W=0 | 1,2,5 | Positively loaded true degree three; only physical boundary needed after local entry |
| T_1=3 | 2,4 | Unloaded true degree two, retained as the actual transmitter |
| C=4 | 3,5 | Positively loaded true degree two; the new center proof needs only the actual contained unit and incoming support |
| B=5 | 4,0 | Positively loaded true degree two; only its actual two physical contacts and circle contact are used |

Thus the actual path is 2--3--4. The actual B=5 physically touches
W=0 and C=4 and physically touches the containing circle. It is
loaded and is never assigned an unloaded transmission equation.
No W3 force is shortened. Every original C2/B2 term, physical
circle corner and zero individual coefficient remains.

The exact original owner feature is

    n_21 is a side axis of square 2;
    n_20 is a side axis of square 0 and is not a square-2 axis;
    n_10 is a square-0 side axis distinct from n_20
       and is not a square-1 axis.                   (31)

These are precisely the literal three premises of Theorem B.
It therefore excludes this entire original feature, including
all initially possible V frames and masks. The three additional
actual squares remain throughout; no allocation, channel occupancy,
central-square location or completion capacity is needed by this
contradiction.

The exact graph-preserving reflection of the entire configuration
has the corresponding reflected implication. This statement does
not exchange individual bodies with different true neighborhoods
or claim an unlisted reflected load-set literal.

## 10. Exact progress boundary and reusable scope

Theorem A is independent of circle geometry and of any degree or
force assumption. Its literal actual-path use needs the full
unloaded internal stars and the actual Southwest application;
neither can be supplied by merely drawing an auxiliary path.
Its bridge-clearance corollary applies whenever the actual owner
slope satisfies 3a>=2b, including equality, and a real physical-
boundary B touches both resulting units.

Theorem B obtains the stronger slope uniformly for the **whole
distinct-W-axis** original feature from the actual physical W
circle equation at R>=sqrt(17)/2. It treats arbitrary actual
outside degrees at W,B,C, so larger original components meeting
these literal hypotheses are covered as well. It cannot be
applied after deleting another force from U, V or a path internal
unit. A loaded internal body is not a genuine unloaded path.

For the four-interface L0145 frontier, this resolves the entire
different-W-side subcase of the sole-UV/nonparallel-V/W-owned-only
interface. The equal-W-axis common-side case remains a separate
feature unless a caller independently proves 3a>=2b. The no-U-axis,
perpendicular-axis, and sole-UT shared-contact interfaces also
remain separate. The already reviewed V-owned and parallel-V
features are not used to hide any of those remaining domains.

No whole original fine flag, graph parent, coarse cell or global
nine-square theorem is declared closed by this source. Root
integration and a full independent review of these exact bytes
remain required.

## 11. Exact operative inputs and existing review boundaries

The new radius-free theorem, support-center proof, full path
derivation, exact window bridge corollary and stronger high-radius
slope comparison are proved above in full. The older sources are
used only at these stated scopes:

| Complete source or review | SHA256 | Literal use |
| --- | --- | --- |
| MIXED_HUB_AXIS_DISTINCT_W_SIDE_NEAR_ORIGIN_INJECTION.md | 71a5b91d3a0bc95dd76ae9b663b801aeabc33cc34ffb261402c4f7af224a0242 | Entire local owner/mask and actual W-chart cover, with arbitrary contained T; no loaded-T capacity or near-unit allocation conclusion |
| REVIEW_MIXED_HUB_DISTINCT_W_NEAR_ORIGIN_ROOT_2026_10_28.md | e27238b3fed5b53d5f590442a12bfbdcf48843bf43035802e5309f17fb7551b3 | Separate complete review of the broadened arbitrary-contained-T local theorem and its preserved component chains |
| RADIAL_INNER_CORNER_BOUNDARY_NEIGHBOR_QUARTER_SIDE_BOUND.md | 37f0f207a86a9d2c4ead42edcfaac01c5dbdd4f08bc66e98e41f985adedc4011 | Complete actual W physical mask and circle equation; the only needed tau derivative is rederived above |
| BOUNDARY_TRIANGLE_UNLOADED_TERMINAL_CHAIN_COMPLETE_RADIUS_REDUCTION.md | a967bb48602466727c2b28208f8884d50be96f03a553abaaa42d960661e9ee33 | Entire low/critical radius exclusion at original true U3/V2 and genuine unloaded path scope |
| REVIEW_BOUNDARY_TRIANGLE_UNLOADED_TERMINAL_COMPLETE_RADIUS_REDUCTION_REVIEW_RESUME_2026_10_29.md | f0493ed4912561f48f61a806d7ad20cb832a094a2ff1b43f0258a566bac04623 | Separate complete review of that corrected low/critical/high reduction; only the complete low/critical conclusion is needed here |
| PARALLEL_BOUNDARY_TRIANGLE_TERMINAL_BRIDGE_CLEARANCE_AND_D02_L0145_FEATURE_EXCLUSION_2026_10_29_CONTINUATION.md | afb1c5aeb44ae8667a96ad6feac9b2fc67966a103d14a04359f30b57fa01aaba | Antecedent full geometric bridge-center theorem; its exact window consequence is reproduced independently of any parallel-V hypothesis |
| REVIEW_PARALLEL_BOUNDARY_TRIANGLE_BRIDGE_CLEARANCE_L0145_PENTAGON_GLOBAL_2026_10_29_CONTINUATION.md | f3a743763aa8ea36099607a47b23a9c4d2aaad34c337e517689cabf7739965e5 | Separate full review of that bridge theorem and earlier parallel feature; no parallel chart is imported here |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Original full force/torque, actual support means and true unloaded path identities |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Literal original D02 graph/load set, actual full degrees and three additional units |

Root suggested pursuing the previously proved bridge-center theorem
beyond the parallel feature. Root supplied no new center-separation
inequality or different-W-circle slope argument in this source.
The new full derivation above is the author's continuation. Existing
input authorship and independent component reviews remain separate
from the required new independent review.

No pose search, sampled angle, orientation grid, optimizer, new
computational packing certificate, altered normal, selected mean,
discarded force, suppressed physical corner, shortened true star,
new physical edge, Lean/Lake invocation, build, CI/workflow, ledger
edit, staging, commit, push or remote action was used. Only this
new mathematical source was written.
