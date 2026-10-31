# Two S leaves at separate triangle tips are impossible when d<=1

Date: October 27, 2026.

**Status: accepted complete hand proof after full-source root and
separate independent reviews in
REVIEW_TWO_S_TIP_TRIANGLES_LOW_RADIUS_ROOT_2026_10_27.md and
REVIEW_TWO_S_TIP_TRIANGLES_LOW_RADIUS_TRIANGLE_BRIDGES_2026_10_27.md.**
This covers the entire low-radius and exact
critical-radius S/S domain of the remaining no-intact attachment of
C2.33.b2. The high-radius S/S domain d>1 is a separate original
obligation; no whole coarse-cell closure is asserted here.

Keep all original nine physical unit squares, their disjoint open
interiors, the common compatible selected certificate, and

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,       r=R-sqrt(2).

The entire actual positive graph is

    HA,AB,BH, HC,CD,DH, AL,CM.

Both L and M are genuine S leaves. The actual degrees are H4,
A3,C3,B2,D2,L1,M1. A and C are physically circle-clear by their
genuine leaf-root geometry. B and D are loaded: a truly unloaded
degree-two transmitter cannot have its two neighbors physically
touching. H's possible original circle load is retained until its
physical clearance is proved. The other two actual physical squares
remain unchanged and arbitrary.

**Theorem.** This entire original family is impossible if d<=1,
equivalently R^2<=17/4.

We use the exact elementary bounds

    9/10<d<61/60,       |d-1|<1/10,       r>1/2.        (1)

For the first lower comparison,
(79/40)^2-1/4-(19/10)^2=65/1600>0. For the upper comparison,
(121/60)^2-1041/256=31/57600>0. Finally sqrt(2)<57/40 gives
r>11/20>1/2 throughout the original window. Every point of a
physical boundary unit has norm at least r, by comparing it with
an actual circle corner and using the unit diameter sqrt(2).
These statements retain physical circle corners with zero weight.

## 1. A local aligned S-root triangle keeps neither endpoint slider

Consider the actual triangle A,H,B, with the genuine S leaf at A
and B physically boundary. This local section imposes no load or
degree assumption on H. Suppose A is aligned with the leaf. Rotate
the actual leaf direction east and write its whole physical chart

    L=[d,d+1] times [-1/2,1/2],
    A=[d-1,d] times [h-1,h],       0<=h<=1.

The real leaf application is (d,0); its force is alpha e_x with
alpha>0 and has zero origin moment. With the two original outward
triangle normals n_1,n_2, applications p_1,p_2 and positive
magnitudes mu_1,mu_2, A's full equations are

    alpha e_x+mu_1 n_1+mu_2 n_2=0,
    mu_1 det(p_1,n_1)+mu_2 det(p_2,n_2)=0.             (2)

Here are the complete physical normal alternatives. The purely
geometric unit-triangle facts in RADIAL_TRIANGLE_CONCURRENCE.md,
Section1, say that a normal which is an actual A side axis makes
the other normal nonobtuse to it, opposite parallel outward
normals are impossible, and opposite strict A vertices cannot
both be used. These facts include arbitrary neighbor degrees,
free point normals, all actual owners and side means.

An A-owned vertical axis is impossible: the other normal has the
opposite strict vertical sign by (2), contrary to the nonobtuse
side-normal fact. If one normal is horizontal, (2) makes both
horizontal. They have the same outward sign, and the east leaf
forces that sign to be west.

If neither is an A axis, both strictly expose A vertices. Their
vertical components have opposite signs by (2), so the two actual
vertices have heights h and h-1. They cannot be opposite vertices,
and therefore are on one vertical A side. The two right vertices
would make both horizontal triangle forces positive, incompatible
with the east leaf. Thus the vertices are exactly

    p_+=(d-1,h),       p_-=(d-1,h-1).                 (3)

This is an exhaustive actual normal cover, without a new normal
selection or a force equation on H.

**Endpoint-slider lemma.** In this local configuration, 0<h<1.

For the parallel west alternative the actual applications have
heights y_i in [h-1,h], and (2) gives

    mu_1 y_1+mu_2 y_2=0.

At h=0 or h=1 these heights all have one weak sign, so both are
zero. In particular B contains the actual point(d-1,0), of norm
|d-1|<r by (1), contradicting its physical circle contact.

For the nonparallel alternative write the actual top and bottom
normals as

    n_+=(-s,c),       n_-=(-t,-e),       s,c,t,e>0,

and keep their positive magnitudes mu_+,mu_-. Vertical balance
gives mu_+c=mu_-e. In the true origin-moment equation, the common
x coordinate d-1 therefore cancels exactly, leaving

    mu_+ h s-mu_-(1-h)t=0.                            (4)

At h=0 its left side is strictly negative, and at h=1 strictly
positive. Both endpoints are impossible. This proves the lemma
with the entire original side-mean and point-owner domains kept.

## 2. The whole strict low-radius family d<1

Every genuine S-leaf root contains O when d<=1: its actual inward
radial unit segment from d v contains O. This applies in particular
to C, independently of its orientation.

At A, first suppose its genuine leaf direction is not an own side
axis. Then d v strictly exposes an A vertex. Choose the own axes
so v has components a,b>0 with a^2+b^2=1. About the original
circle origin, A is exactly

    [d a-1,d a] times [d b-1,d b].

For d<=1 both d a and d b are strictly between zero and one.
Consequently O is in int A. This already overlaps the distinct
closed C containing O, which is impossible.

In the remaining aligned alternative, Section1 gives 0<h<1.
For d<1 the radial interval [d-1,d] also contains zero strictly.
Thus again O is in int A, while O belongs to C. A boundary point
of one closed unit in another unit's open interior forces open-
interior overlap, since its own interior points approach it.

This excludes the entire d<1 family. It uses A's true three-force
equations and the original physical boundary B, not a reduced
equation at H or a choice of two new parallel root frames.

## 3. The critical radius d=1 retains both roots' side interiors

Now let d=1, so R^2=17/4 exactly. The nonaligned-root argument in
Section2 would still put O in int A and overlap C; exchanging the
two original triangles excludes a nonaligned C as well. Both
actual S roots are therefore aligned with their own genuine leaves.
Section1 applies independently at A and C, using their original
boundary tips B and D. Both transverse sliders are strictly
interior.

Hence O is in the relative interior of the inward side of each
actual root, and locally each root occupies a full half-plane.
Interior disjointness forces those two tangent half-planes to be
opposite: any two nonopposite half-planes through O have an open
angular intersection and would overlap arbitrarily near O.
Because O is a relative side-interior point of both finite squares,
their union therefore contains a full neighborhood of O.

It follows that no third actual unit can contain O. Indeed its
interior points approach O and are two-dimensional; inside that
neighborhood they cannot remain on the single common boundary
line, so some would lie in int A or int C.

We will derive precisely the contrary closed containment O in H.
No strict-origin claim about H is needed.

## 4. The original H application proves physical clearance at d=1

Use A's actual aligned chart

    A=[0,1] times [h-1,h],       0<h<1.

The complete cover in Section1 remains exhaustive. If both triangle
normals are west, their original application heights y_B,y_H have
positive weighted mean zero. Physical circle contact of B gives
|y_B|>=r>1/2. Thus y_H has the strict opposite sign, and the two
heights belong to one interval of length one. Consequently

    |y_H|<=1-|y_B|<=1-r<r.

If the normals are nonparallel, the two actual applications are
the left vertices of (3). Their absolute heights are h and1-h,
whose sum is one. The vertex used by B has absolute height at
least r, so the actual H vertex again has absolute height at
most1-r<r.

In both full alternatives, the unchanged actual AH application
p_H=(0,y_H) has norm strictly below r. It belongs to H. Every
point of a physical boundary unit has norm at least r, so H is
physically circle-clear. This proves vanishing of its actual
circle resultant G_H, including every originally possible
physical corner with zero weight. In the parallel case no mean
has been changed to an endpoint or midpoint.

## 5. Both true triangle aggregates force O into the same closed H

Let N_1 be the positive sum of H's actual outward forces toward
A,B, and N_2 the corresponding sum toward C,D. After Section4's
physical clearance, H's unchanged full degree-four equation gives

    N_1+N_2=0.

For the actual triangle H,A,B, its full external system at H is
N_2, at A the genuine S-leaf force, and at B its original circle
resultant. Summing the original private C,D,M origin moments gives
zero total moment for the H external system. The other moments
are zero directly. The same statements hold for H,C,D, with
N_1 as H's full external resultant. Every actual pair application,
leaf force and circle atom remains in these identities.

TRIANGLE_EXTERNAL_RAY_INTERSECTS_BODY.md therefore applies to each
actual triangle. It makes the closed H meet both opposite
nonnegative rays of N_1 and N_2. If either intersection is O the
conclusion is immediate; otherwise convexity puts the segment
between the two opposite-ray points, including O, in H. Thus

    O belongs to H.

Section3 proved that no third actual unit can contain O. This is
the required critical-radius contradiction, retaining every side
and vertex limit and both arbitrary completion squares.

## 6. Exact original consequence and remaining scope

The two cases d<1 and d=1 cover the complete original S/S domain
with R^2<=17/4 for the graph HA,AB,BH,HC,CD,DH,AL,CM. No higher
degree body is treated as a tip, no possible H circle force is
deleted before physical clearance, and no original load or mean
is replaced. The complete strict high-radius S/S domain d>1
remains separate from this source.

The argument is a human core exclusion and uses no completion
motion or lower-radius numerical certificate. All nine original
physical units remain. No sampled pose, new scalar certificate,
generic normal reselection, Lean compilation, CI, remote write,
or shared-ledger mutation was used.
