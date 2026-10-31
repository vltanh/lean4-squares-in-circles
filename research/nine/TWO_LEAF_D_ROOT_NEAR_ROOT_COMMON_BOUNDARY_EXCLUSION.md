# A D-leaf root cannot balance a near-origin neighbor and their boundary common neighbors

Date: October 27, 2026.

**Status: accepted complete hand proof at its stated original scope; full root and separate independent source/scope reviews passed.**

Accepted reviews: REVIEW_D_ROOT_NEAR_ROOT_COMMON_BOUNDARY_TRIANGLE_BRIDGES_2026_10_27.md and
REVIEW_NEAR_ORIGIN_AND_ATTACHMENT_CLOSURES_ROOT_2026_10_27.md.
Their mathematical-source pins precede this acceptance-only header update. No shared ledger or original checkbox changes here.

Retain all nine original interior-disjoint physical unit squares, their
common compatible selected certificate, and

    79/40 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,
    epsilon=max(d-1,0)<1/60,
    r=R-sqrt(2),                 s=1-r.

Let H have a genuine positive D leaf L. Suppose its other actual
positive neighbors are exactly a unit K and units T_1,...,T_m,
where m>=1. Assume K meets the closed disk D_epsilon, each T_i
physically touches the containing circle, and each T_i physically
touches K. The K-T_i contacts need not have positive stress.

**Theorem.** This entire actual configuration is impossible.

The true positive degree of H is m+2, and its full original equation
is retained. No degree or force equation is imposed on K or the T_i.
All actual means, physical masks, individual zero circle weights,
zero-stress contacts and other physical units remain. In particular the
statement concerns an actual genuine D leaf and actual circle-touching
common neighbors, not units assigned artificial leaf or boundary data.

## 1. The D root and its near-origin neighbor fix a shallow top

The genuine D-leaf theorem and compatible bridge-normal selection in
`RADIAL_BRIDGE_AND_LEAF_REDUCTION.md` put the actual root in the chart

    H=[-s,r] times [a-1,a],             0<a<1,           (1)

with its real leaf L pointing east, its actual radial leaf application
(r,0), and O in int H. Here 0<r<1 and 0<s<1. The strict a bounds
are exactly the fact that the leaf vertex lies in a relative side
interior of H. The original D leaf is retained as an occupied unit.

If epsilon=0, the actual K contains O and overlaps int H. Thus
epsilon>0, d>1 and R>sqrt(17)/2>2. The exact bounds recorded in
`D_LEAF_TWO_DISTINCT_NEAR_ORIGIN_UNITS_EXCLUSION.md`, Section 1,
are

    129/200<r<2/3,
    1/3<s<71/200<3/8,
    0<epsilon<1/60.                                    (2)

They follow directly by positive squaring from the original radius
window; no hypothesis about two other near-origin units is used here.

Choose the actual point x_K in K with |x_K|<=epsilon. Its horizontal
coordinate is strictly between -s and r. It cannot lie in int H.
Consequently either its vertical coordinate is at least a or at
most a-1. Reflect the entire physical configuration vertically if
needed; the D leaf still points east. In this chart

    0<a<=epsilon.                                      (3)

Let n=(n_x,n_y) be the actual unit normal on the positive H-K edge,
directed from H into K, and let h be its actual H support. Since
K lies beyond that support and contains x_K,

    0<h=h_H(n)<=n.x_K<=epsilon.                        (4)

The strict lower bound uses O in int H. If n_y<=0, the root support
formula and (2)--(3) give

    h>=min(r,s,1-a)(|n_x|+|n_y|)>1/3,

contrary to (4). Hence n_y>0. Its exact support is then

    h=r n_x+a n_y       if n_x>=0,
    h=s|n_x|+a n_y      if n_x<0.

Equations (2),(4) therefore give

    |n_x|<1/20,        n_y=sqrt(1-n_x^2)>4/5.          (5)

These are conclusions about the unchanged actual selected normal.
No normal is chosen afresh or made into an H side normal.

The upper-left vertex of H is too near O to belong to any physical
boundary unit:

    |(-s,a)|^2<(3/8)^2+(1/8)^2=5/32<1/4<r^2.         (6)

Indeed every point of a unit with an actual circle corner has norm
at least r, by its own diameter sqrt(2). The deliberately coarser
a<1/8 in (6) follows from (3) and keeps every shallow endpoint.

## 2. Two complete physical-triangle feature facts

For each i the three actual squares H,K,T_i physically touch in
all three pairs. We use two degree-free support consequences of
that physical triangle.

First, if one of H's two actual outward normals is an H side axis,
its scalar product with the other is nonnegative. This is the full
`UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md`, with arbitrary degrees
and genuine common support means.

Second, the two actual H contacts cannot be strictly exposed opposite
vertices. To recall the complete local argument, let n_1 strictly
expose vertex P, and n_2 strictly expose its opposite Q in H. The
two inward unit side axes u,v at P give Q=P+u+v and

    n_1.(P-Q)=|n_1.u|+|n_1.v|>=1,
    n_1.n_2<0.

The strict unit-square support-span lemma at the minimum-n_2 point
Q of the other neighbor gives

    max n_1.(x-Q)<1

over that neighbor. The neighbor beyond P has n_1 projection at
least n_1.P, so the two neighbors cannot touch. This contradicts
the physical triangle. This is the opposite-vertex step of
`END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md`, Section 2, and uses no
tip degree, circle load or external resultant at either neighbor.

The following feature cover applies those two facts to the actual
H-K and H-T_i normals. A side-axis normal retains its full actual
mean. A normal with two nonzero own components strictly exposes the
corresponding H vertex, as usual.

## 3. A positive horizontal H-K component contradicts the full root force

Suppose n_x>0. The H-K contact is the upper-right vertex (r,a).
Write m_i for the actual outward H-to-T_i unit normal. If its
horizontal component were negative, there would be precisely three
possibilities:

- If (m_i)_y>0, its H contact is the upper-left vertex, forbidden
  for the boundary T_i by (6).
- If (m_i)_y=0, m_i=-e_x is an H side axis and n.m_i=-n_x<0,
  contradicting the physical-triangle side-normal fact.
- If (m_i)_y<0, its H contact is the lower-left vertex, strictly
  opposite the H-K vertex. The opposite-vertex fact excludes it.

Thus every actual m_i has (m_i)_x>=0. The physical D root H is
circle-clear because O lies in its interior and every H point has
norm at most sqrt(2)<R. Its complete unchanged force equation is

    lambda e_x+mu n+sum_i nu_i m_i=0,
    lambda,mu,nu_i>0.                                  (7)

The horizontal component of its left side is at least
lambda+mu n_x>0, a contradiction. This excludes the entire n_x>0
domain, without using any force equation at a common neighbor.

## 4. An exact cap excludes a downward lower-left boundary contact

We establish the geometric fact needed for n_x<0. Write

    n=(-t,k),       0<t<1/20,       k>4/5,
    t^2+k^2=1.

Then the H-K contact is the upper-left vertex (-s,a), and

    h=ts+ka.

Suppose some boundary common neighbor T has its actual H contact
at the lower-left vertex

    P=(-s,a-1)

with a strictly southwest outward H normal m=(-u,-v), u,v>0.
The same normal is an inward support normal of T at its actual
point P. An actual point Y in T intersect K satisfies

    n.(Y-P)>=h-n.P=k.                                  (8)

We show that every point of this T has norm strictly less than two,
contradicting its physical circle contact at R>2.

### 4.1. Complete own-feature description of T at P

The point P cannot lie in int T. If it is a T vertex and neither
of its two actual inward side axes has a positive vertical component,
every point X of T has X_y-P_y<=0. Then

    n.(X-P)<=t|X_x-P_x|<=t sqrt(2)<k,

contrary to (8). Thus in the vertex case there is an inward upward
axis. Because m is strictly southwest, that axis must be up-left;
its orthogonal inward partner must be down-left, since the other
choice points northeast and has negative scalar product with m.

If P is in a relative side interior of T, its inward side-normal
axis is the actual m, which is southwest, and its up-left tangent
can be oriented as the first axis below. Endpoints of the side are
included by the same parametrization. Consequently every surviving
case has the exact actual form

    w=(-alpha,beta),       z=(-beta,-alpha),
    alpha>=0, beta>0,      alpha^2+beta^2=1,
    T=P+[-tau,1-tau]w+[0,1]z,           0<=tau<=1.     (9)

The vertex alternative has tau=0. The side alternative retains its
whole original slider tau. No supporting point has been moved to
an endpoint to obtain (9).

### 4.2. The full n-span forces alpha<1/8

Here n.w=t alpha+k beta>0 and n.z=t beta-k alpha. The true maximum
of n.(X-P) over (9) is

    (1-tau)(t alpha+k beta)+max(t beta-k alpha,0).

By (8) this is at least k. If t beta-k alpha>0, then
alpha<t/k<1/8. Otherwise

    t alpha+k beta>=k.

For alpha>0, use 1-beta=alpha^2/(1+beta) to obtain

    alpha<=t(1+beta)/k<=2t/k<1/8.                      (10)

For alpha=0 the same strict final bound is immediate. The last
comparison in (10) uses t<1/20 and k>4/5. Thus the entire actual
orientation interval has alpha<1/8; it is not an angle sample.

### 4.3. The full side slider also satisfies tau<1/8

The actual Y from (8) and the diameter of T give

    Y_y-P_y>=1+(t/k)(Y_x-P_x)
             >=1-(t/k)sqrt(2)
             >1-(1/20)(5/4)(3/2)=29/32.

Every point of (9) has vertical increment at most
(1-tau)beta<=1-tau. Therefore

    tau<3/32<1/8.                                     (11)

This covers an arbitrary genuine shared-side mean at P, including
both endpoint cases when physically feasible.

### 4.4. The whole original T lies inside the radius-two disk

For any X in (9), equations (10)--(11) give

    -9/8<X_x-P_x<1/64,
    -1/4<X_y-P_y<=1.

Together with (2)--(3) and P=(-s,a-1), these imply

    -3/2<X_x<0,
    -5/4<X_y<1/60.

Consequently

    |X|^2<(3/2)^2+(5/4)^2=61/16<4<R^2.               (12)

Every point, including every actual vertex of T, is strictly inside
the containing circle. This contradicts the assumed physical boundary
status of T and proves the complete lower-left cap exclusion.

## 5. The remaining H-K normals contradict vertical force balance

If n_x=0, then n=e_y is an actual H side normal. The physical-
triangle side-normal theorem gives (m_i)_y>=0 for every i. The
vertical component of (7) is at least mu>0, impossible.

Finally suppose n_x<0. Its actual H contact is upper-left. If any
m_i had negative vertical component, the complete three-feature
cover would be:

- If (m_i)_x>0, its H contact is the strictly opposite lower-right
  vertex, excluded by Section 2.
- If (m_i)_x=0, m_i=-e_y is an H side axis with n.m_i=-n_y<0,
  again excluded by Section 2.
- If (m_i)_x<0, its H contact is the lower-left vertex with the
  strict southwest normal. Section 4 excludes this whole boundary
  common-neighbor geometry, with every actual T_i side slider.

Thus (m_i)_y>=0 for all i. The vertical component of the unchanged
full root equation (7) is at least mu n_y>0, a contradiction.

Sections 3 and 5 exhaust every actual normal n, while Section 1
already excluded epsilon=0. This proves the entire theorem across
the original radius, mean, mask and force domain.

## 6. Exact two original distinct-root diamond gates

Use the standard diamond labels H,K for its hubs and B,C for its
tips, with all five positive edges HK,HB,HC,KB,KC.

### 6.1. One S and one D leaf at the two hubs

For the original family

    M6.B4L2.DIAMOND.TWO_HUBS.LBC.SD,

name the D-leaf hub H and the S-leaf hub K, exchanging the hubs
if necessary. The genuine S-leaf-root theorem puts this same K in
contact with D_epsilon. Its actual true degree remains four.
The tips B,C have true positive degree two and physically touching
neighbors H,K, so both are positively loaded and physically boundary.
Each touches both hubs through its original positive edges.

The complete positive neighbor list of the D root H is its genuine
D leaf, K, B and C. The theorem applies with m=2, retaining H's
true degree four and every other original force. This closes the
entire SD family, including both symmetry-identified placements,
all genuine leaf geometries, weights, means and all three extras.

### 6.2. An S leaf at a hub and a D leaf at a tip

For the original family

    M6.B4L2.DIAMOND.HUB_TIP.LKC.SH_DB,

the S leaf is at H and the D leaf is at B. Apply the theorem with
its D root equal to this actual tip B, its near-origin unit equal
to the actual S root H, and its sole common boundary neighbor equal
to the actual other hub K.

The complete true positive neighbor list of B is H, K and its
genuine D leaf, so its true degree three is retained. The other
hub K has its true degree three and is loaded by
`NO_UNLOADED_DIAMOND_HUB.md`: its actual neighbors H,B,C contain
the physical contacts HB and HC. That theorem permits all original
additional forces at H and B. Equivalently K's positive load is
part of the unchanged original LKC load cover. K physically touches
both B and H through their actual positive edges.

All theorem premises hold with m=1. Thus this entire SH_DB family
is excluded, including every physical mask, original force ratio,
shared mean and arbitrary remaining square.

## 7. Scope retained beyond these two gates

The theorem is a genuine arbitrary-neighbor-degree implication, but
its complete H neighbor-list hypothesis is essential. In the sibling
DH_SB family the D root is the hub and has another positive boundary
neighbor that is not known to touch the near-origin S-root tip;
that additional force may not be discarded. The proof above does
not close that sibling, the SS siblings, or the distinct-root C4
families. No whole layout or coarse cell is asserted closed here.

The manuscript uses complete physical support features and exact
rational margins. It adds no coefficient packet, sampled orientation,
normal reselection, smaller-degree equation, secondary minimizer,
Lean compilation, CI or remote action. Independent review is required
before the two unchanged existing child gates are recorded closed.
