# One small central unit excludes three further centers in the three-quarter disk

Date: October 28, 2026 UTC. Author: house_aligned continuation.

**Status: complete proposed uniform force-free hand theorem, frozen for
full root and separate independent review.** The complete closed-domain
theorem below needs no containing-circle radius, force, load, positive
graph, normal selection or common orientation premise. Its final aligned
house consequence is a necessary completion-center restriction, not a
whole-family contradiction.

## 1. Complete physical statement

Let actual unit squares have pairwise disjoint open interiors, with
actual centers measured from one unchanged point O. Suppose one actual
unit A has

    |c_A|<=7/12.

**Theorem.** At most two other actual units have center norm at most
3/4. Equivalently, there cannot be four such actual units consisting
of this A and three distinct further centers in the closed disk D_(3/4).

All radius equalities are included. All square orientations, physical
contact types and additional units are arbitrary. The proof first gives
one angular interval and then rules out its sole equality configuration
by actual unit-square rigidity at center distance one.

## 2. Exact center separation and its rigid equality

Every actual unit square contains its open incircle of radius 1/2.
Consequently distinct actual centers have distance at least one.

We will also use the complete equality fact:

    If two actual unit centers have distance one, their center
    displacement direction is a side axis of both actual units.       (1)

To prove it, choose any closed separating line of the two actual convex
squares, directed from the first to the second by its unit normal n.
If their centers are c,d and their directional halfwidths are h_c,h_d,
then

    1=|d-c|>=n.(d-c)>=h_c(n)+h_d(n)>=1.

Equality holds throughout. Thus n=d-c and both halfwidths are exactly
1/2. For an actual square with orthonormal side directions u,v,

    2h(n)=|n.u|+|n.v|,
    (n.u)^2+(n.v)^2=1.

Their nonnegative absolute values have sum one only when one is zero
and the other is one. Therefore n is an actual side axis of each unit,
proving (1). This auxiliary separating line changes no original selected
force normal; the statement is purely physical.

## 3. All three proposed further centers lie in one closed short interval

Suppose three distinct further actual units E_1,E_2,E_3 had centers of
norm at most m=3/4. Put r=|c_A|. If r=0, the distance from c_A to any
c_E is at most 3/4<1, already impossible. Likewise none of these further
centers is O. All directions used below therefore exist.

For positive radii x,y, define

    f(x,y)=(x^2+y^2-1)/(2xy).

When 0<x,y<1 this function is strictly increasing in either variable.
For example its x derivative has the positive numerator x^2-y^2+1.
The cosine law and actual center separation therefore give, for the
minor angle omega between c_A and any c_E,

    cos(omega)<=f(r,|c_E|)
               <=f(7/12,3/4)=-1/9.                         (2)

Put theta=arccos(1/9), so 0<theta<pi/2. Inequality (2) places every
such E direction in the one closed angular interval of halfwidth theta
about the direction opposite c_A. Its total length is 2theta<pi.

For two of these further centers, the same monotonicity gives

    cos(omega_ij)<=f(|c_Ei|,|c_Ej|)
                  <=f(3/4,3/4)=1/9.                       (3)

All directions are distinct: two centers on one ray would have distance
at most 3/4. Ordering the three directions in the interval of (2), both
successive differences are their minor angles because its length is
below pi. Equation (3) makes each difference at least theta.

Their total span is at least 2theta but the containing interval has
length exactly 2theta. Thus every comparison is equality: the outside
two directions are the endpoints of (2), the middle direction is its
midpoint, and the two successive angular differences are exactly theta.

If any of the radius comparisons in (2)--(3) were strict, monotonicity
would make the corresponding angle strict and produce an immediate
span contradiction. Hence the only possible remaining center radii are

    |c_A|=7/12,
    |c_E1|=|c_E2|=|c_E3|=3/4.                           (4)

This includes all original weak radius endpoints rather than removing
them by a generic-position convention.

## 4. The sole center equality cannot be realized by actual units

Rotate the actual coordinates so c_A=(7/12,0). The middle center is
(-3/4,0), and the two outside centers from (2)--(4) are

    E_+=( -1/12, sqrt(5)/3 ),
    E_-=( -1/12,-sqrt(5)/3 ).                            (5)

Indeed cos(theta)=1/9 and sin(theta)=4sqrt(5)/9. Their exact displacement
vectors from c_A are

    v_+=(-2/3, sqrt(5)/3),
    v_-=(-2/3,-sqrt(5)/3),
    |v_+|=|v_-|=1,
    v_+.v_-=-1/9.                                      (6)

By the actual center-distance-one rigidity (1), both v_+ and v_- must
be side axes of the same actual unit A. Two unit side-axis directions
of one square have scalar product in {-1,0,1}. The value -1/9 in (6)
is impossible. Therefore even the sole center equality cannot occur.

This contradiction proves the complete closed-domain theorem.

## 5. Literal aligned S-root completion consequence

Suppose all actual units are contained in the unchanged circle with

    2<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,

and an actual aligned S root and its genuine occupied leaf have

    A=[d-1,d] times [-b,1-b],
    L=[d,d+1] times [-1/2,1/2],
    1/3<=b<=1/2.

This is a whole physical slider interval. No force equation is used in
the consequence once these actual data have been supplied. The exact
radius bounds give

    14/15<d<61/60,
    c_A=(d-1/2,1/2-b),
    0<d-1/2<31/60, 0<=1/2-b<=1/6.

Thus

    |c_A|^2< (31/60)^2+(1/6)^2
            =1061/3600
            =49/144-41/900
            <(7/12)^2.                                (7)

The strict lower d comparison follows from
15/4-(29/15)^2=11/900>0. For the strict upper comparison use
(121/60)^2-(1105/256-1/4)=31/57600>0. The first comparison is
needed only to make the displayed positive horizontal bound literal;
the small-center count itself does not require a containing circle.

In particular, among any three further arbitrary completion units,
at least one has center norm strictly greater than 3/4. If a distinct
already retained core unit D has center norm at most 3/4, then at most
one of those three completions can have center norm at most 3/4, so
at least two completions have center norm greater than 3/4.

The physical boundary units need not be counted as small centers.
Every physical circle-touching unit in this radius interval has center
norm at least R-1/sqrt(2)>1, hence lies outside the three-quarter disk.

For the exact original aligned M6.B5L.HOUSE.HUB.LTCB.S configuration,
the complete source
ALIGNED_S_ROOT_SHALLOW_BOUNDARY_PAGE_EMPTY_CENTER_GAP.md supplies this
slider throughout its whole low, critical and high aligned domains.
Its literal labels are

    edges AT,DT,AD,AB,BC,CD,AL;
    true A4,D3,T2,B2,C2,L1;
    positive circle loads at T,B,C,L.

All original degrees, forces, torques, means, physical masks and zero
individual weights remain. The actual long branch is B--C--D; no BD
contact is added. The three completions cannot all be placed in the
small-center remainder of that source's empty-sector argument. If the
actual D is also small, at least two completions qualify for the broader
centered-arc theorem. A further geometric or capacity argument is still
required to exclude their actual remaining locations.

## 6. Exact inputs and proof boundary

Sections 1--4 are self-contained elementary geometry of actual unit
squares, exact center separation, one monotone cosine-law comparison
and the center-distance-one equality. No computational certificate,
containing radius or force system is a premise.

The original-family entry uses exactly:

| Source | SHA256 | Literal role |
| --- | --- | --- |
| ALIGNED_S_ROOT_SHALLOW_BOUNDARY_PAGE_EMPTY_CENTER_GAP.md | 5681926e8705af07ab4cde28d16e859c42ed8bab71f69e01641844efab47ae0a | Whole original aligned house slider and retained three arbitrary completions |
| FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md | e5c84071363e8dc43b09f9033c7cb3a7684f1de19bcd169d53c9eab55d51963b | Exact original graph, load orbit and true degrees |

The broad centered-arc result has threshold 37/50<3/4; the proved
large-completion conclusions therefore meet that threshold literally.
They do not assert that every completion qualifies, assign physical
boundary status to any clear unit, or locate O in an actual unit.

This theorem and its literal necessary consequence require complete
root and separate independent review before adoption. It grants no
whole original family, parent, coarse-cell, global sharp or equality
closure and no new certificate-retirement count. No numerical pose,
angle mesh, orientation enumeration, generated coefficient table,
Lean/Lake run, CI, force deletion, altered original normal or mean,
checkpoint mutation, staging, commit or remote action was used.
