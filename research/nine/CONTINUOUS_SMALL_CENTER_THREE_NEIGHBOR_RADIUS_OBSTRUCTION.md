# A continuous radius obstruction for three centers around one small central unit

Date: October 28, 2026 UTC. Author: root continuation.
Local read base: c0391fb3bc6fa9c12f2d47d3d1cfda99aa99556b.

**Status: complete proposed hand theorem, frozen for separate complete
independent review and subsequent root adoption.** The main theorem is
force-free and independent of a containing circle. It covers a continuous
two-parameter region, including its entire critical equality curve. Its
aligned-house consequence strengthens a necessary center-count restriction;
it does not close the remaining house or locate any entire unit in a sector.

All centers refer to one unchanged point O. Every unit below is an actual
closed square of side one, and all their open interiors are pairwise
disjoint. Additional actual units, orientations and contacts are arbitrary.

## 1. Continuous theorem and equivalent individual-center formulation

Choose any real parameters a,b satisfying

    1/sqrt(2) < b < 1,
    0 <= a <= 1/b-b.                                      (1)

Suppose one actual unit A has |c_A|<=a.

**Theorem 1.** At most two other actual units have center norm at most b.
The theorem includes every equality in |c_A|<=a, |c_E|<=b and
`b*(a+b)<=1`. No degree, circle load, boundary contact, selected normal,
force application, common orientation, or containing-radius premise is used.

Equivalently, if the actual center radius r=|c_A| satisfies

    0 < r < 1/sqrt(2),
    B(r)=(sqrt(r^2+4)-r)/2,

then at most two other centers lie in the closed disk of radius B(r).
In particular, if three or more other units exist, the third-smallest
of their center radii is strictly greater than B(r). Here

    1/sqrt(2)<B(r)<1,
    B(r)*(r+B(r))=1,                                    (2)

so this is a literal instance of (1), retaining the equality curve.
If r=0, center separation gives only the different endpoint statement
that every other center has radius at least one; a strict conclusion at
one is not asserted.

## 2. Actual center separation and its full equality rigidity

Every actual unit contains the open disk of radius 1/2 about its center.
The actual center distance of two distinct units is therefore at least one.

We need the following physical equality statement:

    At center distance exactly one, the unit displacement vector
    is a side-axis direction of both actual squares.                 (3)

Indeed, take a separating line for the two interior-disjoint compact
convex squares, and choose its unit normal n from the first center c
toward the second center d. If their directional halfwidths are h_c,h_d,
then

    1=|d-c| >= n.(d-c) >= h_c(n)+h_d(n) >= 1.

Every inequality is equality. Thus n=d-c, and both halfwidths equal 1/2.
For the actual orthonormal side directions u,v of either square,

    2h(n)=|n.u|+|n.v|,
    (n.u)^2+(n.v)^2=1.

Two nonnegative numbers whose squares sum to one have sum one only
when one is zero and the other is one. Hence n is one of that square's
two side axes, with either sign, proving (3). The auxiliary separating
line is purely geometric and does not change a selected contact normal.

## 3. One angular interval covers the whole parameter region

Suppose, for contradiction, that three distinct further actual units
E_1,E_2,E_3 have center radii at most b. Write r=|c_A|. If r=0,
their distances from c_A are at most b<1, already impossible. No c_E
can be O either, because r<=a<1. Thus all required directions exist.
The inequality a< b<1 follows from (1) and b^2>1/2.

For positive x,y<1 set

    F(x,y)=(x^2+y^2-1)/(2xy).

It is strictly increasing in either variable on this entire domain:

    partial_x F=(x^2-y^2+1)/(2*x^2*y)>0,
    partial_y F=(y^2-x^2+1)/(2*x*y^2)>0.             (4)

Define

    a_*=1/b-b,
    gamma=F(b,b)=1-1/(2*b^2),
    theta=acos(gamma).

By (1),

    0<gamma<1/2,
    pi/3<theta<pi/2,
    F(a_*,b)=-gamma.                                (5)

The cosine law and actual center separation give, for the minor angle
omega between c_A and any of the three further centers,

    cos(omega) <= F(r,|c_E|)
                <= F(a_*,b) = -gamma.               (6)

Consequently all three directions lie in the one closed interval of
halfwidth theta about the direction opposite c_A. Its total length is
2theta<pi. This is a statement about their center directions only.
No conclusion about the shape or location of an entire unit is drawn.

Similarly, for two further centers their minor angle omega_ij obeys

    cos(omega_ij) <= F(|c_Ei|,|c_Ej|)
                   <= F(b,b)=gamma,                (7)

so omega_ij>=theta. Directions are distinct, since two centers on one
ray with radii at most b would be less than one apart. Order the three
directions in the interval from (6). Because its length is less than
pi, each successive difference is its minor angle. By (7), each is
at least theta. Their total span is therefore at least 2theta,
which is the full length of the containing interval.

Every one of these angular comparisons must be equality. The outside
directions are exactly the endpoints, the middle is the midpoint, and
both successive differences are theta. For either outside direction,
equality in (6) and the strict monotonicity (4) force r=a_* and
the corresponding radius to be b. Equality in (7) for a successive
pair then forces the middle radius to be b as well. In particular
the hypothetical configuration also forces a=a_*; every strict
parameter inequality in (1) was already contradictory.

Thus the sole remaining possibility has

    |c_A|=a_*=1/b-b,
    |c_E1|=|c_E2|=|c_E3|=b,                          (8)

and the exact directions just described. This retains the entire
critical curve, with no generic-position restriction.

## 4. The whole critical equality curve is incompatible with square axes

Rotate the coordinates about O so c_A=(a_*,0). Equations (5)--(8)
place the middle further center at (-b,0) and the other two at

    c_+ = (1/(2b)-b,  sqrt(1-1/(4b^2))),
    c_- = (1/(2b)-b, -sqrt(1-1/(4b^2))).             (9)

These coordinates follow from -b*gamma=1/(2b)-b and
`b^2*(1-gamma^2)=1-1/(4b^2)`. Their displacements from c_A are

    v_+ = (-1/(2b),  sqrt(1-1/(4b^2))),
    v_- = (-1/(2b), -sqrt(1-1/(4b^2))),
    |v_+|=|v_-|=1,
    v_+.v_- = 1/(2b^2)-1.                          (10)

Because 1/sqrt(2)<b<1, the last scalar product lies strictly between
-1/2 and 0. By the actual distance-one rigidity (3), both v_+ and v_-
must be side-axis directions of the same actual square A. Scalar
products between two signed unit side axes of one square belong to
{-1,0,1}. Equation (10) is impossible throughout the entire open b
interval. This excludes every equality configuration and proves
Theorem 1, including all of its closed radius and parameter endpoints.

## 5. Why the two b endpoints are not silently included

At b=1/sqrt(2), a_*=b and the value in (10) becomes zero. There is
an actual counterexample to the proposed endpoint extension: the four
axis-aligned unit squares with centers (1/2,1/2), (1/2,-1/2),
(-1/2,1/2), (-1/2,-1/2). Their interiors are disjoint and all four
centers have norm b. Thus the strict lower endpoint is necessary.

At b=1, a_*=0. A square centered at O and three of its axis-aligned
unit neighbors with centers (1,0), (-1,0), (0,1) are another actual
counterexample. The strict upper endpoint and the separate r=0
statement in Section 1 are therefore intentional.

These examples identify excluded b endpoints, not a claim of global
sharpness for every individual r or for any containing-circle problem.

## 6. A stronger whole aligned-house completion-center threshold

Retain the actual aligned S-root chart

    2<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,
    A=[d-1,d] times [-beta,1-beta],
    L=[d,d+1] times [-1/2,1/2],
    1/3<=beta<=1/2.                                  (11)

The actual leaf is retained; it is not needed for the local count
after this whole chart is supplied. The same exact estimates as in
the accepted three-quarter theorem give

    14/15<d<61/60,
    c_A=(d-1/2,1/2-beta),
    |c_A|^2<(31/60)^2+(1/6)^2=1061/3600.              (12)

For completeness, the d bounds follow by squaring positive quantities:

    15/4-(29/15)^2=11/900>0,
    (121/60)^2-(1105/256-1/4)=31/57600>0.

Take the single rational pair

    b=19/25, a=1/b-b=264/475.

It belongs to the complete domain (1), since b^2=361/625>1/2,
b<1 and a>0. Moreover

    (264/475)^2-1061/3600=460699/32490000>0.           (13)

Thus (12) supplies |c_A|<a. Theorem 1 gives:

**Corollary 2.** Among any three further actual units, at least one
has center norm strictly greater than 19/25. Among any four further
actual units, at least two have center norm strictly greater than
19/25. If one of those four is a retained core unit D with
|c_D|<=19/25, at least two of the other three have center norm
strictly greater than 19/25.

For the original aligned M6.B5L.HOUSE.HUB.LTCB.S component, the full
accepted shallow-page source supplies (11) throughout its whole low,
critical and high aligned domains. Its unchanged graph is

    AT,DT,AD,AB,BC,CD,AL;
    true A4,D3,T2,B2,C2,L1;
    positive circle loads at T,B,C,L.

All nine actual units remain. Applying Corollary 2 to the original D
and the three actual completion units proves that at least two of
these four have center norm greater than 19/25. If the actual D
is itself no larger than that threshold, the two large centers are
necessarily among the three completions. This strengthens the
accepted 3/4 threshold on the whole same original domain. Since
19/25>3/4>37/50, these units also meet the accepted centered-forty-
degree arc theorem's threshold whenever a caller uses that theorem.

This is a center-count consequence only. It neither states that all
completions qualify, nor locates a qualifying unit in a particular
sector or angular gap. No physical boundary status or load is assigned
from a center count. The actual B--C--D branch remains; no BD contact
is added. A further original geometric or capacity contradiction is
still required to close the house family.

## 7. Dependencies and exact export boundary

Sections 1--5 are a self-contained elementary hand proof. Section 2
also reproduces in full the rigidity argument of the accepted fixed-
threshold predecessor rather than treating a prior verdict as a proof.
The following exact sources identify the already accepted physical
house chart, graph, earlier fixed threshold and arc-threshold relation:

| Source | SHA256 | Literal role |
| --- | --- | --- |
| SMALL_CENTRAL_UNIT_EXCLUDES_THREE_OTHER_THREE_QUARTER_CENTERS.md | 5ec9509ff5e2e79c25a4bd9d59d3ee2a53dd2fcf5c0ddd039c93add3552e2a14 | Earlier fixed pair a=7/12,b=3/4 is a literal instance of the new continuous theorem; its whole physical house chart is retained |
| ALIGNED_S_ROOT_SHALLOW_BOUNDARY_PAGE_EMPTY_CENTER_GAP.md | 5681926e8705af07ab4cde28d16e859c42ed8bab71f69e01641844efab47ae0a | Entire original low/critical/high aligned-house slider and all three actual completion units |
| FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md | e5c84071363e8dc43b09f9033c7cb3a7684f1de19bcd169d53c9eab55d51963b | Exact original house graph, true degrees, load set and genuine leaf |
| THIRTY_SEVEN_FIFTIETHS_CENTER_UNIT_CENTERED_FORTY_DEGREE_ARC.md | aef1a6c7a6ac6631c5b236f50301b31db2f87441b1f9e22883686d8f70032282 | Only the stated threshold relation: center norm greater than 19/25 qualifies for its complete actual 40-degree arc |

No source bytes in this table have been modified. No numerical pose,
angle mesh, orientation enumeration, finite exclusion certificate,
generated coefficient table, Lean/Lake run, CI/workflow, force deletion,
changed original normal or mean, metadata/count edit, staging, commit,
remote mutation, whole-family flag, or certificate-retirement credit is
part of this proposed theorem. Separate complete independent review
and root adoption of these exact new bytes are still required.
