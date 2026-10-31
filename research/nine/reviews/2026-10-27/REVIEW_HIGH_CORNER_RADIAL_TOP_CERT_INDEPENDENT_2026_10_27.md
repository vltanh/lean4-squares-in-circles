# Independent review: the entire owned high-corner radial top exclusion

Date: October 27, 2026.  
Reviewer: cert_final_review.  
Verdict: **complete independent non-contributor PASS for the frozen local
theorem and its exact conditional original application. No correction
requested.**

## 1. Exact target, scope and independence

I read and independently reconstructed all twelve sections of

    HIGH_CORNER_OWNED_CENTRAL_RADIAL_TOP_EXCLUSION.md
    SHA256 3b3ba081d85d7695e92d524859a15c8a9a1775ca0416cdb7bb95e76a8685ced7
    14,548 bytes.

The entire physical statement is accepted. Its domain is

    1<=d<61/60, R^2=(d+1)^2+1/4,
    -1/60<=h<=0, 89/120<G<1,
    H=[h-1,h] x [G-1,G], W=(h,G),
    m=(-c,s), n=(s,c), c,s>0, c^2+s^2=1,
    K=W+[-ell,1-ell]m+[0,1]n, 0<ell<1.

The three physical squares are interior-disjoint and pairwise touch.
K touches the containing circle. C has two physical adjacent circle
corners, has minimum height G, and meets H with actual H-to-C normal
E2. The actual central side at W is K-owned, with its full ell retained.

No force equation, degree, individual circle weight, C2 concurrence,
normal selector, CK owner or predetermined CK point enters the local
theorem. In particular K may have arbitrary force degree and either
initial physical mask. The physical two-corner condition at C remains
the exact condition being excluded, even if one of its circle weights
would be zero. The entire h=0 endpoint is included. The strict G<1
hypothesis is correctly retained rather than claimed at G=1.

I supplied no proof argument, scalar comparison, contact-cover step
or correction to this new source. I previously authored or reviewed
other neighboring root/page results. None of those results is a logical
input to this local theorem, whose three foundations are all present
original sources. I did not run or import the author's checker and did
not infer acceptance from the author's algebra report. The geometric
and continuous arguments below were reconstructed independently, and
the separate exact record was written from those reconstructions.

## 2. Full foundational reads and exact bytes

I read the complete three original foundations, including their full
scope restrictions. Only the physical parts stated below are used;
no stronger force-polygon or degree-two conclusion is transferred.

| Exact source | Verified SHA256 | Complete scope checked |
| --- | --- | --- |
| HIGH_CORNER_OWNED_CENTRAL_RADIAL_TOP_EXCLUSION.md | 3b3ba081d85d7695e92d524859a15c8a9a1775ca0416cdb7bb95e76a8685ced7 | All twelve target sections, full local statement and conditional caller |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Physical side/vertex normal cones, actual shared geometry and genuine application conventions |
| C7_FORCE_POLYGON.md | d50d8ca48ea19156175e651bfa74be30ef3e58065ec14d8d1834670a41559089 | Physical two-circle-corner classification, unshareable circle corners and the whole inner-face metric argument only |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Entire radius-free physical triangle theorem, including actual side positions, free other normals and zero dot-product endpoints |

All four pins match the actual present bytes. The target has no missing
recent manuscript or remembered acceptance as a logical premise.

The physical triangle theorem applies whenever the normal at the first
contact is a real side axis of that square. Its other normal can be any
actual common supporting normal. The proof uses the strict backward
span of a whole unit square when the dot product is negative, including
both a vertex support and the full support-side slider. Its conclusion
is nonnegative dot product, not a strict positivity statement. Every
use in the target is on the physical H-K-C triangle; no B-K-C contact
or force has been invented.

## 3. Exhaustive physical C orientation

I reconstructed the physical two-corner classification directly. At
a circle corner in its orthogonal side frame the two outward own
coordinates are at least one half, by comparison with the adjacent
corners. A second equal-radius adjacent corner forces one coordinate
to equal one half. An opposite equal-radius corner would force both
coordinates to equal one half and radius squared one half, outside
the target domain. Thus the exact physical form is

    C=[d,d+1]e+[-1/2,1/2]f,

with orthonormal e,f and actual circle corners (d+1)e±f/2. This
classification does not depend on either circle multiplier.

Since min-height C=G>0, its radial direction has positive height.
For a positive horizontal radial component, write e=(q,p), f=(p,-q),
q,p>0. The unique minimum-height vertex then has horizontal coordinate
dq+p/2>0 and cannot meet H's top, whose x coordinate is at most h<=0.
For a zero horizontal radial component, e=E2 and min-height C=d>=1,
contrary to G<1. This removes the full aligned/shared-HC possibility
physically; no shared mean is replaced by a selected corner.

The entire remaining orientation is therefore exactly

    e=(-q,p), f=(p,q), p,q>0, p^2+q^2=1,
    T=(-dq-p/2,G), G=dp-q/2,
    V=(a,G+q), a=p/2-dq.

T is the actual minimum-height vertex and actual HC application.
The two possibilities for the radial direction and the axis endpoint
have all been exhausted before this chart is used.

## 4. Uniform angle, point and support bounds

The full q>=2/5 alternative has p<=sqrt(21)/5<11/12. Its actual
height would satisfy

    G<(61/60)(11/12)-1/5=527/720<89/120.

The squared radical reserve is 1/3600, and the last height reserve
is 7/720. Thus q<2/5. Consequently p>9/10 and

    a>9/20-61/150=13/300>0,
    a<1/2.

The positivity of a is proved before any ratio q/a or angle atan(q/a)
is used. It also fixes the actual C upper vertex to the right of W.

The full displacement satisfies

    V-W=(a-h,q),
    0<a-h<31/60,
    |V-W|^2<(31/60)^2+(2/5)^2=1537/3600<1.

The strict distance reserve is 2063/3600. The lower C vertex is
strictly left of W: T_x<-9/20<h, including h=-1/60. Since its height
equals G and n=(s,c) has s>0,

    (T-W)·n=s(T_x-h)<0.

The entire K has nonnegative n-coordinate relative to W. Hence T is
not in K. This is an actual support separation, with no C2 or torque
assumption.

## 5. Every C side and vertex in the physical CK cover

The complete actual contact cover passes. I checked the side normals
with their correct directions on both C and K:

| Actual C boundary feature | Complete physical exclusion |
| --- | --- |
| Maximum-e side relative interior | C-to-K=e and C-to-H=-E2 have dot product -p<0; e is C-owned |
| Maximum-f side relative interior | C-to-K=f and C-to-H=-E2 have dot product -q<0; f is C-owned |
| Minimum-f side relative interior | K-to-C=f and the actual K-owned central K-to-H=-n have dot product -(sp+cq)<0 |
| Minimum-e side relative interior | The whole neighboring unit has squared norm at most d^2+9/4<R^2 |
| Both outer C vertices | Actual containing-circle points are physically unshareable |
| Lower inner vertex T | Its actual n-support is strictly below the minimum support of K |
| Upper inner vertex V | Retained |

For the inner-face row I reconstructed the full metric argument,
including a support-side slider rather than only a strict vertex.
At P=de+t f, |t|<=1/2, the neighbor has maximum e support d. Its
whole e interval lies in [d-sqrt(2),d], a subset of [-d,d] because
d>=1. At a maximum-e vertex its two orthogonal inward axes have
opposite f signs, so the whole f interval is in [t-1,t+1]. At a
support side its full actual length-one interval gives the same
bound. Hence every point has squared norm at most d^2+9/4. The
exact gap from R^2=(d+1)^2+1/4 is 2d-1>=1. Such a unit cannot be
the physically boundary K. The endpoints T,V are independently
covered, so a relative-interior argument is not stretched across
an unproved endpoint.

Circle-point unshareability is physical: containment at a circle
corner forces the negative radial vector strictly into the inward
quadrant of every incident square. Two units sharing that corner
would have an open intersection. No circle-weight condition is used.

These rows cover the entire C boundary, and a point of the open C
interior cannot belong to another full-dimensional square with
disjoint open interiors. Therefore the actual contact CK is exactly
{V}. A physical shared segment would contain an excluded side
relative interior or a circle vertex. This proves singletonness
without preselecting a CK type or normal.

## 6. The actual side position and every original normal endpoint

Every nonzero actual outward normal of C at V belongs to the cone
generated by -e=(q,-p) and f=(p,q). Each generator has positive
x coordinate; hence every such normal w has w_x>0, including either
cone boundary.

The actual K n-coordinate of V is

    theta=s(a-h)+cq.

It is positive by the proved signs and strictly below one by
|V-W|<1. Thus V cannot be on either n-face or at any K vertex.
It must be in the relative interior of one of the two m-sides.
The minimum-m side would make the C-to-K normal equal to m, with
negative horizontal component. This contradicts w_x>0. Therefore
V is on the maximum-m side, and the full actual coordinate relation is

    j=1-ell in (0,1),
    V=W+j m+theta n,
    j=sq-c(a-h)>0,
    theta=s(a-h)+cq in (0,1),
    w=-m.

I independently expanded both inverse coordinate equations. The
normal w is fixed by this physical side, not chosen after extracting
a stress. In particular the possible free-CK vertex endpoint theta=1
has been excluded by the actual point-distance inequality, not by
an unproved CK-owner premise. A complete shared mean or an originally
free normal supplies no remaining exception to this cover.

## 7. All K corners and the rigorous h=0 enlargement

The two minimum-n corners are W-ell m and W+j m. Their distances
from W are below one, and |W|<61/60. Thus both have norm below
121/60<R, with squared radius reserve 659/3600. This covers these
two actual corners before any circle corner of K is selected.

The only remaining candidates are

    Z_plus=W+j m+n,
    Z_minus=W+(j-1)m+n.

At fixed d,p,q,c,s define

    j0=sq-ca,
    theta0=sa+cq.

The actual relation is j=j0+ch. Since j>0 and h<=0, j0>0. Also
j0<sq<2/5 and

    0<theta0<=sqrt(a^2+q^2)<sqrt(41/100)<1.

These bounds apply to the entire enlargement, not merely the
actual point. Let Z_plus^0,Z_minus^0 use h=0 and j0. I reconstructed
the exact vector identities

    Z_plus=Z_plus^0+hs n,
    Z_minus=Z_minus^0+hs n.

For both enlarged corners Z^0·n=1+cG. Consequently the whole norm
difference is exactly

    |Z|^2-|Z^0|^2=hs[2(1+cG)+hs]<=0.

The bracket is greater than 2-1/60>0; h=0 gives equality. This
justifies bounding the algebraic expressions at h=0 in the correct
direction. It neither moves an actual packing unit nor assumes that
the enlarged pose is physically feasible. The proof uses an explicit
scalar comparison of its actual corner norms.

## 8. The first enlarged corner is uniformly inside R

The exact physical radial identity is |V|^2=d^2+1/4. At h=0 the
same actual C point satisfies

    V=(0,G)+j0 m+theta0 n,
    Z_plus^0=V+(1-theta0)n.

I expanded its entire squared norm using both unit-frame identities
and obtained exactly

    R^2-|Z_plus^0|^2
       =2d+theta0^2-2cG(1-theta0).

Since c<=1, G>0 and 0<theta0<1, the right side is at least
2(d-G)+theta0^2. The actual C height G=dp-q/2 is strictly below d
for the entire q>0 domain. Thus the gap is strictly positive. No
sign of a circle resultant, K load or K force appears in this step.

## 9. The whole second-corner interval is monotone

Put u=1-j0. Its full norm is

    N=|Z_minus^0|^2
      =G^2+1+u^2+2G(c-us).

With c=sin(phi), s=cos(phi), positivity of a,q gives a well-defined
phi_star=atan(q/a) in (0,pi/2). The actual condition j0>0 is exactly
0<phi<phi_star. Throughout the entire enlarged closed interval
0<=phi<=phi_star, one has

    0<=j0<=q<2/5,
    u>0,
    0<theta0=sa+cq<1,
    u'=theta0, c'=s, s'=-c.

Thus all denominator, square-root and sign conditions needed by the
comparison hold over the whole interval. Direct differentiation gives

    N'=2u theta0+2G[s(1-theta0)+uc]>0.

I checked this as a whole polynomial identity in the actual angular
derivative operator s*d/dc-c*d/ds, rather than at sampled angles.
The derivative is positive also at phi=0 and at phi_star. Therefore
the maximum occurs at j0=0, where

    c_star=q/sqrt(a^2+q^2),
    s_star=a/sqrt(a^2+q^2),
    N<=G^2+2+2G(q-a)/sqrt(a^2+q^2).

The positive square root is legitimate because a,q>0. No positivity
assumption on q-a has been introduced; the next comparison covers
both signs. The actual strict j>0 remains part of the original
physical domain, while j0=0 is only the proved algebraic enlargement.

## 10. The full radial-angle cover and exact reserves

For 0<q<=1/3, the full unit-circle relation gives

    p>=sqrt(8/9)>14/15,
    a>7/15-61/180=23/180,
    q/a<60/23.

The squared p reserve is 4/225. The function
(t-1)/sqrt(1+t^2) has positive derivative (1+t)/(1+t^2)^(3/2)
for the entire t>=0 domain. Hence

    (q-a)/sqrt(a^2+q^2)
       <37/sqrt(4129)<3/5.

The last comparison has squared reserve 2936/103225. It is valid
even if the original numerator q-a is negative. With G>0 and G<1,
the complete endpoint norm is therefore strictly below

    G^2+2+(6/5)G<21/5<17/4<=R^2.

The final strict radius reserve is 1/20.

For 1/3<=q<2/5, the entire other interval gives

    p<=sqrt(8/9)<17/18,
    G<(61/60)(17/18)-1/6=857/1080<4/5.

The squared p reserve is 1/324, and the height reserve is 7/1080.
The positive a,q give (q-a)/sqrt(a^2+q^2)<1 on the whole domain;
there is no unsafe squaring of a possibly negative numerator. Thus

    N<G^2+2+2G<106/25<17/4<=R^2,

with final radius reserve 1/100.

The two intervals cover all q in (0,2/5), and q=1/3 is included
in both necessary comparisons. Both are whole continuous estimates,
not sample values. Together with the first enlarged-corner bound,
the h comparison, and the minimum-n corner bounds, every actual K
corner lies strictly inside the containing circle. The entire convex
square does too, contradicting its physical boundary contact. This
completes the full local theorem.

## 11. Exact caller boundary and proof completeness

The original application in Section 11 is correctly conditional on
the independently derived actual chart

    h=-x<0, 89/120<G<1,
    K=(h,G)+[-ell,1-ell](-c,s)+[0,1](s,c),
    c,s>0, 0<ell<1,
    HC normal E2, with its actual mean.

Every such chart has exactly the local hypotheses just proved.
Neither a B force law nor either particular BK physical type enters
the local theorem. Its broad physical statement therefore transfers
uniformly to either genuine H leaf and either BK type when that
whole original chart has been established.

This review does not independently prove a missing original direction
cover or relabel a unique-C-only cover as valid for physical-S C. The
separate all-mask original chart must still receive its own complete
review before an original-family assembly invokes the present result.
The target itself states that obligation explicitly and does not use
the future assembly as an input to its physical proof. Thus there is
no circular mask or normal-sign argument here.

The h=0 endpoint, full central ell interval, every C side and vertex,
every CK normal-cone endpoint, and all actual means are covered. The
strict G<1 premise and strict 0<ell<1 central ownership remain honest
scope boundaries. No statement at G=1 or a free central endpoint is
claimed by this local source; those have their separate physical
theorems where needed.

## 12. Independent exact record and final verdict

My separately written exact audit is

    recovery_2026_10_27/cert_high_corner_radial_top_exact_audit.py

and its complete report is

    recovery_2026_10_27/cert_high_corner_radial_top_exact_audit.json.

It verifies **36 whole coordinate, norm, support, inverse-frame or
derivative identities; 25 exact rational values and reserves; and all
four target/input pins**. It uses transparent sparse-polynomial
expansion and Fraction arithmetic only. The target author's checker
was not run or imported. The exact record includes both radial circle
corners, every relevant physical normal dot product, both actual port
coordinates and inverse maps, both h-enlargement vectors and complete
norm differences, the first corner's full radial gap, the complete
second-corner norm and angular derivative, and the scalar endpoint
comparisons.

These checks validate the displayed algebra. The full continuous
physical contact cover, actual endpoint handling, safe comparison
directions and original conditional application were independently
reconstructed above. The record is not a computational exclusion
certificate, a pose sample or an interval packet.

**Final verdict: complete independent non-contributor PASS for all
twelve sections at the unchanged frozen source hash, with no requested
correction.** The entire K-owned high-corner/top physical-two-circle C
feature is analytically excluded whenever its explicit actual chart
holds. No original gate or ledger was changed, and no remote, Lean
or CI action was performed.
