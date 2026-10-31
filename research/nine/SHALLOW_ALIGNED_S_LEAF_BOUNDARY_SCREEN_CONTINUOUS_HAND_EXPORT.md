# A continuous hand proof of the entire shallow aligned S-leaf contact screen

Date: October 28, 2026 UTC. Author: fan_low continuation.

**Status: complete force-free hand export and proposed replacement of one
four-interval coefficient certificate, frozen for full root and separate
independent review.** The proof extracts and fully restates the physical
calculation of Sections 2--3 of S_LEAF_C5_ALIGNED_LOW_RADIUS_EXCLUSION.md.
Its original true-degree-three root equations and later singleton
selection are not used. Every premise needed for the physical calculation
is supplied directly below, including both radius endpoints and zero
transverse height.

## 1. Whole physical statement, including all closed endpoints

Let actual unit squares X,L,V have pairwise disjoint open interiors and
be contained in the same origin-centered disk, where

    2<=R<=sqrt(17)/2,
    d=sqrt(R^2-1/4)-1,
    0<=h<=1/3,
    X=[d-1,d] times [h-1,h],
    L=[d,d+1] times [-1/2,1/2].                       (1)

Suppose the actual unit V satisfies

    V subset {y>=h},
    (x,h) in X intersect V,
    d-1<=x<=d.                                       (2)

The displayed point may be its original side mean or either endpoint.
No force, load, degree or selected-normal premise is imposed on V or X.
The actual occupied rectangle L is retained, without replacing any
physical force by a leaf.

**Theorem.** Every actual V corner has norm strictly less than R.
Consequently V cannot physically touch the containing circle.

This is the complete physical top-contact statement in Sections 1--5
of C6_NEXT_INTACT_ROOT_GENUINE_CYCLE_ALIGNED_S_LEAF_EXCLUSION.md, with
the additional closed endpoint h=0. It is proved without that source's
four-interval Bernstein coefficient table. The theorem is not restricted
to any C5 or intact-root graph.

It is convenient to reflect the whole frame vertically and prove the
identical lower-contact statement. Put b=h, a=1-b. Then

    X=[d-1,d] times [-b,a],
    0<=b<=1/3,       2/3<=a<=1,
    V subset {y<=-b},
    P=(x,-b) in X intersect V.                        (3)

The real L is unchanged by this reflection. All original points remain
their actual reflected points; no side mean is moved.

## 2. The physical boundary assumption supplies the full entry interval

Suppose V physically touches the containing circle. We derive a
contradiction for every possible actual orientation and physical mask.
If there were no physical circle point to start with, containment in
the closed disk already gives the theorem's strict corner conclusion.

Every point of a physical boundary unit has norm at least R-sqrt(2),
by its actual diameter. Thus the unchanged contact P satisfies

    x^2+b^2 >= (R-sqrt(2))^2
                 >=(2-sqrt(2))^2>12/35.              (4)

The final strict comparison uses sqrt(2)<99/70. Also

    14/15<d<=1,
    R^2=(d+1)^2+1/4.                                (5)

The lower d inequality follows at R=2 from

    15/4-(29/15)^2=11/900>0.

Since b<=1/3, (4) gives

    x^2>12/35-1/9=73/315>(12/25)^2.

Its last reserve is 53/39375. The actual x>=d-1>-1/15 excludes
the negative sign, so the complete necessary boundary-contact range is

    12/25<x<=d.                                      (6)

This argument does not use an equation at X or V, a physical unique
corner, or positive weight at every circle corner. It applies at
R=2, R=sqrt(17)/2 and b=0 without a limiting argument.

## 3. Every aligned frame and the actual occupied-leaf inequality

If V is aligned, it is [z,z+1] times [-b-1,-b], with z<=x<=z+1.
Its vertical interior overlaps that of the real L, because b<=1/3.
The alternative z>=d+1 is incompatible with z<=x<=d. Thus actual
interior-disjointness forces z+1<=d. Equation (6) gives

    z>=x-1>-13/25>-d.

All V corners consequently have absolute first coordinate at most d
and absolute second coordinate at most 4/3. Their squared norm is
at most d^2+16/9<R^2, by (5). This excludes the complete aligned
support side, its endpoints and every original mean.

Otherwise P is the actual unique highest V vertex. Its entire frame is

    V=P+[0,1](c,-s)+[0,1](-s,-c),
    c,s>0,       c^2+s^2=1.                          (7)

Both tilts are retained; c and s are not ordered. Put

    Delta=1/2-b,       1/6<=Delta<=1/2.

If x+c<=d, every corner has absolute horizontal coordinate at most d:
the leftmost possibility is x-s>-13/25>-d. Every vertical magnitude
is at most b+c+s<1/3+17/12=7/4. Hence

    |corner|^2<d^2+49/16<R^2,                        (8)

because 2d+5/4>187/60 and 187/60-49/16=13/240>0.

Suppose instead x+c>d. The real edge from P in direction (c,-s)
crosses x=d before its endpoint. At that crossing it must have
height at most -1/2; otherwise a short further edge segment enters
the open actual L and forces overlap of square interiors. Thus

    (d-x)s>=Delta*c,
    x<=d-Delta*(c/s).                                (9)

Equality at the actual leaf corner (d,-1/2) is included. This is an
inequality at the unchanged original contact, not a substituted pose.

## 4. Three corners and both full right-adjacent ranges

The actual P and its left adjacent corner P+(-s,-c) have horizontal
magnitude at most d and vertical magnitude at most 4/3. They are
strictly inside the original circle by the aligned comparison above.

For the right adjacent corner P+(c,-s), (9) gives

    0<x+c<=d+c*(1-Delta/s),       b+s<=1/3+s.           (10)

On the positive part of c*(1-Delta/s), its whole-angle maximum is

    (1-Delta^(2/3))^(3/2).

Indeed the derivative of sqrt(1-s^2)*(1-Delta/s) has the sign of
Delta-s^3, and the two endpoints of its positive interval have value
zero. Since Delta>=1/6>1/8, this maximum is strictly below

    (3/4)^(3/2)=3sqrt(3)/8<2/3.                      (11)

The nonpositive part satisfies (11) immediately. No finite list of
angles is used here.

If s<=4/5, equations (10)--(11) put the actual right-corner squared
norm strictly below (d+2/3)^2+(17/15)^2. Subtracting R^2 gives

    -(2/3)d+431/900<-129/900<0.                       (12)

If s>=4/5, then c<=3/5 and 1-Delta/s<=1-Delta<=5/6. Therefore
c*(1-Delta/s)<=1/2, including a nonpositive left side. The squared
norm is at most (d+1/2)^2+(4/3)^2, whose difference from R^2 is

    7/9-d<0.                                         (13)

Both closed ranges contain s=4/5 and cover every original right
adjacent corner, including the full screen equality in (9).

## 5. One continuous concavity estimate for the opposite corner

The only remaining actual corner is

    Z=(x+c-s,-b-c-s).

If c<=s, its horizontal magnitude is at most d and its vertical
magnitude is below 7/4; the complete bound (8) applies. Otherwise
put k=c/s>1. Equations (6),(9) give the entire comparison interval

    1<k<(d-12/25)/Delta<=78/25.                       (14)

The actual first coordinate of Z is positive. In its upper bound
from (9), lowering Delta to 1/6 increases that coordinate; it also
increases its negative second-coordinate magnitude. Consequently

    |Z|^2<=F_d(k),

    F_d(k)=[d-k/6+(k-1)/sqrt(1+k^2)]^2
               +[-1/3-(k+1)/sqrt(1+k^2)]^2.          (15)

For fixed k in (14), the difference F_d(k)-R^2 decreases strictly
with d. Its derivative is

    2[-k/6+(k-1)/sqrt(1+k^2)-1]<0.

It suffices to prove, on the whole closed interval 1<=k<=78/25,

    F_(14/15)(k)<3589/900=(29/15)^2+1/4.              (16)

Write F=F_(14/15). Direct differentiation gives exactly

    F''(k)/2=1/36-N(k)/(1+k^2)^(5/2),
    N(k)=(43/10)k+(31/30)k^2-4/15.                   (17)

The function N(k)-(1+k^2)^2/5 is concave throughout the whole
interval: its second derivative is 19/15-(12/5)k^2<0. Its two
endpoint values are

    64/15,       953582/5859375,

both strictly positive. Thus N(k)>(1+k^2)^2/5 throughout. Also
sqrt(1+k^2)<33/10, so (17) yields

    F''(k)/2<1/36-2/33=-13/396,
    F''(k)<-1/16.                                    (18)

At k=2 the exact values are

    F(2)=556/225+16/(5sqrt(5))<391/100,
    F'(2)=-1/5+19/(75sqrt(5)),
    -9/100<F'(2)<0.                                  (19)

The first bound uses sqrt(5)>67/30, with final rational reserve
73/12060. The derivative bounds use 2<sqrt(5)<9/4; the lower
reserve is 7/2700. These are exact comparisons, not evaluations
at sampled square orientations.

Integrating (18) on either side of 2, and completing one square,
gives every k in the entire interval (14):

    F(k)<=F(2)+F'(2)(k-2)-(k-2)^2/32
         <=F(2)+8 F'(2)^2
          <9937/2500<3589/900.                        (20)

The last exact reserve is 73/5625. This proves (16). Equations
(14)--(20) control every possible opposite corner in the remaining
c>s row, including all real-leaf equality cases.

All four actual V corners are now strictly inside the original
radius-R circle under the assumption that V physically touches it.
This contradiction proves the entire theorem (1)--(2). The proof
has explicitly retained b=0, b=1/3, d=1 and R=2; none is supplied
by a limit of physical poses or force certificates.

## 6. Exact replacement scope and preserved proof obligations

The physical premise (1)--(2) is exactly that of Sections 1--5 of
C6_NEXT_INTACT_ROOT_GENUINE_CYCLE_ALIGNED_S_LEAF_EXCLUSION.md, enlarged
to h=0. Therefore, after independent and root review, this theorem
may replace that entire physical kernel wherever it is called with
its stated actual squares. Its source's later degree-five intact-root
equations, private-cycle order and other graph hypotheses remain their
own obligations. This export does not assert a theorem about those
graphs without their original later proof.

The replaced scalar certificate is exactly the table in that source's
Section 5: four closed intervals [1/6,1/3], [1/3,1/2], [1/2,2/3],
[2/3,1], each with seven degree-six Bernstein coefficients. It has
28 displayed coefficients. This is one certificate at one physical
kernel; it is not 28 distinct original fine goals. The frozen table
and source need not be deleted or altered. No replacement of unrelated
certificates is claimed.

The present proof uses a physical boundary contradiction to obtain
the necessary actual contact interval (6), then the continuous
concavity estimate (17)--(20). Since every actual unit is already
contained in D_R, excluding its physical boundary contact is exactly
the strict whole-corner conclusion required by the earlier kernel.
This change of proof introduces no hidden boundary-neighbor or
force-degree requirement.

## 7. Exact inputs and construction disclosure

| Source | SHA256 | Exact operative relation |
| --- | --- | --- |
| S_LEAF_C5_ALIGNED_LOW_RADIUS_EXCLUSION.md | 02fd37d94d14f8342365160064cff63d91b572e9e162944e9551590fc8f535a1 | Its complete physical Sections 2--3 calculation, fully restated with the direct hypotheses (3)--(6). Neither its true-X3 force equation, its Section 4 selection nor its later boundary-path theorem is used. |
| C6_NEXT_INTACT_ROOT_GENUINE_CYCLE_ALIGNED_S_LEAF_EXCLUSION.md | 6a1a37c6ed825ef1cea0bebf503e894e3ca9d4777fe23e3cf508b188e4898aa5 | Exact target physical kernel and its four-interval, 28-coefficient certificate only; its polynomial positivity is not a mathematical premise of the new proof. |

The mathematical continuous estimate was already printed in the first
pinned source. The new work is its independent physical statement,
direct boundary-annulus entry, complete closed-endpoint verification,
and exact replacement mapping to the second source. The author found
this extraction while completing the low aligned inner fan; root had
asked for broad proofs and fewer computational certificates, but did
not supply the new physical export or endpoint checks.

Every actual unit, original point or full shared-side mean, physical
circle mask and individual zero coefficient is retained. No numerical
pose, angular sample, new coefficient table, Lean execution, CI,
workflow, metadata, commit or remote action is part of this proof.
Full independent and root review of these exact bytes is required
before recording the proposed certificate retirement or an original
family consequence.
