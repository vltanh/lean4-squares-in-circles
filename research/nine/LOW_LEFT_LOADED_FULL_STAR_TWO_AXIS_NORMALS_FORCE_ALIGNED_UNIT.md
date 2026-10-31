# A low-left loaded full star with two perpendicular normal directions is aligned

Date: October 28, 2026 UTC. Author: tc_finish_v2 continuation.

**Status: complete proposed arbitrary-degree hand rigidity theorem,
frozen for separate full independent and root review.** Every actual
force, application and circle coefficient is retained. The proof
excludes the entire tilted-unit domain with one physical-mask cover
and whole-interval inequalities, without a computational certificate.

## 1. Complete original full-star statement

Let T and all its actual neighbors be contained interior-disjoint
closed unit squares in the same original circle, where

    0<=epsilon<1/60, d=1+epsilon,
    R^2=(d+1)^2+1/4<=Q=1105/256.

Suppose T has a positive total original circle load and actual
coordinate maxima

    max_T x=epsilon,
    max_T y=-f,
    89/120<f<1.                                      (1)

Its true positive degree is arbitrary. Assume that every one of its
original positive pair normals is North or East, and that both
directions occur with positive total magnitude. All original means
remain on their actual support faces; no two means are identified
unless the actual geometry makes their application points equal.

**Theorem 1.** T is axis-aligned, hence its entire actual square is

    T=[epsilon-1,epsilon] times [-f-1,-f].             (2)

Its physical circle corner is then uniquely
(epsilon-1,-f-1), and physical boundary contact gives

    R^2=(1-epsilon)^2+(1+f)^2.                       (3)

There is no degree-two premise in the theorem. The full circle
resultant and the complete original force and torque equations are
used at T. Neighbor degrees and loads are unrestricted.

## 2. Every physical two-corner mask is impossible at these maxima

The complete physical mask classification leaves either one circle
corner or exactly two adjacent circle corners. In the two-corner
case T is the actual radial square

    T=[d,d+1]e+[-1/2,1/2]Je.

The actual center has both coordinates negative: its x coordinate
is at most epsilon-1/2<0 and its y coordinate at most -f-1/2<0.
Thus write e=(-s,-c), c,s>0, c^2+s^2=1. Its exact coordinate
maxima are

    epsilon=c/2-d*s,
    f=d*c-s/2.

Adding and subtracting gives

    c+s=(f-epsilon)/(d-1/2),
    c-s=(f+epsilon)/(d+1/2).                         (4)

Both denominators are positive. The complete parameter bounds yield

    c+s>(29/40)/(31/60)=87/62>7/5,
    c-s>(89/120)/(91/60)=89/182>12/25.

Consequently

    2=(c+s)^2+(c-s)^2
       >49/25+144/625=1369/625>2,

a contradiction. This entire physical-mask exclusion uses no circle
weight restriction or force equation. In particular neither of the
two original coefficient-zero endpoints can evade it.

## 3. A tilted T has exactly two actual application values

Suppose T is not axis-aligned. Its actual rightmost and top vertices
are distinct. Write its full frame from the rightmost one as

    Q=(epsilon,-f-s),
    u=(-c,s), v=(-s,-c),
    c,s>0, c^2+s^2=1,
    T=Q+[0,1]u+[0,1]v,
    P=Q+u=(epsilon-c,-f).                           (5)

Every original East force acts at the unique actual Q; every
original North force acts at the unique actual P. Let their
unchanged positive total magnitudes be beta and alpha. The exact
full force equation gives

    F_T=(-beta,-alpha), alpha,beta>0.                (6)

This is only a grouping of original forces at identical actual
points. Their original supports, positive terms and torques all
remain. The full two-application theorem 3808 applies at arbitrary
true degree, with nonparallel original group sums. Its actual
concurrence is the intersection of the vertical P line and horizontal
Q line:

    K=(epsilon-c,-f-s)=t*F_T, t>0.                  (7)

Equation (6) therefore gives c>epsilon. Section 2 has excluded the
two-physical-corner mask, so T has one physical circle corner Z.
The legitimate unique-mask clause of the same complete theorem
puts K in the actual T. Thus

    K=theta*Z, 0<theta<=1.                          (8)

No inside-concurrence conclusion is used for a two-corner mask.

Since

    Q.v=-epsilon*s+c*(f+s)>0,

where c>epsilon and f>0, adding v strictly increases squared norm
both at Q and at Q+u. The complete unique physical circle cover is
therefore exactly

    Z_0=Q+v=(epsilon-s,-f-s-c),
    Z_1=Q+u+v=(epsilon-c-s,-f-c).                   (9)

These are actual vertices, not representatives selected by a pose
sample or a change of frame after extraction.

## 4. The entire Z_0 physical-corner row exceeds the circle

If Z=Z_0, the y coordinate in (8) gives
theta=(f+s)/(f+s+c). Its x coordinate then yields exactly

    (s-c)(f+s)=c*(c-epsilon)>0.                     (10)

Hence s>c. Also c>1/2. Otherwise c<=1/2 and s<1 imply

    (s-c)(f+s)>(s-c)*s
       =1-c^2-s*c>c^2>=c*(c-epsilon),

contradicting (10); the strict middle inequality follows from
2c^2<=1/2 and s*c<c<=1/2.

For 1/2<c<s and c^2+s^2=1, the complete interval gives

    c+s>(1+sqrt(3))/2>27/20,

using sqrt(3)>17/10. The actual circle corner in (9) would have

    |(Z_0)_y|=f+s+c>89/120+27/20=251/120
                              >25/12>sqrt(Q)>=R.

This is impossible. The last strict radius bound follows from
(25/12)^2-Q=55/2304>0.

## 5. The entire Z_1 physical-corner row also exceeds the circle

If Z=Z_1, equation (8) gives theta=(f+s)/(f+c)<=1, hence s<=c.
Its x coordinate gives the exact identity

    s*(f+c+s-epsilon)=c*(c-epsilon).                (11)

### 5.1. Two whole-interval component bounds

First c>9/10. If c<=9/10, then c>=s and normalization imply

    s>=sqrt(19)/10>2/5,
    c+s>=9/10+sqrt(19)/10>13/10.

For the second inequality, c+sqrt(1-c^2) decreases on
[1/sqrt(2),9/10], so its minimum is at the displayed endpoint.
Since f-epsilon>29/40, the left side of (11) is strictly greater
than

    (2/5)*(29/40+13/10)=81/100>=c^2,

whereas its right side is at most c^2. This is a contradiction.

Second s>1/3. If s<=1/3, then the right side of (11) is greater
than

    8/9-1/60=157/180,

while its left side is less than

    (1/3)*(1+1+1/3)=7/9<157/180.

This uses f<1, c<1 and epsilon<1/60 on the entire interval.
Thus

    c>9/10, s>1/3, s<c.                            (12)

### 5.2. The complete range f>=4/5

Normalization and (12) give

    c+s>(sqrt(8)+1)/3>5/4.

Here the sum increases with s on 0<s<=1/sqrt(2), and
sqrt(8)>11/4. Consequently the actual Z_1 in (9) satisfies

    |(Z_1)_x|>5/4-1/60=37/30,
    |(Z_1)_y|>4/5+9/10=17/10.

Its squared radius is therefore greater than

    (37/30)^2+(17/10)^2=397/90>Q,
    397/90-Q=1091/11520>0.                          (13)

### 5.3. The complete range f<=4/5

In this range, (11) further gives s>3/8. Otherwise its right side
would exceed

    55/64-1/60=809/960,

while its left side would be less than

    (3/8)*(4/5+1+3/8)=261/320=783/960.

Hence normalization gives

    c+s>(sqrt(55)+3)/8>13/10,

using sqrt(55)>37/5. The same actual corner now has

    |(Z_1)_x|>13/10-1/60=77/60,
    |(Z_1)_y|>89/120+9/10=197/120.

Its squared radius exceeds

    (77/60)^2+(197/120)^2=62525/14400>Q,
    62525/14400-Q=59/2304>0.                        (14)

The two continuous f ranges overlap at f=4/5. Their strict
contradictions include that endpoint. Equations (13)--(14) exclude
the entire Z_1 row. Together with Section 4 and the full physical
mask exclusion of Section 2, every tilted T is impossible.

## 6. Exact conclusion and operative inputs

Thus T is aligned. Its actual maxima in (1) give exactly (2).
Both center coordinates in that rectangle are strictly negative,
so its unique farthest corner is (epsilon-1,-f-1). Since the original
circle load has positive total, that corner is physical boundary,
and (3) follows.

The full-star grouping was used only under the contradicted tilted
frame, where the actual supporting points are unique. At an aligned
T the original East/North means may be distinct arbitrary side
points, and no reduction to two applications is asserted or needed.

| Source | SHA256 | Literal operative use |
| --- | --- | --- |
| LOADED_TWO_APPLICATION_FULL_STAR_BOUNDARY_FREE_CONCURRENCE_DICHOTOMY.md | 3808b2b767a9e15c7270b50c4fbbb434ae0d69fe42c567d4da01f7d167f7fa78 | Complete physical mask classification; arbitrary-degree actual two-application nonparallel properness; inside clause only for the unique physical corner |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Unchanged full force/torque, original positive normals at their actual support points, all physical circle coefficients |

Both sources were read completely before this construction. The
declared radius satisfies sqrt(2)<R<1+sqrt(2), so the full 3808
theorem applies without dropping either original radius endpoint.
Every neighbor and every other packing unit remains physically
present. No graph family is declared closed by this local rigidity
theorem alone. No computational certificate, numerical pose, angle
mesh, Lean/Lake, CI, normal reselection, mean replacement, force
deletion, metadata edit, staging, commit or remote action is used.
Separate full independent and root review are required for adoption.
