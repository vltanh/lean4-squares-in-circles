# A genuine S-leaf root within one tenth of the origin has at most two boundary neighbors

Date: October 27, 2026. Author: mixed_blocks.

**Status: complete proposed physical theorem and exact genuine-root
consequence, frozen for full independent and root review.** No original
cell, load gate, equality packing, shared ledger or remote object is
declared closed by this source.

Every square and every physical contact below is an unchanged actual
unit square or contact. Physical boundary status permits zero individual
circle weights. No force, mean, normal or positive degree is replaced.

## 1. Full statement and elementary physical bounds

Put Q=1105/256 and suppose

    sqrt(17)/2<R<=sqrt(Q),
    d=sqrt(R^2-1/4)-1=1+epsilon,
    0<epsilon<eta=1/60.

Let an actual root have the own chart

    X=[a,1+a] x [-beta,1-beta],
    0<a<=epsilon, 0<=beta<=1/10.                    (1)

Suppose its real S leaf L has its unchanged center of one of the
following two kinds:

    aligned: a=epsilon, C_L=(d+1/2,0);
    tilted: P=(1+a,-beta), |P|=d,
            C_L=(1+1/(2d))*P.                      (2)

In both cases L physically touches X and the circle, and all actual
units have disjoint open interiors.

**Theorem.** Every physical boundary neighbor of X other than L belongs
to a single center set of diameter strictly less than one. In particular
X has at most two distinct physical boundary neighbors in total.

An arbitrary contained actual unit center C satisfies

    |C|<M=91/60.                                    (3)

Its farthest squared corner norm is at least |C|^2+|C|+1/2, and
M^2+M+1/2-Q=31/57600>0. A physical boundary center also satisfies

    |C|^2>183/100.                                  (4)

Indeed |C|>=R-1/sqrt(2), and
(sqrt(17)/2-1/sqrt(2))^2=19/4-sqrt(17/2)>183/100,
because sqrt(17/2)<73/25. Every point of a boundary square has norm
at least R-sqrt(2)>1/2. Every point of any square lies within
1/sqrt(2)<17/24 of its center. Distinct actual centers have distance
at least one, by their open radius-1/2 incircles.

All of (3)--(4) are physical statements, independent of the circle
weights and the number of positive forces.

## 2. A complete contained-wall estimate on the whole required interval

Let 9/10<=A_0<=1 and 0<q<=7/20 satisfy

    (A_0+1)^2+(q+1/2)^2>Q.                          (5)

We claim that any contained actual unit E in x>=A_0 has

    |C_E,y|<q.                                      (6)

Reflect vertically if necessary and suppose C_E,y>=q. Write its
actual own-axis tilt as c>=s>=0, c^2+s^2=1. Its horizontal half-width
is (c+s)/2 and C_E,x>=A_0+(c+s)/2.

If s>=1/5, its actual rightmost corner has x coordinate at least

    A_0+c+s>=11/10+sqrt(24/25)>133/64>R.

The exact first radical reserve is
24/25-(133/64-11/10)^2=67/20480>0; the second squared reserve is
(133/64)^2-Q=9/4096>0.

It remains that 0<=s<1/5, so c>24/25. For one sign of the actual
tilt the upper right corner has coordinates at least
(A_0+c, q+(c+s)/2), componentwise. For the other sign, the rightmost
upper corner has coordinates at least
(A_0+c+s, q+(c-s)/2). The difference of this latter squared lower
bound and the former is

    (2A_0+c-2q)*s+s^2>=0.

Both are positive-coordinate comparisons, so an actual squared
corner norm is at least

    F(s)=(A_0+c)^2+(q+(c+s)/2)^2.

Using c-1=-s^2/(1+c), 2A_0+q<=47/20 and c>24/25 gives

    F(s)-F(0)
      =(2A_0+q)(c-1)+q*s+c*s/2-s^2
      >=s*(q+12/25-(431/196)*s)>=0.

The bracket is positive throughout 0<=s<=1/5, because
12/25-431/980=197/4900>0. Thus F(s)>=F(0)>Q by (5), a
contradiction. The case s=0 and both signs of tilt were included.
This proves the whole wall statement (6), not only an aligned wall.

## 3. Every southeast boundary neighbor coincides with the real leaf

Use the actual southeast corner P=(1+a,-beta), east own side and
south own side of X. We prove that each boundary neighbor E supported
there has center C satisfying

    C_x>1, -97/120<C_y<3/20.                         (7)

For a strict southeast normal n=(c,-s), c,s>0, the application is
P. If P is an E vertex, its open tangent quadrant avoids X's open
northwest quadrant. The exhaustive closed possibilities are that
its inward edges both have nonnegative x component or both have
nonpositive y component. In the first case the opposite corner's
squared norm is at least

    1+2+2-2/10=24/5>Q,

which is impossible. In the second case P is a highest vertex,
so C_y<=-beta-1/2<0.

If P is in a relative interior of an E side, put j=(s,c) and write
the unchanged actual center as

    C=P+n/2+k*j, -1/2<k<1/2.

Suppose C_y>=3/20. Then k=(C_y+beta+s/2)/c>0. The actual corner
Z=C+(n+j)/2 has

    Z_x>=2+(13/20)*s.

For s>=1/2 this already exceeds R. For 0<s<=1/2 it also has
Z_y>=13/20-3s/4>0. Its squared norm is therefore at least

    (2+(13/20)*s)^2+(13/20-3s/4)^2>Q.

The constant term minus Q is 679/6400, the linear coefficient is
13/8 and the quadratic coefficient is positive. Thus C_y<3/20
for the whole strict southeast feature, including every actual mean.
Vertex endpoints were treated separately.

For an east-axis contact, E lies in x>=1+a>=1. Apply Section 2
with A_0=1,q=3/20; condition (5) has the same reserve679/6400.
For a south-axis contact E lies in y<=-beta, so C_y<=-beta-1/2.
In the strict-corner and south-axis cases the original contact itself
and the circumradius bound give C_y>-1/10-17/24=-97/120. The east
case already has the stronger bound from the wall estimate.

By (4), these vertical bounds imply

    C_x^2>183/100-(97/120)^2=1+2543/14400>1.

The negative branch is impossible: each such actual contact has
nonnegative x coordinate, so C_x>-17/24>-1. This proves (7).

The actual real leaf in (2) satisfies

    1<(C_L)_x<M, -3/20<=(C_L)_y<=0.

For the tilted case (C_L)_x>1+30/61 and its negative ordinate has
absolute value at most (3/2)beta<=3/20. The aligned case is direct.
If E were distinct from L, (3),(7) would give

    |C-C_L|^2<(31/60)^2+(97/120)^2
      =1-1147/14400<1,

contradicting their actual open incircles. Thus no distinct physical
boundary neighbor can occur in any southeast or corresponding axial
feature. No leaf force or other multiplier has been changed.

## 4. The entire northwest neighbor family: five exact intervals

Interchange the own coordinate axes only for this section. The
original northwest corner becomes

    p=(A,a), A=1-beta in [9/10,1], 0<a<=eta.

The root tangent quadrant there is northwest. Its strict southeast
normal, east axis and south axis now represent exactly the original
northwest neighbor family. Fix the row containing the actual A:

| A_lo | A_hi | q | D | L |
| --- | --- | --- | --- | --- |
| 9/10 | 23/25 | 341/1000 | 149/250 | 97439/82800 |
| 23/25 | 47/50 | 147/500 | 607/1000 | 198367/169200 |
| 47/50 | 24/25 | 61/250 | 617/1000 | 201937/172800 |
| 24/25 | 49/50 | 19/100 | 627/1000 | 205591/176400 |
| 49/50 | 1 | 13/100 | 127/200 | 41867/36000 |

Define

    K=133/100+eta^2-2*eta*q,
    L=(A_hi^2+K)/(2*A_hi).                            (8)

The table's intervals are closed and cover every possible A. Every
row has 1<L<6/5, D>=149/250>1/2, q>=13/100>eta, and the following
five strict rational inequalities:

    (A_lo+1)^2+(q+1/2)^2>Q,                          (9)
    (9/4-A_hi^2)^2>4*A_hi^2*(2-4D^2),               (10)
    K>A_hi^2,                                       (11)
    (q+D)^2+(M-L)^2<1,                              (12)
    183/100-D^2>L^2.                                (13)

Their full exact reserves are recorded in Section 6. We prove that
every actual boundary neighbor in this family has

    L<C_x<M, -D<C_y<q.                              (14)

### 4.1. All downward depth alternatives

First suppose p=(x,a), |x|<=A_hi, is a highest actual vertex of a
boundary square. Its inward edges have the form (r,-t),(-t,-r),
where r,t>=0 and r^2+t^2=1. If C_y<=a-D, then u=r+t>=2D. The
opposite actual vertex has squared norm at most

    x^2+a^2+2+2|x|sqrt(2-u^2)-2a*u
      <=A_hi^2+2+2A_hi*sqrt(2-4D^2)<17/4.            (15)

Here a^2-2a*u<=0, the radical decreases with u, and (10), with its
positive left square root, gives the strict last comparison. The
point p has norm <101/100, so p and both adjacent vertices also have
norm <201/100<sqrt(17)/2. This contradicts physical boundary status.
Thus every such highest-vertex alternative has C_y>a-D.

At the strict southeast root contact p=(A,a), an E-vertex tangent
quadrant either points rightward or downward, exactly as in Section 3.
The rightward case has an opposite actual corner of squared norm at
least

    (9/10)^2+2+9/5-1/30=Q+4997/19200>Q.

It is impossible; the downward case is (15).

For a relative side-interior contact use n=(c,-s),j=(s,c), c,s>0,
and C=p+n/2+k*j. Suppose C_y<=a-D and put t=k+1/2. Then

    0<t<1/2, s+c-2tc>=2D.

In fact t<1/5. Otherwise s+(3/5)c>=2D, whereas Cauchy gives
s+(3/5)c<=sqrt(34)/5 and 4D^2-34/25>=951/15625>0.
The four actual vertices are

    p+t*j, p-(1-t)*j, Z_+=p+n+t*j,
    Z_-=p+n-(1-t)*j.

The first two have norm <201/100. Also

    |Z_+|<101/100+51/50=203/100<sqrt(17)/2,

because |p|<101/100 and sqrt(1+t^2)<51/50.
For s<=3/4 the derivative of |Z_-|^2 in t, throughout the interval
from zero to the actual t, is

    2(A*s+a*c-1+t)
      <=2(3/4+1/60-1+1/5)=-1/15<0.

At t=0 the same full opposite-vertex estimate (15) applies, since
c+s>=2D. Therefore |Z_-|^2<17/4. If s>3/4, then c<2/3 and

    -1/10<Z_-,x<67/60, |Z_-,y|<sqrt(2).

The second inequality uses a>=0 and a<s. Consequently
|Z_-|^2<(67/60)^2+2<17/4, with reserve3611/3600. No corner is on
the circle, another contradiction. This proves C_y>a-D in the whole
relative side-interior case, retaining all original sliders.

For a south-axis contact the top of E is y=a. A horizontal top side
gives C_y=a-1/2>a-D. Otherwise the actual contact is its highest
vertex (x,a), with x in [A-1,A] and hence |x|<=A_hi; (15) applies.
Thus all south-axis endpoints are included. East-axis contacts have
|C_y|<q<D directly from Section 2 and (9).

### 4.2. The whole upper bound

The surviving downward E-vertex case has C_y<=a-1/2<0<q.
For a side-interior case suppose C_y>=q. Then
k=(C_y-a+s/2)/c>0 and the actual corner Z=C+(n+j)/2 satisfies

    Z_x>=A+1+(q+1/2-eta)*s.

For s>=1/2 this exceeds 263/120>25/12>R, using A>=9/10 and
q>1/10. For 0<s<=1/2, its positive ordinate obeys
Z_y>=q+1/2-3s/4. Hence its squared norm is at least

    (A_lo+1+(q+1/2-eta)*s)^2
      +(q+1/2-3s/4)^2.                              (16)

Its constant term exceeds Q by (9); its linear coefficient is

    (2A_lo+1/2)(q+1/2)-2(A_lo+1)*eta
       >197/150>0,

and its quadratic coefficient is positive. Thus (16)>Q throughout
the whole interval, a contradiction. South-axis contacts have
C_y<=a-1/2<q. East-axis contacts use the full wall theorem. This
establishes C_y<q in every case, including both sets of endpoints.

### 4.3. The longitudinal coordinate and actual diameter

At a strict corner contact, (4) and |C-p|^2<=1/2 give

    2A*C_x>133/100+A^2+a^2-2a*C_y
             >=133/100+A^2+eta^2-2eta*q=A^2+K.

The weak comparison is sufficient because the first inequality is
strict. It uses q>eta and 0<a<=eta. By (11), (A^2+K)/(2A)
decreases throughout the actual closed A interval, so C_x>L.
For an east-axis contact C_x>=A+1/2>=7/5>L.
For a south-axis contact -D<C_y<a-1/2<0, so (4),(13) give
C_x^2>L^2. Its actual contact has x>=A-1>=-1/10, whence
C_x>-1/10-17/24=-97/120>-1. The negative branch is impossible
because L>1. Thus C_x>L there too.

Equation (3) supplies C_x<M. We have proved the complete rectangle
(14). Its squared diameter is strictly less than one by (12), so
it contains the center of at most one actual unit. The parameters
in a row depend only on the original root's A, and hence are the
same for every one of its neighbors.

## 5. Complete normal cover and genuine-root consequence

In the original X chart, every strict southwest normal exposes the
actual vertex S=(a,-beta), of norm at most sqrt(1/3600+1/100)<1/2.
It cannot belong to a physical boundary square. Every strict
northeast normal exposes W=(1+a,1-beta). An actual neighbor with
minimum support at W in a unit direction n contains W+n: at a side
point this is unit width, and at a vertex the inward components of
n on its two orthogonal unit edges belong to [0,1]. For northeast n,

    |W+n|^2>=1+(9/10)^2+1+9/5
      =461/100=Q+1879/6400>Q.

Thus that entire feature is impossible. Section 3 covered the strict
southeast quadrant, east axis and south axis. Section 4, after the
stated coordinate interchange, covered the strict northwest quadrant,
north axis and west axis. These are all four strict normal quadrants
and all four axes, for any owner and every actual mean or endpoint.

Every physical boundary neighbor distinct from L is consequently in
the one rectangle of Section 4. Its diameter contradiction proves
the theorem in the complete scope of (1)--(2).

Here is the exact genuine-root consequence used in the remaining
original mixed domain. Let X be any actual origin-free root of a
genuine S leaf in the present radius interval. The full degree-free
leaf geometry gives the actual positive-axis chart

    X=[a,1+a] x [-beta,1-beta], 0<a<=epsilon.

For an aligned root the full interval is 0<=beta<=1 and its leaf
center is the first alternative (2); transverse reflection is allowed.
For a tilted root the complete chart has 0<beta<11/60 and the second
alternative (2). These are precisely the physical chart statements
in 9036a1a8 Section 1 and 45dcd1b8 Sections 3--4; no concurrence or
shortened star at a higher-degree root is used here.

If this actual root had a vertex in the closed D_(1/10), the far
vertices, with own x=1+a>1, could not be that vertex. In the aligned
case reflect transversely so that the near vertex becomes
(a,-beta) with beta<=1/10. In the tilted case the other near vertex
has height >49/60, so the same conclusion already holds. The entire
proved theorem would permit at most two physical boundary neighbors.
Consequently a genuine root with three distinct physical boundary
neighbors has **every actual vertex strictly outside D_(1/10)**.

For the original D_th private root Y, its real leaf L_Y, private K3
and private T2 are three such distinct actual boundary neighbors.
Their positive degrees and all full forces remain unchanged. Thus
this consequence applies to that full original root, independently
of the shape or equation of its other actual neighbor H.

## 6. Exact scalar checks and operative source scopes

For rows1--5 of Section 4 the exact positive reserves in (9) are

    3499/4000000, 1719/4000000, 2919/4000000,
    207/160000, 143/160000.

The reserves in (10), after the displayed squaring, are

    1464081/156250000, 1130241/156250000,
    833481/156250000, 3257129/156250000, 141/10000.

Those in (11) are

    21263/45000, 39319/90000, 36049/90000,
    32719/90000, 5867/18000.

The full diameter reserves 1-(q+D)^2-(M-L)^2 in (12) are

    1117728251/171396000000,
    49861735259/715716000000,
    102673327559/746496000000,
    162726322139/777924000000,
    375419111/1296000000.

The south-axis reserves 183/100-D^2-L^2 in (13) are

    15413110439/171396000000,
    62318768291/715716000000,
    62441065031/746496000000,
    61084953779/777924000000,
    96254711/1296000000.

Additional strict reserves used above include

    67/20480, 197/4900, 4997/19200, 951/15625,
    223/11250, 1/2500, 1291/10000, 1/30,
    3611/3600, 1879/6400, 2543/14400, 1147/14400.

Sections 1--5's physical theorem is fully proved here. Only the final
genuine-root chart extraction invokes these frozen complete inputs:

| Source | SHA256 | Exact used scope |
| --- | --- | --- |
| ROOTED_C3_334_PRIVATE_ADJACENT_LEAF_TWO_LOAD_C4_EXCLUSION.md | 9036a1a8c2b1c7e0f713eef3e0dc3bacbecb42d588332120cf9e04c27ffa98c5 | Section 1's complete aligned and tilted genuine-leaf physical charts, arbitrary contained nonleaf neighbors. |
| GENERAL_GENUINE_FOUR_BLOCK_DECORATED_HUB_DIAMOND_COMPLETE_EXCLUSION.md | 45dcd1b830306b0ab32429e91b8aaeda5561d2ea3c05ef102ef4b5ce1ecab99f | Sections 3--4's complete actual genuine X4 physical charts and true private boundary status; no genuine-Q0 path conclusion. |

The interval rows are exact continuous geometric estimates for the same
actual root, not new load domains, fine labels or a sampled pose list.
No actual unit was moved; no mean, force, circle atom, degree, ledger,
source header, Lean file, CI state or remote object was changed.
