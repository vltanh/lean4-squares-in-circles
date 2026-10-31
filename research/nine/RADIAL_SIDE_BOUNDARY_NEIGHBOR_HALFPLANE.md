# A boundary unit at a radial side lies beyond the near supporting line

Date: October 27, 2026.

**Status: complete force-free theorem and complete original S123 contact
subdomain, submitted for root and separate independent review.**
The theorem uses actual contained unit squares and their actual common
points. The caller retains the full radial physical mask and every
original force, owner, and side mean. It does not close the remaining
axis or opposite-vertex S123 root features.

## 1. A force-free boundary-center bound

Suppose actual unit squares are contained in the circle of radius R,
where

    sqrt(17)/2 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1, epsilon=d-1 in [0,1/60).

Let n,f be any orthonormal frame. Suppose a physical boundary unit E
contains an actual point Q such that

    Q.n >= d, Q.f=1/2.                                (1)

Then every point of E satisfies

    z.n > epsilon.                                    (2)

There is no force, degree, owner, or concurrence assumption in this
statement. In particular Q can be any point of an actual shared side,
including either endpoint. Reflection gives the corresponding statement
when Q.f=-1/2.

Let c be the actual center of E. Assume, contrary to (2), that
min_E z.n<=epsilon. Every unit square has half-width at most
1/sqrt(2), so

    c.n <= epsilon+1/sqrt(2).

Also |c-Q|<=1/sqrt(2). Since Q.n>=d=1+epsilon, these inequalities give

    c.n >= d-1/sqrt(2)>0,
    Q.n-c.n >= 1-1/sqrt(2),
    |c.f| <= 1/2+sqrt(1/2-(1-1/sqrt(2))^2)
           =1/2+sqrt(sqrt(2)-1).

Consequently

    |c|^2
      <= (epsilon+1/sqrt(2))^2
         +(1/2+sqrt(sqrt(2)-1))^2
      < 1/3600+(61/60)(99/70)-1/4+161/250
       =230849/126000
       =11/6-151/126000.                              (3)

Here sqrt(2)<99/70. The second radical estimate follows from

    (161/250)^2-(99/70-1)=197/437500>0,

so sqrt(sqrt(2)-1)<161/250. These are exact rational comparisons
over the entire stated radius interval.

On the other hand E has an actual circle vertex, and the distance from
its center to that vertex is 1/sqrt(2). Therefore

    |c| >= R-1/sqrt(2) >= sqrt(17)/2-1/sqrt(2),
    |c|^2 >=19/4-sqrt(17/2)>11/6.                       (4)

The last strict comparison follows from

    (35/12)^2-17/2=1/144>0,
    19/4-35/12=11/6.

Equations (3)--(4) contradict one another. This proves (2), including
the weak point condition Q.n=d and the critical radius d=1.

## 2. A radius-free projection bound from an actual support point

Let E be any unit square, let m,n be unit vectors with m.n<=0, and
let P be an actual minimum-m support point of E. Then

    max_{z in E} z.n <= P.n+1.                         (5)

This also includes every actual mean on a supporting side.

If E owns m, write an arbitrary point of E relative to its unchanged
mean P as

    r m+z j, 0<=r<=1, -1<=z<=1,

where j is a unit vector perpendicular to m. The increment in its
n projection is at most |j.n|<=1, since r m.n<=0.

Otherwise P is a strict minimum-m vertex. Write the actual square
as P+[0,1]u+[0,1]v, with u,v its orthogonal inward unit axes.
Both m.u and m.v are positive. They cannot both have positive
n projection, because then

    m.n=(m.u)(n.u)+(m.v)(n.v)>0.

Thus at most one axis contributes a positive n projection, and
that contribution is at most one. This proves (5). An axis
endpoint is already retained in the owned-side case; no point
or normal has been reselected.

## 3. Exact original radial-C S123 caller

Keep precisely the original positive component

    A--B--M--C--U--A, A--L,

with A=0,B=1,M=2,C=3,U=4. A has its genuine S leaf L and true
degree three. B,M,C retain their positive total circle loads and
true degree two. U is the true unloaded degree-two side transmitter.
All six core units and the three original completion units remain
fixed.

Use the complete necessary-domain source

    S_LEAF_C5_THREE_LOAD_TILTED_CHANNEL_DOMAIN.md
    SHA256 8cadc80c6de3a86c44f120f4a309a50af7361aec072341cb27297e47401943f2,

independently accepted in
REVIEW_S123_FAR_SUPPORT_AND_TILTED_CHANNEL_HEXAGON_2026_10_27.md.
The complete unique-C alternative is separately excluded by

    S_LEAF_C5_THREE_LOAD_UNIQUE_FAR_ENDPOINT_EXCLUSION.md
    SHA256 9172d79b0c4c553770795ae5ed0a1d3064ebf39cfee6ccfeef57f1b5d4fee2c7,

with full independent review
REVIEW_S123_UNIQUE_FAR_ENDPOINT_HEXAGON_2026_10_27.md.

Thus the remaining strict-tilted caller has the actual coordinates

    p0=(d,0), A=p0+[0,1]f1+[0,1]f2,
    f1=(-a,-b), f2=(-b,a), a>b>0, a^2+b^2=1,
    n=x f1-t f2, x>0,t>=0,x^2+t^2=1,
    f=t f1+x f2,
    h_A(n)=epsilon,
    p_AU=p0+f1+Y f2,
    Y=0 if t>0, 0<=Y<db if t=0,                       (6)
    C=[d,d+1]n+[-1/2,1/2]f,
    p_CU=d n-T f, 0<T<13/50.                          (7)

The physical radial C in (7) has two circle vertices. Both original
weights remain, including either zero individual weight. No unique-
physical-corner or inside-C concurrence conclusion is imposed on it.

Let g be the actual normal from C toward M. The original loaded C2
radial concurrence has f coordinate -T. Its full circle resultant
therefore has strictly negative f component, while the U force is
parallel to n. The full unchanged C2 equation gives

    g.f>0.

If g.n>0, its actual support point would be the upper outer circle
corner of C, which cannot be shared by a distinct contained unit.
If g.n=0, its actual point is an unchanged mean on the upper side.
If g.n<0, its actual point is the upper inner corner. Consequently
every surviving actual C--M application Q satisfies

    Q.f=1/2, Q.n>=d.                                  (8)

This exhausts the upper-side mean and both support-normal cases.
Applying Section 1 to the actual physical boundary unit M gives

    every point of M has n projection >epsilon.        (9)

The conclusion uses M's actual boundary status and does not shorten
its two positive pair forces or delete its circle load.

## 4. The whole negative first component at the direct root is excluded

Suppose the actual A-to-B normal m has m.f1<0. The exact full
root feature cover in the necessary-domain source gives

    m.f2>0, p_AB=p0+f2.

Hence

    n.m=x(m.f1)-t(m.f2)<0.                             (10)

Subtract the actual channel application in (6):

    p_AB-p_AU=-f1+(1-Y)f2,
    p_AB.n=epsilon-x-t(1-Y).                           (11)

When t>0 the original Y is zero and x+t>=1. When t=0 the
original x is one and the entire Y interval is retained.
Thus in both genuine mean cases

    p_AB.n<=epsilon-1.                                (12)

The actual B lies beyond its minimum-m support at the actual
point p_AB. Section 2 applies with the original n,m and gives

    every point of B has n projection <=epsilon.

This contradicts (9), because B and M have an actual physical
contact in the original positive cycle. No B equation, load
mask, normal ownership, or side mean was specialized.

Therefore the entire original tilted radial-C subdomain with
m.f1<0 is impossible.

## 5. Exact remaining obligation

In the strict-tilted original S123 family, the unique physical
C mask is already wholly excluded by the separately reviewed
source cited above. The present source additionally excludes
the entire radial-C first-root-component-negative feature.

The two direct-root features still retained are

    m.f1=0: the original A-owned f2 side with its full mean;
    m.f1>0: the actual opposite A vertex p0+f1+f2.

The high aligned nonparallel root also remains separate. These
domains require complete original-force exits before the full
M6.B5L.C5.L123.S family can be declared closed. The reflection
L234 has exactly the same scope.

No physical radial mask is replaced by a positive-weight mask.
No full force is omitted, no mean or normal is reselected, and
no completion unit is discarded. No new finite pose premise,
shared ledger change, remote action, compilation, or CI is used.

