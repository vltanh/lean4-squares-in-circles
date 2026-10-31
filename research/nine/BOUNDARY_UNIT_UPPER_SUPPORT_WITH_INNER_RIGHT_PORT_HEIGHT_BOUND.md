# A boundary unit above an inner right port has a uniform minimum height

Date: October 28, 2026 UTC. Author: fan_finish_v2 continuation.

**Status: complete proposed force-free physical height theorem,
frozen for separate full independent and root review.** The proof
covers one whole continuum of actual unit frames and original side
positions with elementary inequalities, without an exclusion packet.

## 1. Complete physical statement

Let an actual unit square A lie in the disk about the unchanged
origin of radius R, and physically touch that circle. Suppose

    R^2=(2+epsilon)^2+1/4,
    epsilon>=0, |h|<=epsilon,
    p,q>=0, p^2+q^2=1,
    m=(-q,p), w=(p,q),
    A=(h+x,g)+[0,1]m+[0,1]w.                       (1)

Suppose the same actual A contains the original side point

    Q=(h+x,g)+rho*w=(h+beta,g+rho*q),
    0<=rho<=1, beta=x+rho*p>=0,
    x<=0, 0<=Q_y<=1.                              (2)

Thus the actual lower corner has abscissa at most h, and its
actual point Q on the side in direction w has abscissa at least h.
Every closed endpoint in (1),(2) is retained. There is no load,
degree, force, second physical unit or origin-interior premise.

**Theorem.** The exact minimum height of this actual A satisfies

    g>4/7.                                        (3)

No containing-circle upper bound beyond the displayed radius
relation is needed in the proof. The horizontal displacement
h may have either sign. A graph caller must supply the actual
frame and actual point Q in (1),(2); a center-position sketch is
not a substitute for those hypotheses.

## 2. The entire horizontal interval and the nonpositive-height case

Equations (2) give

    -rho*p<=x<=0,
    0<=g+rho*q<=1.                               (4)

Temporarily subtract h from the horizontal coordinates of the four
actual corners only for scalar bookkeeping. Their resulting pairs are

    U0=(x,g),
    U1=(x-q,g+p),
    U2=(x+p,g+q),
    U3=(x+p-q,g+p+q).                             (5)

The actual corners are (h+(Ui)_x,(Ui)_y); the containing-circle
origin has not been moved. Equation (4) gives |(Ui)_x|<=p+q<=sqrt(2).
Therefore, for every one of these same actual corners,

    |(h+(Ui)_x,(Ui)_y)|^2
       <=|Ui|^2+2*sqrt(2)*epsilon+epsilon^2.       (6)

If g<=0, the lower bound Q_y>=0 gives g>=-rho*q>=-1.
Every height in (5) lies between -1 and sqrt(2). Hence |Ui|^2<=4
for every i. Since 2*sqrt(2)<4,

    4+2*sqrt(2)*epsilon+epsilon^2
      <17/4+4epsilon+epsilon^2=R^2.

All actual corners would be strictly inside the circle. Thus this
entire case is impossible, and it remains to rule out 0<g<=G=4/7.

## 3. Two easy corners and the aligned endpoint

Put t=1-G=3/7. Suppose for contradiction that 0<g<=G.
If q=0, p=1 and (4) gives -1<=x<=0. Every corner then has
|Ui|^2<=1+(1+G)^2=170/49<17/4. Equation (6) contradicts
physical boundary contact exactly as in Section 6 below.

Keep q>0. For the first and third corners of (5),

    |U0|^2<=1+G^2=65/49<17/4,
    |U2|^2<=p^2+(G+q)^2
            =1+G^2+2G*q<=(1+G)^2=121/49<17/4.    (7)

Here 0<=x+p<=p follows from -rho*p<=x<=0 and rho<=1.
The other two corners are handled over their entire allowed frame
and side-position intervals in the next sections.

## 4. The complete upper-left adjacent corner

For U1, (4) gives

    |U1|^2<=(rho*p+q)^2+(g+p)^2,
    0<=rho<=min(1,(1-g)/q).                      (8)

If q<=t, then p+q is increasing up to q=t<1/sqrt(2), and

    p+q<4/3.

Indeed its value there is (sqrt(40)+3)/7<4/3, since
sqrt(40)<19/3. Therefore (8) gives the complete bound

    |U1|^2<(4/3)^2+(11/7)^2
              =1873/441=17/4-5/1764.             (9)

Now suppose q>=t. The right side of (8) increases with rho.
If g<=1-q, its maximum is bounded by its values rho=1 and
g=1-q, giving

    |U1|^2<=(p+q)^2+(1-q+p)^2
             =3+2(p-q)
             <=(15+2*sqrt(40))/7<83/21<17/4.     (10)

If g>=1-q, substitute rho=(1-g)/q. The resulting expression

    [q+(1-g)*p/q]^2+(g+p)^2

is a convex quadratic in g. On [1-q,G] its maximum occurs at
an endpoint. The first endpoint is already (10). At the second,
the exact value is

    2G+2p+t^2/q^2=8/7+2p+9/(49q^2).

This decreases with q>=t, so its maximum at q=t is again
(15+2*sqrt(40))/7<83/21. This proves |U1|^2<17/4 throughout,
including the common boundaries q=t and g=1-q.

## 5. The complete opposite corner

For fixed p,q,g,rho, the squared norm of U3 is convex in x.
By (4) it suffices to use x=0 or x=-rho*p. The first endpoint has

    |U3|^2=(p-q)^2+(g+p+q)^2
             =2+g^2+2g(p+q)
             <2+16/49+(8/7)(99/70)
              =138/35<17/4,                     (11)

using sqrt(2)<99/70. At x=-rho*p the norm is a convex quadratic
in rho, so it suffices to use rho=0, already covered in (11),
or rho=min(1,(1-g)/q).

If q<=t, this latter value is one. By p+q<4/3,

    |U3|^2=q^2+(g+p+q)^2
             <9/49+(4/7+4/3)^2=1681/441<17/4.   (12)

Suppose q>=t. If g<=1-q, the same rho=1 expression increases
with g and is at most q^2+(1+p)^2=2+2p<=2+2*sqrt(40)/7,
which is strictly below 80/21<17/4.

It remains that q>=t and g>=1-q, with rho=(1-g)/q. The exact
opposite-corner expression is

    F(g,q)=[p-q-(1-g)*p/q]^2+(g+p+q)^2.

Its derivative with respect to g is

    2[1+1/q-(1-g)/q^2]>=2>0,

because 1-g<=q. Thus F(g,q)<=F(G,q), where exact expansion gives

    F(G,q)=15/7+2(p+q)-6/(7q)+9/(49q^2).          (13)

The last two terms form an increasing function of q on [t,1].
For t<=q<=9/10, use p+q<=sqrt(2)<99/70 and its value at
9/10 to obtain

    F(G,q)<15/7+99/35-320/441
              =9362/2205=17/4-37/8820.           (14)

For 9/10<=q<=1, p+q decreases and is at most
9/10+sqrt(19)/10<27/20. The same increasing last terms in
(13) are at most their q=1 value -33/49. Therefore

    F(G,q)<15/7+27/10-33/49
              =2043/490=17/4-79/980.             (15)

These two continuous inequalities include their shared endpoint.
They establish |U3|^2<17/4 for every original p,q,rho,x in the
whole stated domain, rather than for a sampled list of frames.

## 6. Actual circle contradiction and precise export boundary

Equations (7)--(15), together with the aligned q=0 case, show
that every Ui in (5) has squared norm strictly below 17/4 whenever
0<g<=4/7. Returning to the original actual corner coordinates by
(6), every one consequently has

    |corner|^2<17/4+2*sqrt(2)*epsilon+epsilon^2
                <=17/4+4epsilon+epsilon^2=R^2.

The first inequality stays strict at epsilon=0. Thus every actual
corner of A is inside the original containing circle. The squared
norm on a convex square is bounded by its maximum at the corners,
so the entire actual A is physically circle-clear. This contradicts
its assumed physical circle contact and proves g>4/7.

The proof is self-contained unit-square geometry. It needs no
stress, selected-normal convention, force degree, circle-corner
weight or mask choice. Both tilt-axis endpoints and every closed
position of Q are covered. The radius cap of a future nine-unit
caller can be retained, but is not a premise needed here.

This local height statement does not by itself exclude a packing,
identify a fan normal, replace any original body, or supply a
completion count. All actual units, forces and means in a graph
caller stay unchanged. The caller must independently establish
the literal actual frame and point bounds (1),(2).

No sampled pose, finite geometric exclusion certificate, numerical
optimizer, normal reselection, application replacement, force
deletion, Lean/Lake, CI, metadata/checkpoint edit, staging, commit
or publication is part of this proof. Exact scalar arithmetic was
used only to check the displayed rational identities and reserves.
Separate full independent and root review are required before
adopting these exact bytes.
