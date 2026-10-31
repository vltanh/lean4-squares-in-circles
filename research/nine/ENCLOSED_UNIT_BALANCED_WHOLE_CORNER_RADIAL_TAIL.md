# An enclosed unit has a sharper balanced radial-tail restriction from the whole witness square

Date: October 26, 2026.

**Status: complete proposed continuous geometric theorem; author full-source
and direct-prerequisite review passed. Root and separate independent
full-source reviews are pending.** The proof keeps the whole actual ray
witness and its farthest corner, both separator owners and every witness
orientation. It introduces no coefficient packet or parameter grid.

Put

    Q=1105/256, M=91/60, k=3721/7200, e=k-1/2=121/7200.

## 1. Exact physical statement

Let

    T=(a,b)+[-1/2,1/2]^2,
    3/8<=a<=k,        2a/3<=b<=a.                         (1)

Let S be any actual unit square interior-disjoint from T, contained in
the disk D_R about the unchanged origin, where R^2<=Q. Suppose S meets
the actual outgoing radial ray {t(a,b):t>1} beyond T. No physical circle
contact, positive load, force, common frame or contact-owner assumption
is made for S.

**Whole-corner radial-tail theorem.** Necessarily

    R^2 >= F_R(a,b):=(a+3/2)^2+[b(1+1/(2a))]^2.          (2)

The formula retains the actual whole-square containment. In contrast,
C7_SHARP_BALANCED_RADIAL_TAIL.md bounds only the witness center norm.
The present domain also includes 3/8<=a<9/20. The square S is never
replaced by an independently placed point.

For an enclosed actual unit T, the outgoing-ray property of the physical
ring supplies exactly such an actual S. The ring can have any number of
bodies. Consequently (2) holds for every enclosed T satisfying (1),
with signs and own axes chosen to put its center in this ordered sector.

The bound is sharp wherever its equality example belongs to the stated
disk: the aligned square with center

    (a+1, b(1+1/(2a))-1/2)

touches T's right face and the outgoing ray at its upper-left corner.
Its actual farthest corner has squared norm F_R(a,b).

## 2. A separator owned by T: complete witness-frame cover

An actual square-owned separating axis exists. If T owns it, only the
positive horizontal or positive vertical normal is possible, because
S meets the positive outgoing ray beyond T. We treat both, keeping the
entire arbitrary orientation of S.

For a rightward separator put

    X=a+1/2, q=b/a, g=qX=b(1+1/(2a)).

Then S lies in x>=X and meets the line y=qx. Let (C_x,C_y) be its
center. Choose its frame up to exchanging its side axes so that

    u=cos(phi), v=sin(phi), 0<=phi<=pi/4,
    h=(u+v)/2, j=(u-v)/2.

The two reflected orientations of this frame are both retained.
In either one C_x>=X+h. We have

    7/8<=X<21/20,       2/3<=q<=1,       g>0.             (3)

### 2.1. The first actual orientation

Its leftmost and topmost vertices relative to the center are
(-h,j) and (j,h). If v/u<=q, the maximum of y-qx on S occurs at
the leftmost vertex (or the connecting side at equality). Since S
meets y=qx,

    C_y-qC_x+j+qh>=0,

so C_y>=g-j. Its actual topmost vertex has coordinates at least
(X+u,g+v), both positive. The squared norm of that vertex is at least
F_R, because

    (X+u)^2+(g+v)^2-[(X+1)^2+g^2]
      =2Xv[q-v/(1+u)] >=0.                              (4)

Here v/(1+u)<=sqrt(2)-1<1/2 and q>=2/3. The aligned v=0 endpoint
is included with equality.

If v/u>q, then phi>atan(2/3), so

    u+v>5/sqrt(13)>4/3.

The rightmost actual vertex has first coordinate greater than X+4/3.
Using g<=X, its squared norm exceeds F_R since

    (X+4/3)^2-[(X+1)^2+X^2]
       =-X^2+(2/3)X+7/9 >0.                            (5)

The quadratic is concave. Its values at X=7/8 and21/20 are
343/576 and1351/3600, respectively, both positive. This is one
whole interval comparison, not a sampled frame argument.

### 2.2. The reflected actual orientation

Here the topmost and rightmost vertices relative to the center are
(-j,h) and (h,j). Since qv<=v<=u, the maximum of y-qx is attained
at the topmost vertex. Thus

    C_y-qC_x+h+qj>=0,
    C_y>=g-h+qv.

Its actual rightmost vertex has coordinates at least

    (X+u+v, g-(1-q)v).

The second coordinate is positive: g>=7/12 and
(1-q)v<1/3. Subtracting F_R from this vertex's squared lower bound gives

    v[2u+2X(1-q+q^2-v/(1+u))+(1-q)^2v] >=0.            (6)

Every term has the required sign, using 1-q+q^2>=3/4 and
v/(1+u)<1/2. Again the aligned endpoint is retained. Equations
(4)--(6) prove the complete rightward T-owned alternative.

### 2.3. The upward T-owned alternative

Exchange the two displayed coordinates only for this case. Now

    X=b+1/2>=3/4, q=a/b in[1,3/2], g=qX,
    F_U(a,b):=(b+3/2)^2+[a(1+1/(2b))]^2.               (7)

In the first orientation v/u<=1<=q, so the argument of (4) applies
throughout and bounds an actual corner by F_U.

In the reflected orientation, if v/u<=1/q, the maximum of y-qx
is at the topmost vertex. The rightmost-vertex bounds from Section2.2
then have second coordinate g+(q-1)v>=g and first coordinate
X+u+v>=X+1. They give squared norm at least F_U.

If v/u>1/q>=2/3, the actual rightmost vertex instead has first
coordinate greater than

    X+4/3>=3/4+4/3=25/12>sqrt(Q).

This contradicts containment directly; the exact squared reserve is
(25/12)^2-Q=55/2304>0. Thus this entire remaining orientation cannot
occur for S in the stated disk.

Finally F_U>=F_R throughout (1). To check it, put rho=a/b in[1,3/2].
Direct expansion gives the exact identity

    F_U-F_R
      = b(rho-1)^3/rho
        +(rho-1)(rho+1)(rho^2+1)/(4rho^2) >=0.          (8)

This finishes every T-owned separator, including both own axes and
every original support transition of S.

## 3. A separator owned by S: keep its actual farthest corner

Let n be an actual own unit normal of S directed from T toward S,
and let m be a perpendicular own unit normal. Put

    z=(a,b), z_n=n dot z, z_m=m dot z,
    H=z_n+(|n_x|+|n_y|)/2.

Ray membership implies z_n>0. Otherwise every t>1 would have
t z_n<=z_n<H, while separation requires every S point to have
normal projection at least H. Therefore H>0 and

    lambda=H/z_n>1.

If t z belongs to S, separation and its two actual side strips give

    n dot C_S>=H+1/2,   t>=lambda,
    |m dot C_S|>=max(t|z_m|-1/2,0).

The actual farthest corner of S has squared norm
(|n dot C_S|+1/2)^2+(|m dot C_S|+1/2)^2. Consequently

    R^2 >= (H+1)^2+max(lambda|z_m|,1/2)^2
         >= lambda^2(a^2+b^2)+2H+1 =:F(n).             (9)

The second inequality is valid on every tangential clipping branch.
It does not discard the farthest-corner term when z_m=0.
We prove F(n)>=F_R for the complete allowed normal domain.

## 4. The whole positive normal quadrant

Put A=a+1/2, B=b+1/2, d=a-b>=0 and L=a^2+b^2. Notice

    B>(4/5)A,       A^2<2B^2.                          (10)

Indeed B-(4/5)A>=1/10-(2/15)a>0 because a<=k<21/40.

### 4.1. From the horizontal axis through the diagonal

For n=(1,t)/sqrt(1+t^2), 0<=t<=1, write D=a+bt. Then

    lambda=1+(1+t)/(2D), H=(A+Bt)/sqrt(1+t^2),
    lambda'=d/(2D^2), lambda''=-bd/D^3.

The function lambda^2 is concave, since

    (lambda^2)''=d[d-4b lambda D]/(2D^4) <=0.

For d>0 the bracket is strictly negative: d<=a/3, b>=2a/3 and
lambda D=D+(1+t)/2>=a+1/2 give
4b lambda D>=4(2a/3)(a+1/2)>a/3.
When d=0 the derivative is zero.

Also H is strictly concave. Its second derivative has numerator

    -A+2At^2-3Bt
      <= A[-1+2t^2-(12/5)t] <0                       (11)

on the whole interval. The final quadratic is convex and is negative
at both endpoints. Thus F=L lambda^2+2H+1 is concave. Its minimum
on this complete angular sector is attained at one of its two endpoints.

### 4.2. From the vertical axis back to the diagonal

For n=(t,1)/sqrt(1+t^2), 0<=t<=1, put D=b+at. Then

    lambda=1+(1+t)/(2D), H=(B+At)/sqrt(1+t^2),

and direct differentiation gives

    F'=-L d lambda/D^2+2(A-Bt)/(1+t^2)^(3/2).           (12)

If d=0, the right side is nonnegative, and the minimum is at the
vertical endpoint. Suppose d>0. Every factor below is positive, and
the sign of (12) is the sign of G(t)-Ld, where

    G(t)=2(A-Bt)D^3/[(B+At)(1+t^2)^(3/2)].              (13)

The logarithmic derivative of G has the sign of

    N(t)=3(a-bt)(A-Bt)(B+At)
               -(A^2+B^2)(b+at)(1+t^2).

Write N=c_0+c_1t+c_2t^2+c_3t^3. Its coefficients are

    c_0=3aAB-b(A^2+B^2),
    c_1=2aA^2-4aB^2-3bAB<0,
    c_2=-3aAB-4bA^2+2bB^2<0,
    c_3=3bAB-a(A^2+B^2).

The sign of c_1 follows from (10); c_2<0 uses A>=B.
Moreover N is strictly decreasing. This is immediate if c_3<=0.
If c_3>0, use a>=b and A>=B to obtain

    2c_2+3c_3 <= b(3AB-11A^2+B^2) <=-7bA^2<0.

For0<=t<=1 it follows that
N'=c_1+2c_2t+3c_3t^2<=c_1+t(2c_2+3c_3)<0.

Therefore G can only increase and then decrease, with either part
possibly empty. Its superlevel sets are intervals. At t=0 one has
F'>0. After cancelling positive factors, this last claim is

    2A b^3 > LdB.

Put rho=a/b in[1,3/2]. The difference after division by b^3 is

    [2rho-(rho-1)(rho^2+1)]b
       +1-(rho-1)(rho^2+1)/2 >0,                      (14)

because (rho-1)(rho^2+1)<=13/8, so its two coefficients are at
least3/8 and3/16. Thus G(0)>Ld. The sign of F' can consequently
change at most once, from positive to negative. F increases and then
possibly decreases, and its minimum is at an endpoint of this whole
sector. No angular sample or subdivision is used.

### 4.3. The three intrinsic endpoint values

At n=e_x, F=F_R. At n=e_y, F=F_U>=F_R by (8).
At the common diagonal, with T_0=a+b, Cauchy gives

    F >= [(T_0+1)/sqrt(2)+1]^2
       >= [(1+5a/3)/sqrt(2)+1]^2.

On the other hand F_R<=(a+3/2)^2+(a+1/2)^2. The difference of
the displayed lower bound and this upper bound is

    -(11/18)a^2+[(5sqrt(2)-7)/3]a+sqrt(2)-1
       > 2/5-(11/18)a^2
       > 741/3200>0,                                 (15)

using sqrt(2)>7/5 and a<21/40. Thus the diagonal value also exceeds
F_R. Sections4.1--4.3 cover the entire positive normal quadrant.

## 5. Both complete mixed-sign normal sectors

For n=(1,-t)/sqrt(1+t^2), positivity z_n>0 gives0<=t<a/b.
Put D=a-bt>0. Here

    lambda=1+(1+t)/(2D), lambda'=(a+b)/(2D^2),
    H=[a+1/2+(1/2-b)t]/sqrt(1+t^2).

Since D<=a, L>=a^2 and lambda>=1+1/(2a),

    2L lambda lambda' >=(a+b)(1+1/(2a))
                            >=(5/3)(a+1/2).

Also b<=k=1/2+e and t/(1+t^2)^(3/2)<=2/(3sqrt(3))<2/5 give

    2H'>=-2e-(4/5)(a+1/2).

Consequently

    F' >=(13/15)(a+1/2)-2e>0.                         (16)

The last sign follows already from a+1/2>=7/8 and2e<1/25.
F is increasing from its horizontal endpoint value F_R.

For n=(-t,1)/sqrt(1+t^2), use0<=t<b/a, D=b-at and interchange
a,b in the same calculation. This time a+b>=2b gives

    F' >=(6/5)(b+1/2)-2e>0,                          (17)

because b>=1/4. Its initial value is F_U>=F_R.
Normals with both coordinates nonpositive have z_n<=0 and were
already excluded. These are all remaining S-owned separators.

Equations (9)--(17) prove the theorem in the complete S-owned case.
Together with Section2, they establish (2) for every physical SAT owner,
normal sign, witness frame, tangential clipping endpoint and allowed
original actual ray encounter.

## 6. Actual ring consequence and exact scope

For a physical ring enclosing T, any ray beginning in T's open interior
and continuing to infinity must meet the actual occupied ring after it
leaves T. Otherwise its nonzero winding would remain unchanged all the
way to infinity. This supplies the actual witness S used in Section1.
The same argument applies to every compact inner portion at weak
junctions, as in SHORT_DIAMETER_CONTACT_RING_CENTRAL_CAPACITY_ONE.md.
No hypothetical hull edge or fictitious independently placed witness
is substituted for that physical S.

Thus every actual enclosed T in the balanced range (1) satisfies

    (a+3/2)^2+[b(1+1/(2a))]^2 <= R^2 <=Q.              (18)

The center-only side, corner and outside-face restrictions in the older
ring sources remain valid; (18) is an additional, stronger whole-witness
restriction. It does not assert the same formula outside (1).

For example, an enclosed unit with equal own center magnitudes a=b in
this range must obey

    2a^2+4a+5/2 <=Q.

In particular the radial-diagonal unit centered at radius3/5, whose
own coordinates are a=b=3/(5sqrt(2)), cannot be enclosed by an actual
ring in this disk. Indeed its left side is

    143/50+(6/5)sqrt(2) >143/50+42/25=227/50>Q.

This example illustrates why independent scalar center/vertex necessary
bounds do not capture actual enclosure: the whole physical witness
corner must also fit in the original disk.

For the original four-load C6 task, its one retained central unit keeps
the same actual ring enclosure, so (18) applies wherever its own center
falls in (1). The two side transmitters, every loaded neighbor, every
actual channel/cap extra, and all remaining center sectors are unchanged.
The full side/side joint (central,cap_U,cap_V)=(1,1,1) still requires
its complete exit. This local theorem closes no original gate by itself.

There is no square motion, force deletion, new normal selection, finite
coefficient packet, numerical premise, Lean compilation or CI result.
