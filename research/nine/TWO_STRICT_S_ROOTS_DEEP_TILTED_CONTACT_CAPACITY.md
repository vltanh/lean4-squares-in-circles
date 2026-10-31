# Two strict genuine-leaf roots with a deep tilted contact admit at most eight units

Date: October 27, 2026.

**Status: complete force-free hand capacity theorem and exact original
caller, submitted for full root and separate independent review.**
It excludes the entire one-owner strict-B domain with k>=3/20,
at every physical C/D mask. It does not claim the remaining shallow
one-owner domain closed.

Put

    d=1+epsilon,       0<epsilon<1/60,
    R^2=(d+1)^2+1/4<=Q_*=1105/256.

Keep two actual interior-disjoint unit roots with exactly the following
physical charts, in the unchanged circle coordinates:

    A=[-X,h] times [-v,1-v],       X=1-h,
    X^2+v^2=d^2,       |h|<=epsilon,
    P=(h,-k),       0<k<v<13/50;

    f=(c,s),       j=(s,-c),
    c,s>0,       c^2+s^2=1,
    B=P+[0,1]f+[0,1]j.

In the actual positively oriented (j,f) coordinates of B write

    B=[xi,U] times [-w,1-w],       U=1+xi,
    U^2+w^2=d^2,       -epsilon<xi<epsilon,
    0<w<13/50,
    h=xi*s-w*c,       k=xi*c+w*s.

The two real radial S leaves are actual distinct units with respective
inner midpoints (-X,-v) and U*j-w*f. No force or degree assumption
on any other unit is made in this physical theorem.

**Theorem.** If k>=3/20, these four actual units A,B,L,M admit at most
four further interior-disjoint unit squares in the same containing disk.
Thus they cannot occur among the original nine units.

The root charts are precisely the strict/strict sole-AB-owner domain.
The capacity argument below keeps the full original pose and actual
radial leaves; it does not replace B by a parallel square.

## 1. Exact physical scalar consequences

The two genuine radial identities and k<v give

    v^2-k^2=2(xi+h)>0,
    xi*(1+s)>w*c.

Thus xi>0, U>1, h<xi and h>-xi. In particular

    |h|<xi,
    w^2<d^2-1<121/3600.

The orthogonal coordinate identity h^2+k^2=xi^2+w^2 and k>=3/20
also give

    w^2>=k^2-xi^2
       >9/400-1/3600=1/45,
    w>4/27,
    xi=(d^2-1-w^2)/(U+1)<41/7200.                    (1)

Here (4/27)^2<1/45 follows from 720<729. Consequently

    c<2xi/w<(41/3600)*(27/4)=123/1600<1/12,
    s>143/144,
    c/s<12/143<1/8.                                  (2)

The inequality for s follows from
s^2>143/144 and sqrt(143/144)>143/144.

Let

    phi=arctan(c/s),
    phi_A=arctan(v/X),       phi_B=arctan(w/U).

The real j axis has world angle -phi. The two actual radial leaf
directions have angles pi+phi_A and -phi-phi_B. From (2),

    0<phi<arctan(1/8)<pi/24.                          (3)

The last comparison follows from arctan(1/8)<1/8<pi/24, using pi>3.

We shall need the strict bounds

    1/7<phi_A,phi_B<pi/12.                            (4)

For the lower bounds, use X,U<61/60 and (1):

    v/X>9/61>14/97,
    w/U>80/549>14/97.

The elementary estimates sin x<x and cos x>1-x^2/2 give
tan(1/7)<14/97, so both angles exceed 1/7.

For the upper A bound, v/X<78/295<2-sqrt(3)=tan(pi/12).
The exact latter radical comparison has reserve
512^2-3*295^2=1069>0. For B,
w/U<11/60<1/4<2-sqrt(3). This proves (4).
All inequalities are strict even when the original k equals 3/20.

## 2. A small-circle arc occupied by any unit meeting D_(1/8)

Set

    rho_0=7/50,       eta=1/8.

We first prove a physical local fact: any closed unit square T meeting
the closed disk D_eta occupies a connected arc of the radius-rho_0
circle of angular length strictly greater than pi/18.

Use its actual closest point to the origin, without moving T. If O
lies in T, choose the signs of its axes toward the farther endpoint
in each coordinate. Each such endpoint is at least 1/2 away, so
T contains a full quarter-circle arc of radius rho_0.

If the closest point is in a side, let the inward normal be u and
orient its perpendicular v toward the farther side endpoint. Then
T contains on this small circle the arc

    x.u>=a,       x.v>=0,

where 0<=a<=eta and both far coordinate bounds exceed rho_0.
The same assertion with two nonnegative thresholds applies at a
closest vertex: use the two actual inward axes u,v, so the closest
point has coordinates a,b>=0 with a^2+b^2<=eta^2. Again the
actual upper bounds a+1,b+1 exceed rho_0. These statements include
side endpoints and the possible zero coordinate limits.

Thus in every case there is an actual connected circle arc of length
at least

    pi/2-alpha-beta,
    alpha=arcsin(a/rho_0), beta=arcsin(b/rho_0),
    (a^2+b^2)/rho_0^2<=625/784<1.                    (5)

Write x=a/rho_0, y=b/rho_0 and z=x^2+y^2. A direct calculation gives

    cos(alpha+beta)
      =sqrt(1-z+x^2*y^2)-x*y
      >=1-z>=159/784.

For precision, at fixed z<1 the first expression decreases with
p=x*y, while p<=z/2; its value at z/2 is 1-z. Also
alpha+beta<pi/2 because z<1.

Now

    cos(4*pi/9)=sin(pi/18)<pi/18<11/63<159/784,

using pi<22/7. Hence alpha+beta<4*pi/9, and the actual arc
in (5) has length strictly greater than pi/18. In the side or
origin case its larger arc satisfies the same conclusion.

No containment or stress assumption on T is needed for this local
small-circle fact.

## 3. The actual two roots leave less than one sixth radian free

On the radius-rho_0 circle, the actual A and B are exactly the
following two half-plane intersections:

    A: x<=h,
    B: j.x>=xi.                                       (6)

Indeed X>59/60, v>k>=3/20>rho_0 and 1-v>37/50 make all
other A faces irrelevant on this circle. For B, (1) gives
w>4/27>rho_0, while 1-w>49/60 and U>1, so only its
actual j-minimum face can meet the circle.

Their occupied arcs have disjoint interiors, because the actual
square interiors are disjoint. Their angular lengths are

    pi+2arcsin(h/rho_0),
    pi-2arcsin(xi/rho_0).

Therefore the total unoccupied circle length is

    2[arcsin(xi/rho_0)-arcsin(h/rho_0)]
      <4arcsin(xi/rho_0).                            (7)

Here |h|<xi was proved physically, not imposed as a symmetric
replacement of the two support lines.

By (1),

    0<xi/rho_0<41/1008<1/20.

On [0,1/20], the derivative of arcsin is below 101/100.
Consequently (7) is strictly smaller than

    (101/25)*(41/1008)=4141/25200<1/6.                (8)

Any further actual unit T meeting D_(1/8) would, by Section 2,
occupy on this same circle an arc longer than pi/18>1/6.
That arc cannot meet an open arc in either actual root, because
the square interiors are disjoint. This contradicts (8).

Thus **every actual unit other than A and B has distance strictly
greater than 1/8 from the origin**. The conclusion is strict:
we excluded intersection with the closed disk, and actual squares
are compact. No assertion at mere equality is imported into a
connected-arc theorem.

## 4. Four actual occupied pieces on the 9/8 circle

Set rho=9/8 and theta=arctan(4/5). The unchanged A contains the
radius-rho point of angle pi-theta in its open interior. In
coordinates its absolute horizontal coordinate and height are

    45/(8sqrt(41)),       9/(2sqrt(41)).

The horizontal coordinate is strictly below 59/60 and above
|h|; the height is strictly below 37/50. These are direct squared
rational comparisons. Thus every A face has a strict margin.

The unchanged B likewise contains in its open interior the
radius-rho point of angle theta-phi. Its actual (j,f) coordinates
are the same two positive quantities. They lie strictly between
xi,U and -w,1-w respectively, by (1) and the bounds above.

The angle theta satisfies

    pi/5<theta<pi/4.                                  (9)

For the lower bound, cos(theta)=5/sqrt(41)<4/5, whereas
cos(pi/5)=(1+sqrt(5))/4>4/5. The upper bound is immediate
from 4/5<1.

Each genuine radial S leaf contains in its open interior the
whole closed radius-rho subarc whose angle is within pi/8 of
its actual radial direction. Indeed

    rho*cos(pi/8)>33/32>d,
    rho*sin(pi/8)<1/2,
    rho<d+1.

The first estimate uses cos(pi/8)>11/12; the second follows
from sin^2(pi/8)<3/20<16/81. Both follow from sqrt(2)>7/5.
Thus the actual radial and tangent side inequalities are strict,
including the endpoints of these chosen subarcs.

We now have four genuinely occupied pieces on the same circle:
the two actual root-interior points and the two entire actual
leaf-interior subarcs. Their complement consists of four open
gaps, or smaller gaps if any other occupied part is also used.

## 5. Exact gap lengths and the original nine-unit contradiction

Use increasing ordinary angles from the M leaf's upper endpoint.
The four free-gap lengths are bounded as follows.

The right and left side gaps, from a leaf subarc to its adjacent
root point, have lengths

    theta-pi/8+phi_B,
    theta-pi/8+phi_A,

respectively. By (4),(9), both are strictly below

    pi/4-pi/8+pi/12=5*pi/24<2*pi/9.                   (10)

The top gap between the two root points has length

    pi-2theta+phi
      <pi-2*pi/5+pi/24=77*pi/120<2*pi/3.             (11)

The bottom gap between the two leaf subarcs has length

    3*pi/4-phi-phi_A-phi_B
      <3*pi/4-2/7<2*pi/3.                            (12)

For the last comparison, pi/12<11/42<2/7, again using pi<22/7.
These are inequalities for the actual unchanged pieces, not
arcs from an aligned surrogate.

Every additional unit beyond A,B,L,M has distance greater than
1/8 by Section 3. The complete accepted physical theorem
FORTY_DEGREE_NINE_EIGHTHS_ARC_OUTSIDE_ONE_EIGHTH.md therefore
gives its open interior one connected radius-9/8 arc of length
strictly greater than 2*pi/9. The theorem includes every actual
orientation and both physical outer-face cases.

That connected arc cannot cross any of the actual occupied root
points or leaf subarcs in Section 4. Thus it lies in one of the
four free gaps. Neither side gap in (10) holds such an arc.
Each top or bottom gap in (11)--(12) holds at most two disjoint
arcs longer than 2*pi/9. Consequently at most four further
actual units exist.

The original nine squares supply five such further units. This
contradiction proves the capacity theorem.

## 6. Exact original one-owner caller

In the full high adjacent-S C4, the complete one-owner feature
reduction supplies precisely these actual charts whenever A's
genuine leaf is strict outer lower and B's is strict lower
adjacent. Its true contact P=(h,-k) is A-side-interior, hence
0<k<v, and both actual S radial identities hold. All hypotheses
of the physical theorem are therefore literal properties of the
original nine-unit packing.

Thus the entire original domain with k>=3/20 is impossible,
whether C or D has one or two physical circle corners and
regardless of any actual outer-edge owner or original side mean.
In every remaining strict/strict one-owner caller,

    0<k<3/20.

No C/D force, degree, mask, circle weight or application is
deleted to obtain this conclusion. It is a complete same-nine
capacity exit at the declared threshold, not a numerical
sample or a claim about the remaining smaller-k domain.
