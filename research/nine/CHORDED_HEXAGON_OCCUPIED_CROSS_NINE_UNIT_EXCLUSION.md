# An occupied four-ring with two adjacent boundary arms cannot be completed to nine units

Date: October 27, 2026.

**Status: complete proposed whole geometric theorem and full one-diameter
central-region exclusion, pending root and separate independent review.**
No original graph/load gate or shared ledger is changed.

Put Q=1105/256. Consider actual interior-disjoint closed unit squares
in one disk of radius

    79/40 <= R <= sqrt(Q).

**Geometric theorem.** Suppose five of the squares form the aligned
occupied cross: one central unit and its four full-side neighbors.
If two adjacent arms physically touch the containing circle, there
are at most eight squares in the entire packing.

This theorem has no force, degree, load, selected-normal or contact-mean
premise. A physical circle contact is sufficient, including one having
zero multiplier in a caller. The other three or four squares retain
all positions and orientations.

The final section applies it to every original positive exterior
hexagon with its single diameter chord 03. It proves that all three
completion units are exterior in every original load orbit of that
whole graph. Its exterior capacity remains a separate obligation.

## 1. Exact cross and circle chart

Translate and rotate the actual cross to the five units with centers

    (0,0), (1,0), (0,1), (-1,0), (0,-1).

Take the two adjacent circle-touching arms to be north and west.
Write the actual circle center in this chart as (s,v). The squared
farthest-vertex distances of north and south are respectively

    (|s|+1/2)^2+(|v-1|+1/2)^2,
    (|s|+1/2)^2+(|v+1|+1/2)^2.

The first is R squared and the second is at most R squared, so v<=0.
The corresponding west/east comparison gives s>=0. Equality of the
north and west farthest distances then gives s+v=0. Consequently

    O=(t,-t), t>=0,
    R^2=(t+1/2)^2+(t+3/2)^2=2t^2+4t+5/2.

The complete radius window gives the useful strict bounds

    3/10 < t < 23/60.                                (1)

Indeed the last polynomial at 3/10 is 97/25<(79/40)^2; at 23/60
it is 7789/1800>Q. It is strictly increasing for t>=0.

Every contained unit has center distance strictly less than

    M=91/60                                          (2)

from the center of its containing disk of radius at most sqrt(Q).
To check this directly, if its center vector has own coordinates
(u,v), its farthest squared corner radius is

    u^2+v^2+|u|+|v|+1/2
      >= r^2+r+1/2, r=sqrt(u^2+v^2).

At r=M the latter exceeds Q by 31/57600. Hence (2) is strict.

The solid cross contains both rectangles

    [-3/2,3/2] x [-1/2,1/2],
    [-1/2,1/2] x [-3/2,3/2].                         (3)

The radius-one-half open incircle of every additional unit is disjoint
from the open interiors of both rectangles. Its center therefore has
distance at least one half from each closed rectangle.

If its center has |x|<=1/2, this distance condition for the vertical
rectangle forces |y|>=2. Its distance from O is then at least
2-t>97/60>M, impossible. The horizontal rectangle gives the same
conclusion if |y|<=1/2. Every additional center thus lies in one of
the four strict corner quadrants

    |x|>1/2, |y|>1/2.                                (4)

## 2. The northwest corner is empty, and each mixed corner holds at most one

For a northwest center (-x,y), x,y>1/2, either x>=3/2 or y>=3/2
would give distance from O greater than 3/2+t>9/5>M. Otherwise
the two incircle conditions from (3) give x>=1 and y>=1. Its
squared center distance is then greater than

    2*(13/10)^2=169/50>M^2.

Thus the northwest corner has capacity zero.

Consider a northeast center (x,y), x,y>1/2. We have y<3/2 by the
same center-radius bound, and hence x>=1 from the vertical rectangle.
Suppose x>=3/2. Put X=x-3/2>=0 and Y=y-1/2>0. The distance
from the horizontal rectangle gives X^2+Y^2>=1/4. With

    p0=3/2-t, q0=1/2+t, p0>q0>0,

its actual squared center radius obeys

    (p0+X)^2+(q0+Y)^2
      >= p0^2+q0^2+1/4+2*q0*(X+Y)
      >= p0^2+q0^2+1/4+q0
       = 2t^2-t+13/4
       = 2(t-1/4)^2+25/8 > M^2.

This is impossible, so x<3/2. The horizontal rectangle now also
gives y>=1. Using (1)--(2),

    y < M-3/10=73/60<5/4,
    x < 23/60+sqrt(M^2-(13/10)^2)
      = (23+sqrt(2197))/60 < 7/6 < 5/4.

Every northeast center is therefore in [1,5/4)^2. Its diameter is
at most sqrt(1/8)<1. Distinct interior-disjoint units have centers
at least one apart, by their open incircles. This corner has capacity
at most one. Reflection in y=-x fixes both O and the actual cross
and gives the identical southwest capacity.

It remains to prove capacity at most one in the southeast corner.
We prove the following uniform rectangle for every such actual center:

    59/60 < x < 27/16,
    59/60 < -y < 27/16.                              (5)

Its squared diameter is

    2*(27/16-59/60)^2=28561/28800<1,

which will finish the theorem.

## 3. A fixed larger circle and the complete separating-axis cover

Reflect the southeast quadrant across the x axis and write its center
as (x,y), now with x,y>1/2. The circle center becomes (t,t).
Move that center to (T,T), where T=23/60, and allow squared radius Q.
Every southeast unit remains inside this larger disk.

Here is a direct verification, without assuming that the original
cross remains inside the moved disk. Choose its own unit axes as
(a,b) and (b,-a), with a,b>=0 and a^2+b^2=1. For p=x-t>0,
q=y-t>0 the farthest squared corner radius is

    F=p^2+q^2+1/2+a*p+b*q+|b*p-a*q|.                 (6)

As t increases while remaining at most T<1/2, p,q stay positive.
On either side of the absolute-value corner, the derivative is
-2(p+q)-2a or -2(p+q)-2b, strictly negative. Continuity includes
the corner. Thus moving the center as stated decreases the farthest
corner radius. In the rest of this section and Sections 4--5 put

    p=x-T, q=y-T, A=67/60, B=7/60.

The unit has center norm less than M relative to (T,T), by (2).
In particular x,y<T+M=19/10<2.

We use separation between this actual unit and each rectangle in
(3). The usual rectangle separating-axis criterion follows by taking
a common supporting line of two disjoint convex rectangles: a side
axis of one of the two rectangles suffices, including weak touching.
The axes from (3) are the horizontal and vertical axes; the other
possible axes are the actual unit's own axes.

Only a first-quadrant own normal need be considered if neither
rectangle axis separates. To verify this explicitly, let the fixed
rectangle have halfwidths l,m>=1/2. If an own normal (-a,b),
a,b>=0, separates a unit centered at x,y>1/2, then

    b*y-a*x >= l*a+m*b+1/2.

Here b>0. The unit's vertical halfwidth is (a+b)/2, and

    1+2*a*(x+l)-b*(a+b)
       =a^2+a*(2*(x+l)-b)>=0.

Thus y>=m+(a+b)/2: the vertical rectangle axis already separates.
The reflected calculation for (a,-b) gives horizontal separation.
A normal with both components nonpositive cannot separate in that
orientation. Axial endpoints are already rectangle-axis alternatives.
Hence after excluding those axes the remaining normal is (a,b) with
a,b>0. Its actual own-coordinate halfwidth is one half.

This covers every physical square orientation and all support means;
no common frame has been imposed on an additional unit.

## 4. The upper coordinate bound x<27/16

Assume x>=27/16, so p>=p0=313/240. Separate the unit from the
horizontal rectangle of (3). Horizontal-axis separation would give
x>=3/2+1/2=2, already impossible.

### 4.1. Vertical rectangle-axis separation

Choose the unit axes in this subsection as (b,a), (a,-b), where
a,b>=0 and a^2+b^2=1. Its vertical halfwidth is (a+b)/2.
Vertical separation gives

    q>=B+(a+b)/2>1/2.

For p,q>1/2 the farthest-corner expression is increasing in each
coordinate separately: its piecewise linear support term has each
coordinate derivative at least -1, while the quadratic contributes
2p>1 and 2q>1. It is therefore at least the value at
p=p0, q=B+(a+b)/2. That value is the larger of

    F1(a)=(p0+(a+b)/2)^2+(B+a)^2,
    F2(a)=(p0+(b-a)/2)^2+(B+a+b)^2.                  (7)

For 1/2<=a<=1, F1 is strictly concave. Indeed, with
b=sqrt(1-a^2),

    F1''=2-[p0+a*(3-2a^2)/2]/b^3<0,

because 2b^3<=3sqrt(3)/4<13/10<p0. Its endpoint limits both
exceed Q. The exact lower comparisons, using sqrt(3)>173/100, are

    F1(1/2)>(149/75)^2+(37/60)^2>Q,
    F1(1)=(433/240)^2+(67/60)^2>Q.

For 0<=a<=1/2, F2 is strictly concave, since

    F2''=-[p0+2B+3a*(3-2a^2)/2]/b^3<0.

Its value at zero is the same F1(1), while

    F2(1/2)>(223/150)^2+(889/600)^2>Q.

A concave function lies above the minimum of its two endpoint
values. Thus (7) exceeds Q throughout the full orientation interval,
contradicting containment. Vertical separation is impossible too.

### 4.2. A genuine own-axis separator

By Section 3 the remaining own normal is n=(a,b), a,b>0.
Let its actual center coordinates in the orthonormal axes n,(b,-a)
be c and w. The support inequality against the horizontal rectangle
gives

    c>=L=1/2+h, h=A*a+B*b.

Containment gives (c+1/2)^2+1/4<=Q. Hence h<61/60.
The concave function h(a) on 6/7<=a<=1 has both endpoint values
greater than 61/60. At a=6/7 this follows from sqrt(13)>25/7;
at a=1 it is immediate. Therefore

    a<6/7, c<M, a*c<13/10<p0.

Since w=(p-a*c)/b, it is strictly positive. Lowering p to p0
decreases (c+1/2)^2+(w+1/2)^2 and preserves that sign. At fixed
p0 this quadratic in c has its unconstrained minimum at

    c*=a*p0+a*b/2-b^2/2.

It lies strictly below L, because

    c*-L=(3/16)*a+a*(a+b)/2-B*b-1
          <=3/16+sqrt(2)/2-1<0.

Consequently the actual farthest squared radius is at least

    G_+(a)=(1+h)^2+[1/2+(p0-a*(1/2+h))/b]^2.         (8)

Here is a complete exact positivity check for (8), given explicitly
so no numerical range search is an input. Put z=a/(1+b). Then
0<z<4/7, a=2z/(1+z^2), b=(1-z^2)/(1+z^2). The bound z<4/7
follows again from a<6/7 and sqrt(13)>25/7. Direct expansion gives

    G_+(a)-Q = N_+(z)/[57600*(1-z^2)^2*(1+z^2)^2],

where the coefficients of N_+ in increasing powers of z are

    10688, 30960, -41340, -242640, 287144,
    -117360, 172740, 156240, -166432.                (9)

On z=(4/7)u, 0<=u<=1, this polynomial has the exact Bernstein
expansion sum_(j=0)^8 b_j*C(8,j)*u^j*(1-u)^(8-j), with

| j | b_j |
| --- | --- |
| 0 | 10688 |
| 1 | 90296/7 |
| 2 | 5017664/343 |
| 3 | 36177128/2401 |
| 4 | 1163434112/84035 |
| 5 | 1282219656/117649 |
| 6 | 5406603008/823543 |
| 7 | 266630760/117649 |
| 8 | 249163200/823543 |

Every coefficient is strictly positive and the basis functions sum
to one. Thus N_+>0 on the entire closed interval, proving G_+>Q.
This contradicts containment in the last separator alternative.
The strict bound x<27/16 follows.

## 5. The lower coordinate bound x>59/60

Assume x<=59/60, so p<=3/5 in the fixed circle of Section 3.
Separate the unit from the vertical rectangle of (3).
Horizontal-axis separation would give x>=1; vertical-axis separation
would give y>=2. Both are impossible here. Section 3 therefore gives
an actual own normal n=(a,b) with a,b>0 and

    c>=L=1/2+h, h=B*a+A*b.

Again containment gives h<61/60. For 0<=a<=1/2, h(a) is
concave and both endpoint values exceed 61/60: the endpoint at
1/2 reduces to 67sqrt(3)>115. Hence a>1/2.

On 1/2<=a<=1 the function a*(1/2+h) is concave. Its second
derivative is

    7/30-(67/60)*a*(3-2a^2)/b^3<0.

The value at one is 37/60, and the value at one half is larger.
Therefore a*L>=37/60>3/5 throughout the remaining interval.

The other center coordinate has absolute value

    |w|=|p-a*c|/b >= (a*c-3/5)/b>0.

Both terms of the resulting farthest-radius lower bound increase
with c>=L. Consequently it is at least

    G_-(a)=(1+h)^2+[1/2+(a*(1/2+h)-3/5)/b]^2.         (10)

For completeness, the exact whole-interval positivity of (10) is
as follows. Put z=a/(1+b), so 0<z<1. Direct expansion gives

    G_-(a)-Q = N_-(z)/[57600*(1-z^2)^2*(1+z^2)^2],

where the coefficients in increasing powers of z are

    10015, 19648, 69184, -375872, 390978,
    -242368, 153664, 153152, -178145.                (11)

The following are its exact degree-eight Bernstein coefficients on
the two complete intervals [0,2/3] and [2/3,1]. The affine variable
u always increases from zero to one across the displayed interval.

| j | [0,2/3] coefficient | [2/3,1] coefficient |
| --- | --- | --- |
| 0 | 10015 | 21711391/6561 |
| 1 | 34957/3 | 4216933/2187 |
| 2 | 906433/63 | 4469965/5103 |
| 3 | 3067987/189 | 535237/1701 |
| 4 | 15405023/945 | 339578/945 |
| 5 | 24226235/1701 | 187682/189 |
| 6 | 51785473/5103 | 120700/63 |
| 7 | 13277525/2187 | 6848/3 |
| 8 | 21711391/6561 | 256 |

All coefficients are strictly positive. Hence N_->0 throughout
[0,1], with its common endpoint included, and G_->Q. This is the
contradiction in the complete last separator case.
Thus x>59/60.

The reflection exchanging x and y fixes the moved circle and swaps
the two actual cross rectangles. It gives the same upper and lower
bounds for y. This proves the entire southeast rectangle (5).

The coefficient identities (9)--(11) are elementary polynomial
identities: for a polynomial sum c_i*z^i on [l,l+w], substitute
z=l+w*u, then the degree-eight Bernstein coefficient is

    b_j=sum_(i=0)^j a_i*C(j,i)/C(8,i),
    a_i=sum_(k=i)^8 c_k*C(k,i)*l^(k-i)*w^i.

This formula verifies every entry exactly. The tables are complete
univariate positivity proofs over the full stated ranges, not sampled
poses or a finite substitute for the original configuration domain.

## 6. Whole packing count

Every additional actual unit center belongs to one of the four strict
quadrants by (4). The northwest quadrant contains none; northeast and
southwest contain at most one each; southeast contains at most one by
the strict rectangle (5) and center separation. Therefore at most
three units can be added to the actual five-unit cross. The entire
packing has at most eight units, proving the geometric theorem.

## 7. Complete original single-diameter exterior-hexagon application

Take the unchanged selected positive exterior hexagon 0,1,2,3,4,5
with precisely the one chord 03. Its two bounded face cycles are
0123 and 0345. Every additional whole central unit lies on one of
these bounded physical face sides. The physical center/contact
routing and its weak-junction limits are the same complete routing
used in CHORDED_HEXAGON_CENTRAL_CAPACITY_ONE.md. Additional physical
zero-weight contacts may subdivide a face; they cannot move an open
unit through an occupied body to the other side.

Suppose a completion unit lies in face 0123. The degree-independent
occupied-four-ring equality of
FOUR_CYCLE_THREE_BOUNDARY_HOLE_EMPTY.md, Sections 1--2, forces its
four ring units and the enclosed unit to be the exact aligned cross.
The actual rim bodies 1 and 2 have true positive degree two. At
each, its two original strict point-only ring normals have strictly
negative projection on that arm's outward radial cross axis. If
its circle load vanished, its two positive pair forces could not
sum to zero. Thus both are positively circle-loaded and physically
touch the circle. They are adjacent arms of the actual cross.

All nine original physical squares remain, so the geometric theorem
contradicts this occupied face. The reflected proof applies to face
0345, using the true degree-two adjacent arms 4 and 5. No force
at either degree-three chord endpoint is removed or replaced.

Hence the complete one-diameter graph has central unit capacity zero,
for every original load set, circle mask, positive force magnitude,
common mean and extra physical contact. This is a whole-region theorem,
not a restriction to favorable positions or a few load assignments.

Together with the separate complete two-chord central-region theorem
and the triangular-face area theorem, every exterior hexagon having
a diameter chord or at least two positive chords has empty bounded
unit regions. The single-short-chord pentagon face remains separate.

No exterior capacity or full D03 graph/load exclusion is inferred here.
Those complete original obligations remain open until their exterior
completions are excluded. No shared ledger, Lean file, CI workflow,
remote branch or extracted physical certificate is changed by this
geometric argument.
