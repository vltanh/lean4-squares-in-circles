# Every actual occupied cross has total unit capacity at most eight

Date: October 27, 2026.

**Status: accepted complete uniform geometric theorem after full root and separate independent reviews.**
Reviewed mathematical SHA-256: `c3e0979e5baacda8a117572ad9e337b0ec4e21a56bbcf9bb25f7af33481e92a5`. Root review: REVIEW_GENERAL_OCCUPIED_CROSS_NINE_UNIT_ROOT_2026_10_27.md. Separate review: REVIEW_GENERAL_OCCUPIED_CROSS_NINE_UNIT_GLOBAL_2026_10_27.md.
No original graph/load gate, shared ledger, Lean file, workflow, or remote
branch is changed.

Put Q=1105/256. Let actual closed unit squares, with pairwise disjoint
open interiors, lie in one disk of radius R<=sqrt(Q). Suppose five of
those squares are the aligned occupied cross: one unit and the four
units sharing its four full sides.

**Theorem.** The entire packing contains at most eight unit squares.

There is no force, degree, load, selected normal, contact mean, or
physical boundary-arm premise. All additional squares retain every
position and orientation. In particular this theorem applies to an
occupied four-ring equality even when none of its arms has a positive
circle load and when its ring vertices have arbitrary higher degrees.

The proof uses the complete force-free opposite-quadrant lemma in
`CHORDED_HEXAGON_OCCUPIED_CROSS_OPPOSITE_QUADRANT_EMPTY.md` (frozen
SHA256 c824dd96ba8b9505de653248b9bd99bbf429eb706f84f5288d58657db6f9abf7).
Its full proof, including every SAT alternative, remains part of the
present dependency. The new work below proves a uniform center rectangle
for every corner unit and includes all possible units beyond an arm.

## 1. The actual cross, center bounds, and a point-square identity

Use the actual cross frame, centered at its central unit. Its union is

    B=[-3/2,3/2] times [-1/2,1/2],
    V=[-1/2,1/2] times [-3/2,3/2].                   (1)

Write o=(u,v) for the actual containing-circle center. The greatest
squared distance from o to the eight outer cross vertices is exactly

    u^2+v^2+3 max(|u|,|v|)+min(|u|,|v|)+5/2.

Consequently

    |u|,|v| < 31/60.                                (2)

Indeed (31/60)^2+3(31/60)+5/2-Q=31/57600>0. Every
contained unit center c also satisfies

    |c-o| < M:=91/60,                               (3)

since its farthest squared corner radius, for own center coordinates
p,q and r=sqrt(p^2+q^2), is

    r^2+|p|+|q|+1/2 >= r^2+r+1/2,

and M^2+M+1/2-Q=31/57600>0. This latter inequality also holds for
the farthest vertex of a square measured from any fixed point z, with
r the distance from z to its center; z need not be its circle center.

The following necessary containment inequality will remove the actual
circle center without fixing it. Let z be any actual cross vertex. For
an extra square centered at c, choose actual own orthonormal axes

    n=(a,b), m=(b,-a), a,b>=0, a^2+b^2=1.

Its two actual corners c+n/2+m/2 and c+n/2-m/2, together with z,
are all in the original containing disk. For any -1/2<=tau<=1/2,
assign them respectively the nonnegative weights

    1/4+tau/2, 1/4-tau/2, 1/2.

The weighted variance is no greater than R^2. Expanding that variance
therefore proves the exact necessary inequality

    1/8-tau^2/2 + |c-z+n/2+tau*m|^2/4 <= Q.         (4)

This is a geometric variance identity for three actual points, not an
alteration of physical forces or loads.

Put X=(c-z)_x, Y=(c-z)_y. The larger of the two left sides of (4)
for tau and -tau, with 0<=tau<=1/2, is

    F_tau(X,Y)=1/8-tau^2/2
       + [(aX+bY+1/2)^2+(|bX-aY|+tau)^2]/4.         (5)

For X,Y>=1 it is strictly increasing in each coordinate separately.
Away from bX-aY=0 its derivatives are

    (X+a/2+tau*b*sign(bX-aY))/2,
    (Y+b/2-tau*a*sign(bX-aY))/2,

both positive. Continuity gives the same monotonic conclusion through
the absolute-value junction. The single signed expression (4) has the
same monotonicity for X,Y>=1, directly from its expansion.

On a line aX+bY=C, (5) is increasing in |W|, where
W=bX-aY. In particular F_(1/2) is one quarter of the squared distance
from z to the farthest actual square corner, since aX+bY is positive.

## 2. Corner centers, the complete SAT cover, and the target rectangle

Call a center a corner center if |x|>1/2 and |y|>1/2. Independent
reflections of the whole actual geometry reduce any such center to

    x>1/2, y>1/2.                                   (6)

Neither coordinate can be at least 2. For example, if x>=2 and
 y>=1/2, take the actual cross vertex z=(-3/2,-1/2). The center
is at distance r with r^2>=53/4 from z. One actual square corner
is therefore at squared distance at least

    r^2+r+1/2 > 53/4+18/5+1/2=347/20 > 4Q.          (7)

Here r>18/5, as (18/5)^2<53/4. This contradicts the diameter
2sqrt(Q) of the original containing disk. The same proof interchanges
x,y. It includes the weak endpoint y=1/2 needed later as an algebraic
lower-bound evaluation. Thus every corner center satisfies x,y<2.

We shall prove the full orientation-uniform bounds

    59/60 < x,y < 169/100.                           (8)

The squared diameter of this open rectangle is

    2(169/100-59/60)^2=5618/5625<1.                  (9)

Two distinct interior-disjoint units have center distance at least one,
by their open radius-1/2 incircles. Thus (8) gives capacity at most one
in each of the four corner regions.

For completeness, separation of an actual extra from either solid
rectangle [-ell,ell] times [-h,h], ell,h>=1/2, has the following
complete form under (6): a positive cross axis separates, or an actual
own axis n=(a,b) with a,b>0 separates. Indeed a rectangle's side axis
or an extra square's side axis is a separating axis. Negative cross
axes and a normal with two nonpositive coordinates cannot separate.
If an own normal (-a,b), a,b>=0, separates, it gives

    by-ax >= ell*a+h*b+1/2.

For b>0 this already implies the ordinary vertical separation
 y>=h+(a+b)/2, because

    1+2a(x+ell)-b(a+b)=a^2+a[2(x+ell)-b]>=0.

The reflected calculation treats (a,-b) and gives ordinary horizontal
separation. Axial endpoints are already cross-axis alternatives.
Every remaining own normal consequently has a,b>0. This covers every
physical orientation and every weak contact of the two rectangles.

## 3. The upper coordinate bound, with ordinary vertical separation

Suppose x>=K:=169/100 and separate the extra from B. Horizontal
cross-axis separation would give x>=3/2+(a+b)/2>=2, excluded by (7).

First consider ordinary vertical separation. Choose the actual own
axes as in Section 1 and put h=(a+b)/2. Then y>=1/2+h. With the
actual cross vertex z=(-3/2,-1/2), the variables of (4) satisfy

    X>=X0:=319/100, Y>=1+h.

By the signed monotonicity after (5), its left side is at least

    P_tau(a,b)=1/8-tau^2/2
       + [(X0+a/2+tau*b)^2+(1+(1/2-tau)*a+b)^2]/4.  (10)

Set z=b/(1+a), so 0<=z<=1 and

    a=(1-z^2)/(1+z^2), b=2z/(1+z^2).

For each of the following three signed choices of tau, direct expansion
is

    P_tau-Q = N_tau(z)/[160000(1+z^2)^2].            (11)

The coefficients of N_tau are in ascending powers of z:

| tau | Coefficients | Entire interval used |
| --- | --- | --- |
| -2/5 | 5619, 67840, -371962, -156160, -393581 | [0,43/200] |
| 0 | -35981, 240000, -327162, 80000, -371181 | [43/200,7/25] |
| 1/2 | -105981, 455200, -307162, 375200, -361181 | [7/25,1] |

Appendix A supplies every exact Bernstein coefficient on these closed
intervals; all are strictly positive. Hence (10) exceeds Q throughout
the full closed orientation interval, contradicting (4). Ordinary
vertical separation is impossible.

## 4. The upper coordinate bound, with a genuine own-axis separator

The remaining complete SAT alternative from B has a,b>0 and

    ax+by >= 1/2+3a/2+b/2.                          (12)

For the same actual cross vertex z=(-3/2,-1/2), this says

    aX+bY >= C:=3a+b+1/2,
    X>=X0=319/100, Y>=1.                            (13)

At the lower corner (X0,1) of this allowed rectangle the normal
projection is smaller than C, since

    C-aX0-b=1/2-(19/100)a>0.

The coordinatewise monotonicity in (5) therefore lets us first reduce
to the line aX+bY=C. More explicitly, the segment from (X0,1) to
an actual point of (13) crosses this line at a coordinatewise smaller
point. This is only an algebraic lower-bound evaluation of (5).
On that line put

    U0=C+1/2=3a+b+1,
    W=bX-aY=(X-aC)/b.

The feasible interval for W has endpoints

    W_min=(X0-aC)/b,
    W_max=(bC-1)/a.                                 (14)

Every expression (5) is minimized there by the value of W having
smallest absolute value. We cover the entire a interval next.

### 4.1. The complete range 0<a<=7/8

Here W_min>0. To verify it, f(a)=a(3a+b+1/2) is strictly increasing
on [0,7/8]. Its derivative is

    f'=6a+1/2+(1-2a^2)/b.

It is positive for a<=1/2. For 1/2<=a<=7/8, a possibly negative
last term has absolute value at most 17/(4sqrt(15))<17/12, whereas
6a+1/2>=7/2. At the upper endpoint,

    f(7/8)=(175+7sqrt(15))/64 < 203/64 < 319/100.

Thus all W in (14) are positive, and every (5) is at least its value
at X=X0. The corresponding actual-coordinate lower-bound evaluation
has

    x=K, y=1/2+[1/2-(19/100)a]/b.

Put k=19/100 and retain X0=319/100. For tau>=0 define

    H_tau(a,b)=1/8-tau^2/2
       + [(X0+a/2+tau*b)^2
          +(1+(1/2-k*a)/b+b/2-tau*a)^2]/4.           (15)

The actual value of (5) is at least H_tau. Now put

    z=a/(1+b), a=2z/(1+z^2), b=(1-z^2)/(1+z^2).

Our interval has 0<z<3/5: at a=7/8 this follows from sqrt(15)>11/3,
which gives z=7/(8+sqrt(15))<3/5. Expansion gives

    H_tau-Q = J_tau(z)/[160000(1-z^2)^2(1+z^2)^2].   (16)

The complete coefficient lists are:

| tau | Coefficients in ascending powers of z | Entire intervals used |
| --- | --- | --- |
| 1/2 | 14019, 74400, -179024, -276000, 478714, -135200, 270576, 215200, -401181 | [0,1/2] |
| 2/5 | -7901, 98400, -134064, -284000, 471514, -159200, 225616, 223200, -372061 | [1/2,11/20], [11/20,3/5] |

Every exact Bernstein coefficient on these full intervals is positive
in Appendix A. Hence some necessary (5) exceeds Q at every orientation
in this range. This is a contradiction.

### 4.2. The complete range 7/8<=a<=99/100

The function U0=3a+sqrt(1-a^2)+1 is concave. At a=7/8 its value is
(29+sqrt(15))/8>41/10, using sqrt(15)>19/5. At a=99/100 it is
(397+sqrt(199))/100>41/10, using sqrt(199)>13. Concavity gives
U0>41/10 throughout. Therefore the necessary inequality (5) with
 tau=0 already has left side at least

    1/8+U0^2/4 > 1731/400 = Q+71/6400,

a contradiction, regardless of W or of which endpoint in (14) minimizes it.

### 4.3. The complete range 99/100<=a<1

Here b<1/7. Thus bC<(1/7)(3+1/7+1/2)=51/98<1, so W_max<0.
The minimum of (5) over (14) occurs at W_max, equivalently at Y=1.
The corresponding center evaluation is

    y=1/2, x=3/2+1/(2a)>=2.

For tau=1/2, (5) is a quarter of the squared farthest-vertex distance
from the actual cross vertex z. At this evaluation the same universal
point-to-square calculation (7) gives F_(1/2)>Q. No physical square
is moved or assumed to exist at the evaluation point. It is simply a
lower bound for the original necessary inequality. This is the last
contradiction in the complete SAT cover.

Sections 3--4 prove x<169/100. Exchanging the two actual cross
coordinates gives the identical bound for y.

## 5. The lower coordinate bound

Suppose 1/2<x<=L:=59/60 and separate the extra from V. Horizontal
cross-axis separation would give x>=1, a contradiction. Vertical
cross-axis separation would give y>=2, excluded by (7). The remaining
complete own-axis condition has a,b>0 and

    ax+by >= 1/2+a/2+3b/2.                          (17)

Use the other actual cross vertex z=(-1/2,-3/2). Then

    1<X=x+1/2<=XL:=89/60, Y=y+3/2>1,
    aX+bY>=C:=a+3b+1/2.                             (18)

For any fixed X in this interval, the point on aX+bY=C still has
Y>1, because

    C-aX-b >= (1-XL)a+2b+1/2 > 1/60.

The monotonicity of F_(1/2) therefore allows us to decrease Y to
that line. On it,

    U0=C+1/2=a+3b+1, W=(X-aC)/b.                    (19)

We minimize U0^2+(|W|+1/2)^2 over the full closed relaxation
1<=X<=XL, and prove it greater than 4Q in every remaining orientation.

For 0<a<=1/4, aC<=15/16<1. Hence W is positive and its smallest
value occurs at X=1. There Y=3+1/(2b)>=7/2. The point-to-square
calculation (7), with squared center displacement at least 53/4,
again makes the squared farthest-corner distance greater than 4Q.

For 1/4<=a<=5/12, U0 is concave. At the endpoints its values are

    (5+3sqrt(15))/4 > 33/8,
    (17+3sqrt(119))/12 > 33/8.

The strict inequalities follow respectively from sqrt(15)>23/6 and
sqrt(119)>65/6. Thus

    U0^2+(|W|+1/2)^2 >= U0^2+1/4
       > (33/8)^2+1/4 = 4Q.                        (20)

For 5/12<=a<1, we have aC>=3/2>XL. Here is a whole-interval check.
The function f(a)=a(a+3b+1/2) has

    f''=2-3a(3-2a^2)/b^3<0.

Indeed g(a)=a(3-2a^2)/b^3 has derivative 3/b^5>0, and g(5/12)>1.
At a=5/12, f=(55+15sqrt(119))/144>3/2, using sqrt(119)>54/5;
at a=1 its continuous value is exactly 3/2. Concavity proves the claim.
Thus W is negative throughout (18), and its smallest absolute value
occurs at X=XL. The necessary squared farthest-corner distance is at least

    G(a,b)=(a+3b+1)^2
       + [1/2+(a(a+3b+1/2)-89/60)/b]^2.             (21)

Set z=a/(1+b), as in Section 4.1. This range has 1/5<z<1 because
z>=a/2>=5/24>1/5. Direct expansion gives

    G-4Q = T(z)/[14400(1-z^2)^2(1+z^2)^2],          (22)

where the coefficients of T in ascending powers are

    -4301, 32160, 42736, -226080, 194394,
    -87840, 12976, 170400, -134381.

Every exact Bernstein coefficient of T on the two entire intervals
[1/5,4/5] and [4/5,1] is positive in Appendix A. Hence (21) exceeds
4Q throughout the last range, contradicting the diameter of the
original containing disk. This excludes every alternative in (17).

Therefore x>59/60. Exchanging coordinates proves the same lower
bound for y and completes the full rectangle (8).

## 6. All extra centers, including the four axial regions

The open radius-1/2 incircle of an extra is disjoint from both solid
rectangles (1). If |x|<=1/2, its distance from V can be at least 1/2
only if |y|>=2. Similarly |y|<=1/2 forces |x|>=2. Thus every extra
center is either in a strict corner region or in one of four axial
regions, such as

    north: |x|<=1/2, y>=2.                          (23)

If no axial region is occupied, the complete opposite-quadrant lemma
quoted at the start gives at least one empty corner. Each of the other
three corners has capacity at most one by (8)--(9). Thus there are at
most three extra units.

Suppose instead that (23) contains an actual center. Then (3) forces

    v>2-M=29/60.                                    (24)

An occupied south axial region would force v<-29/60, impossible.
An occupied east or west axial region would force |u|>29/60, also
impossible: the exact cross-radius expression in Section 1 would give

    R^2 > 2(29/60)^2+4(29/60)+5/2 > Q.               (25)

So north is the only possible occupied axial region. All its centers
satisfy

    2<=y<v+M<61/30,
    (x-u)^2 < M^2-(2-v)^2
              < M^2-(89/60)^2=1/10<1/9.            (26)

They therefore lie in a rectangle of width 2/3 and height 1/30,
whose squared diameter is 401/900<1. The whole north axial region
has capacity at most one.

Both southern corner regions are empty in this case. For any putative
center there, (2), (8), and (24) give

    |x-u| > 59/60-31/60=7/15,
    |y-v| > 59/60+29/60=22/15.

Consequently its squared distance from o exceeds

    (7/15)^2+(22/15)^2=533/225
       = M^2+247/3600 > M^2,                        (27)

contrary to (3). Each of the two northern corner regions has capacity
at most one by (8)--(9). Including the unique possible axial extra,
there are again at most three extra units. Rotations give the same
argument for any initially occupied axial direction.

This exhausts every actual extra center. The five cross units and at
most three extras give at most eight units in the original disk.

## 7. Scope of the resulting geometric completion theorem

The proof retains all nine actual physical units in every caller. It
uses no equilibrium equation and consequently remains valid with every
original chord force, root attachment, circle mask, force magnitude,
and common support mean retained.

In particular, the degree-independent occupied-four-ring equality in
`FOUR_CYCLE_THREE_BOUNDARY_HOLE_EMPTY.md`, Sections 1--2, now implies:

**No actual physical four-ring in a nine-unit packing at R^2<=Q can
enclose another whole actual unit.**

This implication uses that equality only to identify the five actual
cross units; it makes no assertion about a loaded degree-two neighbor.
It strengthens the older adjacent-boundary-arm cross theorem without
changing or deleting that historical proof or its accepted callers.

Likewise, an actual embedded K_(2,3) subgraph is impossible in such a
nine-unit packing, with arbitrary additional edges and forces and no
boundary-load premise. Restrict the existing physical embedding to the
five actual K_(2,3) vertices and its six actual edges. Its exterior face
is a four-cycle and its fifth vertex lies on the bounded side of that
actual four-ring. The same occupied-four-ring equality gives the cross,
and the present theorem contradicts the unchanged nine-unit completion.
The physical embedding and enclosed-unit routing are exactly the
restricted-embedding argument in
`GLOBAL_CLOSURE_SPANNING_K23_BOUNDARY_AND_TERMINAL_EXCLUSIONS.md`,
Section 1; no physical embedding is replaced by an abstract drawing.

Every bounded unit region surrounded by a four-cycle is therefore empty
throughout every original exterior-hexagon graph/load family. Triangular
regions retain their separate area obstruction. A five-sided bounded
region or a remaining exterior completion is not closed merely by this
statement. No original parent graph/load ID is ticked by this source.

## Appendix A. Complete exact univariate positivity certificates

For a polynomial N(z)=sum c_k z^k of degree n and a closed interval
[l,l+w], substitute z=l+w t. Its Bernstein coefficient of index j is

    beta_j = sum_(i=0)^j A_i binom(j,i)/binom(n,i),
    A_i = sum_(k=i)^n c_k binom(k,i) l^(k-i) w^i.     (28)

Then N(l+w t)=sum_(j=0)^n beta_j binom(n,j)t^j(1-t)^(n-j).
The basis is nonnegative and sums to one on 0<=t<=1. The following
lists give every beta_j in ascending index. Each entry is strictly
positive. They are exact rational identities on full intervals, not
sampled poses or assumptions about a finite set of square orientations.

### A.1. Ordinary vertical separation, tau=-2/5

Interval [0,43/200].

| j | beta_j |
| --- | --- |
| 0 | 5619 |
| 1 | 46327/5 |
| 2 | 1205537131/120000 |
| 3 | 1514646823/200000 |
| 4 | 988312739619/1600000000 |

### A.2. Ordinary vertical separation, tau=0

Interval [43/200,7/25].

| j | beta_j |
| --- | --- |
| 0 | 796616506019/1600000000 |
| 1 | 410467500631/200000000 |
| 2 | 20876601461/6250000 |
| 3 | 6789402903/1562500 |
| 4 | 1970380044/390625 |

### A.3. Ordinary vertical separation, tau=1/2

Interval [7/25,1].

| j | beta_j |
| --- | --- |
| 0 | 1331980044/390625 |
| 1 | 1008746592/15625 |
| 2 | 69826308/625 |
| 3 | 3554016/25 |
| 4 | 56076 |

### A.4. Own-axis upper bound, tau=1/2

Interval [0,1/2].

| j | beta_j |
| --- | --- |
| 0 | 14019 |
| 1 | 18669 |
| 2 | 152044/7 |
| 3 | 315807/14 |
| 4 | 11755277/560 |
| 5 | 1924795/112 |
| 6 | 656925/56 |
| 7 | 194625/32 |
| 8 | 511875/256 |

### A.5. Own-axis upper bound, tau=2/5, first interval

Interval [1/2,11/20].

| j | beta_j |
| --- | --- |
| 0 | 151875/256 |
| 1 | 242325/512 |
| 2 | 2624389/7168 |
| 3 | 97930619/358400 |
| 4 | 17574840457/89600000 |
| 5 | 24435394591/179200000 |
| 6 | 170973090749/1792000000 |
| 7 | 191590420929/2560000000 |
| 8 | 1950420590659/25600000000 |

### A.6. Own-axis upper bound, tau=2/5, second interval

Interval [11/20,3/5].

| j | beta_j |
| --- | --- |
| 0 | 1950420590659/25600000000 |
| 1 | 496234243007/6400000000 |
| 2 | 1128985484577/11200000000 |
| 3 | 413063427421/2800000000 |
| 4 | 76731455579/350000000 |
| 5 | 27777488817/87500000 |
| 6 | 693281569/1562500 |
| 7 | 234154912/390625 |
| 8 | 307069504/390625 |

### A.7. Lower bound, first interval

Interval [1/5,4/5].

| j | beta_j |
| --- | --- |
| 0 | 905230144/390625 |
| 1 | 1717637776/390625 |
| 2 | 15879769228/2734375 |
| 3 | 16887853762/2734375 |
| 4 | 2110605514/390625 |
| 5 | 10050128317/2734375 |
| 6 | 4512217993/2734375 |
| 7 | 253854871/390625 |
| 8 | 178559059/390625 |

### A.8. Lower bound, second interval

Interval [4/5,1].

| j | beta_j |
| --- | --- |
| 0 | 178559059/390625 |
| 1 | 30692091/78125 |
| 2 | 45755377/109375 |
| 3 | 459801/875 |
| 4 | 15033582/21875 |
| 5 | 148482/175 |
| 6 | 159868/175 |
| 7 | 3648/5 |
| 8 | 64 |

All intervals include their common endpoints. The positive denominators
in (11), (16), and (22) are retained throughout their actual domains;
z=1 is used only as a harmless closed polynomial endpoint when a
denominator tends to zero. Every original orientation is covered before
the corresponding contradiction is drawn.
