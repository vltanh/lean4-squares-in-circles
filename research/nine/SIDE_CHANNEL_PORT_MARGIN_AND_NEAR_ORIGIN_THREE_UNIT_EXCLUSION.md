# A uniform side-channel port margin and a three-unit obstruction near the origin

Date: October 26, 2026.

**Status: complete geometric reductions, accepted after the independent
full-source review REVIEW_SIDE_CHANNEL_PORT_MARGIN_AND_NEAR_ORIGIN_C6_2026_10_26.md.**
The complete original C6 join is now provided separately by
FOUR_C6_SIDE_OCCUPIED_CAP_TRANSMITTER_PROXIMITY.md and
GENERAL_SIDE_CHANNEL_CAP_CENTRAL_INJECTION_BOUND.md. Section 5 below
preserves the earlier sufficient vertical-separation condition; that
stronger condition is not asserted and is not needed by the new proof,
which establishes the required transmitter proximity directly.

Put Q=1105/256 and M=91/60. Work in 2<=R<=sqrt(Q). Every actual unit
contained in the disk D_R has center norm strictly below M, since

    M^2+M+1/2-Q=31/57600>0.

## 1. Complete actual side-channel domain

Let X-U-Y be an original width-one normal channel. Its actual endpoint
applications and unchanged support equations are

    P_X=(-a,h), P_Y=(b,h), a+b=1, h>0,
    X subset {x<=-a}, Y subset {x>=b},
    U=[-a,b] times [v,v+1], v<=h<=v+1.                 (1)

Assume X,Y are actual physical boundary units, their center heights
are nonnegative, and their horizontal center signs are left and right.
These are exactly the whole-channel consequences already proved for
every positive-reserve channel of an entire simple positive cycle with
at least three loads. Their full scope is in
SIMPLE_CYCLE_CONVEX_FORCE_POLYGON.md, Section 5. The local geometric
argument below imposes no further degree, load, or circle-mask condition.

**Port theorem.** The unchanged actual applications satisfy

    a>7/100, b>7/100.                                    (2)

Consequently every actual vertex of U has norm greater than 7/100,
for every original transverse slider and every endpoint mean.

Every support half-width is at least 1/2. The two boundary center bounds
first give a,b<61/60, and a+b=1 then gives a,b>-1/60.

## 2. A full physical endpoint inequality, including radial masks and means

Consider an actual boundary unit X with right support point p=(-a,h),
where a>0,h>0, and with nonnegative center height. We prove

    R^2 >= (a+1)^2+h^2.                                 (3)

If X owns this side axis, its full form is

    X=[-a-1,-a] times [B-1,B],
    B>=1/2, B-1<=h<=B,
    R^2=(a+1)^2+B^2.

Since B>=h>0, (3) follows for the entire original mean interval.

Otherwise the rightmost point is the actual exposed vertex p. Choose
the two unit side vectors u=(c,s), v=(-s,c), with c,s>0 and c^2+s^2=1,
so X has vertices p,p-u,p+v,p-u+v. Its own coordinates at p are

    k=-ac+hs, j=as+hc>0.

The positive v-coordinate of its center means that its farthest circle
corner is p-u+v when k<=1/2, or p+v when k>=1/2. At a physical two-corner
tie either calculation is valid. These are original physical corners,
not replacements for the circle-load system.

For the adjacent corner p+v, k>=1/2 implies h>ac/s, whence

    j=as+hc>a/s>=a.

Therefore R^2=a^2+h^2+1+2j>=(a+1)^2+h^2.

For the opposite corner p-u+v, put C=c+s and D=c-s. The exact excess is

    R^2-[(a+1)^2+h^2]=1+2a(C-1)+2hD.                  (4)

If c>=s, every term on the right is nonnegative. If c<s, the actual
corner condition k<=1/2 gives h<=(1/2+ac)/s. Multiplying by D<0 in (4)
then gives

    1+2a(C-1)+2hD
       >= c/s+2a(1-s)/s >=0.                            (5)

This proves (3) for every original endpoint orientation and physical
circle mask, without a positive-concurrence premise.

One further endpoint bound will be used. Whenever h>=a>0,

    R^2 <= (a+1)^2+(h+1)^2.                             (6)

For an axis owner, B<=h+1 proves it directly. In the opposite-corner
case, aC+hD=(a+h)c+(a-h)s<=a+h, which gives (6) after expansion. In the
adjacent-corner case j<=sqrt(a^2+h^2)<=a+h, so its exact radius expression
is even smaller than the right side of (6). Thus both endpoint estimates
retain all faces, singletons, physical radial ties, and original means.

## 3. The strict port margin on the whole width-one channel

First suppose a<=0. Then b>=1, and the reflected right endpoint obeys
(3), giving

    h^2<=Q-(b+1)^2<=Q-4=81/256.

The unchanged left application consequently has

    |P_X|^2<(1/60)^2+81/256<(23/40)^2.

Every point of a unit lies within sqrt(2) of each of its vertices,
including an actual circle corner. Hence

    R<=|P_X|+sqrt(2)<23/40+57/40=2,

contrary to R>=2. Reflection rules out b<=0 as well. Thus a,b>0.

Suppose now that 0<a<=7/100. If h<=a, then

    R<=|P_X|+sqrt(2)<=sqrt(2)(1+a)
       <(3/2)(107/100)<2,

again impossible. Thus h>a. Apply (6) at X and (3) at the reflected Y:

    (2-a)^2+h^2 <= R^2 <= (a+1)^2+(h+1)^2.

Expansion gives h>=1-3a>0. Consequently

    R^2 >= (2-a)^2+(1-3a)^2
         =5-10a+10a^2
         >=4349/1000>1105/256.                          (7)

The quadratic is decreasing on [0,7/100], and the last positive reserve
is 1043/32000. This contradiction proves a>7/100. Reflection proves
b>7/100, completing (2). The vertex conclusion follows immediately
from the unchanged horizontal coordinates -a and b of every U vertex.

## 4. At most two units can be this close to the origin with every vertex far away

Here is a radius-free auxiliary statement. Let 0<delta<d/2 and d<1/2.
Suppose actual unit squares have pairwise disjoint open interiors,
each meets the closed disk D_delta, and every one of their vertices
has norm greater than d. Then there are at most two such squares.

For each unit S consider its open-interior intersection with the circle
|z|=d, measured by angular length. We prove that this length exceeds
2pi/3 in every location of the origin relative to S.

If O is outside S, its nearest point cannot be a vertex. In an actual
own frame therefore

    S=[a,a+1] times [b,b+1],
    0<a<=delta, b<0<b+1.

Both vertices on the nearest face are outside D_d, giving

    -b>sqrt(d^2-a^2), b+1>sqrt(d^2-a^2).

Every point of |z|=d with x>a lies strictly inside S: its transverse
coordinate has magnitude below sqrt(d^2-a^2), and x<=d<a+1. The contained
open arc has angular length 2 arccos(a/d)>=2 arccos(delta/d)>2pi/3.

If O lies on the boundary of S, it is in a relative side interior,
because every vertex is outside D_d. The same own-frame argument with
a=0 places an open semicircle in S, of length pi.

If O lies inside S, at most two of its supporting faces can cut the
circle |z|=d, and if two do they are adjacent: opposite faces are one
unit apart whereas the circle diameter is less than one. No cutting
face leaves angular length less than or equal to pi inside by itself.
For two cutting faces at positive distances a,b<d, the norm of their
common actual vertex gives a^2+b^2>d^2. Hence

    arccos(a/d)+arccos(b/d)<pi/2.

The total angular length removed by their two outward half-planes is
at most twice this sum, strictly less than pi. The interior part left
inside S has length greater than pi. Tangencies remove zero length;
faces not cutting the circle remove nothing. This exhausts the case.

Thus every proposed square occupies angular length greater than 2pi/3
on the same circle. Three disjoint square interiors would require total
angular length greater than 2pi. That is impossible, proving the lemma.

In particular the convenient exact constants

    delta=1/40, d=3/50                                  (8)

satisfy its strict hypotheses, since delta/d=5/12<1/2.

## 5. Earlier conditional application, superseded by the complete proximity proof

Keep either original four-load bare C6, with both actual transmitters
U,V side-normal, and the only remaining allocation (central,cap_U,cap_V)
=(1,1,1). Let T be the unchanged central extra and E_U,E_V the unchanged
two exterior extras. The accepted full central routing and local inner
square bounds in SHORT_DIAMETER_CONTACT_RING_CENTRAL_CAPACITY_ONE.md,
Section 5, apply to T with all original ring bodies retained. They give

    |each own center coordinate of T|<1/2+121/7200,
    every vertex norm of T>19/300>3/50.

The first inequality makes dist(O,T)<sqrt(2)*121/7200<1/40. The latter
strict comparison follows already from sqrt(2)<10/7 and 121/5040<1/40.
Section 3 gives every vertex of U,V norm greater than 7/100>3/50.

The remaining additional premise sufficient for a contradiction is:
each actual occupied cap extra lies wholly beyond its transmitter's
outward parallel side, in that channel's own frame. This is stronger
than the already proved inclusion y>=h and is NOT proved here.

Indeed write U as in (1), with outward side y=v+1. If its actual cap
extra satisfies y>=v+1 throughout, the sharp universal unit supporting-
height bound gives

    v+1<=D:=sqrt(R^2-1/4)-1<61/60,
    v<1/60.

Also v+1>=h>0, and -a<0<b. Thus dist(O,U)<1/60<1/40, whether O lies
inside U or just below its inward side. The same argument applies to V.
The three unchanged actual units T,U,V would then satisfy the complete
lemma in Section 4 with constants (8), a contradiction.

Therefore proving that full physical occupied-cap side-separation
property, or any other argument giving dist(O,U),dist(O,V)<=1/40,
would close the whole remaining all-side allocation simultaneously.
The port theorem and angular lemma themselves are unconditional in
their stated domains. No separation of E_U from U or E_V from V is
silently inferred from cap routing, center ordering, or a drawing.

No physical square is moved, no force or actual mean is changed, and
no coefficient packet, numerical pose, Lean compilation or CI is used.


## 6. Completed original join

The independently accepted whole-channel theorem
FOUR_C6_SIDE_OCCUPIED_CAP_TRANSMITTER_PROXIMITY.md proves directly that
an occupied actual side cap forces the original transmitter to lie
within1/60 of O, retaining every physical endpoint mask and mean.
It does not assume the stronger vertical-separation condition above.
GENERAL_SIDE_CHANNEL_CAP_CENTRAL_INJECTION_BOUND.md applies the present
unconditional port and angular theorems to an injective assignment of
ALL actual extras to original near-origin units, proving total capacity
at most two for every simple cycle with single-transmitter channels.
Its full original load-cover assembly closes the entire bare C6 after
both source and parent reviews. No positive-chord family is included.
