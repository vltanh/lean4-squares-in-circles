# An exact fixed-point piercing theorem for perpendicular three-square caps

## Main theorem (arbitrary square orientations)

Suppose eight unit squares have pairwise disjoint open
interiors in a disk D_R centered at zero with

    sqrt(2)+1/2<R<=sqrt(9789/2500)<99/50.

Let C be the origin-containing central square.
Suppose three other squares lie **wholly** beyond
its right side at positive offset h_R and
three lie wholly beyond its upper side at
offset h_U. If

    h_R>=1/10,       h_U>=1/10,                     (1)

then the two three-square populations **must share
an actual square label**, which has central-owned
double-side status RU.

There is no assumption of common square orientations,
actual-contact edges, center-norm-at-least-one,
stress forces, or an idealized grid.

**Corollary — new S1 rejection.** In the
all-seven-single-side configuration S1=(3+0,3+1),
the perpendicular triple populations have
**no shared square**. Therefore

    S1 => min(h_triple1,h_triple2)<1/10.           (2)

When the triple side directions are normalized to
the positive x and y axes and the central square's
center is (a,b), this becomes

    **S1 => min(a,b)<-2/5.**                         (3)

The prior two-outer-center angular-lane argument
gave only 7/50. The present theorem is strictly
stronger and uses just elementary vertical and
horizontal sections of actual unit squares.

## 1. A universal chord reserve at a midpoint cap slice

First consider *three* unit squares in one cap

    D_R intersect {x>=h},
    1/10<=h<7/24.

The upper restriction h<7/24 holds automatically
whenever a cap of the stated eight-square disk
serves three squares, by the exact
HUMAN_THREE_SQUARE_CAP.md inequality:
q>=(1+h)^2+9/4 and
q<2257/576=(1+7/24)^2+9/4.

Set

    X=(R+h)/2,       m=(R-h)/2,
    B=sqrt(R^2-X^2).

The analytical radius bounds imply

    1<X<57/50,       m<47/50,       B<169/100.      (4)

For the first lower bound, R>sqrt(2)+1/2>19/10
and h>=1/10 give X>1.
For its upper bound, R<99/50 and h<7/24 give

    X<(99/50+7/24)/2=1363/1200
      <1368/1200=57/50.

For m, (R-h)/2<(99/50-1/10)/2=47/50.

For B, the squared expression
B^2=[3R^2-2Rh-h^2]/4 increases in R and
decreases in h. Hence

    B^2<(99/50)^2-(26/25)^2
        =7097/2500
        <28561/10000=(169/100)^2,

since 4*7097=28388<28561.

Take any one of the three arbitrary-frame squares.
Modulo quarter turns/reflection, choose its unsigned
angle 0<=theta<=pi/4 and put

    c=cos(theta),s=sin(theta),
    L=c+s in [1,sqrt(2)],    c*s=(L^2-1)/2.

Its horizontal projection has length L and is
contained in the strip [h,R]. At x=X, its
distance to either horizontal projection endpoint
is at least L-m>0.

Let ell be its **actual vertical chord length**
at x=X. If the chord crosses the square's
parallel-side plateau, ell=1/c>=1.
Otherwise, elementary intersection with the
square's sides gives

    ell=(L/2-|X-p_x|)/(c*s)>=(L-m)/(c*s).

The axis-aligned limit has ell=1.

We claim the uniform strict reserve

    **ell>947/1000**.                              (5)

It is immediate on the plateau. In the
sloping branch, because m<47/50,
it suffices to show

    L-(947/1000)*c*s>47/50.

The left side is the concave quadratic

    g(L)=L-(947/2000)*(L^2-1).

Its minimum on [1,sqrt(2)] lies at an endpoint.
At L=1, g=1>47/50. At L=sqrt(2),

    g=sqrt(2)-947/2000
      >707/500-947/2000
      =1881/2000>1880/2000=47/50.

The rational fact sqrt(2)>707/500 follows
from 2*500^2=500000>707^2=499849.
This proves (5) over the **full orientation
and center-position continuum**.

## 2. One of the three squares contains a fixed whole vertical segment

At x=X, the three square intersections are
open vertical chord intervals of lengths
ell_1,ell_2,ell_3>947/1000.
They are pairwise disjoint and all lie inside
the disk's vertical chord [-B,B].
Order them bottom-to-top; let the uppermost
chord be (y_low,y_high).

Since the three lower/upper chord intervals
are disjoint and ordered, the top chord's
upper endpoint satisfies

    y_high>=-B+ell_1+ell_2+ell_3
       >-169/100+3*(947/1000)
       =1151/1000>57/50.                           (6)

On the other hand, because the top chord is
contained in [-B,B] and its own length
exceeds 947/1000,

    y_low<=B-ell_top
       <169/100-947/1000
       =743/1000<1.                                (7)

Equations (6)--(7) prove that the **same
topmost actual square** has in its open
interior the entire segment

    { (X,y) : 1<=y<=57/50 }.                        (8)

This is stronger than merely containing a
single marked point: it is an exact common
piercing segment valid for every three-square
cap of offset h in [1/10,7/24), with
independent square frames.

## 3. Two perpendicular triples force a common square label

Apply section 2 to the three right-cap members,
using their offset h_R. At the midpoint

    X_R=(R+h_R)/2,

one square S_R among those three has the full
vertical open-interior segment

    {X_R} times [1,57/50].

Apply section 2 after interchanging x and y
to the three upper-cap members, using h_U.
At midpoint

    Y_U=(R+h_U)/2,

one square S_U among those three has the full
horizontal open-interior segment

    [1,57/50] times {Y_U}.

By (4), both X_R and Y_U belong to
the open interval (1,57/50).
Therefore the two segments cross at

    P=(X_R,Y_U),

and P lies in **the open interiors of both**
S_R and S_U. Packed squares have disjoint
open interiors, so S_R and S_U must be the
**same square label**.

That square lies wholly beyond the right
central side, because it was one of the R
triple, and wholly beyond the upper side,
because it was one of the U triple.
It therefore has central-owned double-side
status RU, proving the theorem. Reflections
and quarter-turns treat all other adjacent
side pairs. QED.

## 4. Consequences for the remaining patterns

* The pure all-single-side S1=(3+0,3+1)
  branch is impossible whenever both
  perpendicular triple side offsets are
  >=1/10. Thus only the narrow central-
  center band `min(a,b)<-2/5` survives
  after choosing the triple directions R,U.
  This is a **strictly larger continuous
  exclusion region** than the previous
  7/50/13/60 thresholds and applies to
  all outer-center counts k.

* In saturated Type A=(3+1,3+1), if both
  triples have offsets >=1/10, their
  shared RU double-status square **must be**
  both the highest midpoint-chord member
  of the R triple and the rightmost
  midpoint-chord member of the U triple.
  The angular pair theorem is not needed
  to establish this unique slice routing.

* If S1's exceptionally small-offset
  triple `h<1/10` has an opposite
  singleton (its 3+1 axis), the opposite
  side has offset `1-h>9/10`. The sharp
  one-square cap center envelope gives
  a still narrower **transverse lane**:

      (|z|+1/2)^2
          < q_plus-(19/10)^2
          =764/2500.

  Since (14/25)^2=784/2500>764/2500,
  this implies

      **|z|<3/50.**                                 (9)

  Thus the singleton must cross the
  corresponding diameter in a center
  strip of half-width just 3/50, for
  every possible square frame.

The theorem does not exclude S1 when one
triple line lies within 1/10 of the origin.
It does not force any contact graph or the
five-corner projected chain. The
unrestricted sharp lower bound
R8>=Rhat remains OPEN.
