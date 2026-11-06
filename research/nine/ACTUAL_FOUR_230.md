# A central cone endpoint is high, and the complete (2,3,0) closure

Complete hand proof, independently reviewed, 5 November 2026.
This replaces the archived central-right endpoint certificate by
two explicit convex endpoint checks. No mathematical script is used.

Put Q=1105/256, r=sqrt(Q), rho=91/60, l=29/60, u=13/12.

## 1. Complete original-square statement

Let original interior-disjoint physical unit squares in the centered
Q-disk contain an actual horizontal four-chain M0<_x M1<_x M2<_x M3,
whose consecutive centers also satisfy the horizontal cone comparisons.
Let L<_c P<_c R be a disjoint original outsider horizontal cone
three-chain. Suppose its right endpoint is central, |x_R|<=l, and

    y_P>3/5.                                         (1)

Then

    y_R>3/5.                                         (2)

No whole-floor assumption on P is required. No selected cone edge is
declared an actual projection edge. All centers and half-unit disks in
the proof belong to the same unchanged original squares.

For a unit S, its contained aligned-square halfwidth satisfies
g_S>=1/(2sqrt(2)). Every physical cone comparison gives

    x_T-x_S>=g_S+g_T>=1/sqrt(2)>7/10.

Its proof is immediate from the two original insets: one coordinate gap
must be at least g_S+g_T, while the cone comparison makes the horizontal
gap at least the vertical gap. Thus, writing x_P=p and x_L=-Z,

    -23/60<p<-13/60,
    11/12<Z<13/12.                                  (3)

For the first lower bound use x_L>-u and x_P-x_L>7/10. For the first
upper bound use x_R<=l and x_R-x_P>7/10. For the Z lower bound use
x_R-x_L>=sqrt(2)>7/5. These bounds hold independently of vertical order.

The standard actual-four and common-cone routing bounds give

    y_L>27/40.                                       (4)

Here is a complete derivation of the needed routing fact. The main
heights satisfy |y1|,|y2|<139/120 and |y2-y1|<31/30. P's horizontal
gap to either inner main is less than 9/10, and their inset halfwidths
exceed 12/25. The half-unit disk of P gives

    |y_P-y_i|>(12+sqrt(46))/25>3/4.

It cannot lie between the two main heights, since that would require
their difference to exceed 3/2>31/30. It cannot lie below both either:
(1) would put each main above 3/5+3/4=27/20>139/120. Therefore P
is above both, with the displayed positive vertical gaps.

L's horizontal gap from M1 is less than 3/5, so the corresponding
physical clearance is |y_L-y1|>29/30. If L were below M1, then
y_P-y_L>103/60, contrary to their cone comparison and the outsider
strip. Thus L is above M1 and y_L>-23/120. Its horizontal center gap
from M0 is less than 3/5, by (3) and the endpoint x-band, so the two
half-unit disks give |y_L-y0|>4/5. The lower alternative would give
y_L<1/8-4/5=-27/40, contradicting y_L>-23/120. Therefore L is above
M0, and y_L>-1/8+4/5=27/40. This proves (4) without a selected
projection edge or a selected separating-axis owner.

## 2. The retained endpoint raises L above 17/20

Reflect horizontally so L has center (Z,y_L). The original reflected
outer endpoint contains the fixed rectangle

    [A,B] x [-c,c],
    A=503/480, B=937/480, c=221/600.

This is the standard actual-four endpoint inset consequence. By (3),
Z<B and its horizontal distance to this rectangle is at most

    max(A-Z,0)<A-11/12=21/160.

By (4), y_L>c. The unchanged half-unit disk of L is disjoint in
interior from the rectangle. Its exact center-to-rectangle distance
therefore yields

    y_L>c+sqrt(1/4-(21/160)^2)>17/20.                 (5)

The last comparison is between positive quantities and has squared
reserve

    1/4-(21/160)^2-(17/20-c)^2
        =4439/5760000>0,
    17/20-c=289/600.

This step uses only the original L incircle and the contained endpoint
rectangle; no normal owner or physical orientation is lost.

## 3. P cannot be below L

Suppose y_P<=y_L. From (1), (3), and the universal center bound,

    |c_P-c_L|^2
       <(Z-13/60)^2+(sqrt(rho^2-Z^2)-3/5)^2=:f(Z).

All distances bounded here are nonnegative: Z>11/12 and -p>13/60,
while y_L>=y_P>3/5. Expanding f shows that its only nonlinear term
is -(6/5)sqrt(rho^2-Z^2). Thus f is convex on [11/12,13/12] and its
maximum is at an endpoint.

At Z=11/12,

    rho^2-Z^2=73/50<(121/100)^2,
    f(11/12)<(7/10)^2+(61/100)^2=8621/10000<1.

At Z=13/12,

    rho^2-Z^2=169/150<(17/16)^2,
    f(13/12)<(13/15)^2+(37/80)^2=55585/57600<1.

The radical comparisons have squared reserves 41/10000 and 43/19200,
respectively. Hence |c_P-c_L|<1, contradicting their two disjoint
original half-unit disks. We have proved

    y_P>y_L>17/20.                                  (6)

## 4. A low R would force the same two original disks to overlap

Suppose contrary to (2) that y_R<=3/5. The actual cone comparison
P<_c R gives

    y_P-y_R<=x_R-p,
    y_P<=3/5+l-p=u-p.

Together with (3), (5), and (6), this bounds the squared distance of
the same original L,P by

    |c_P-c_L|^2
      <(u+p)^2+(u-p-17/20)^2
       =(u+p)^2+(7/30-p)^2=:F(p).

The function F is convex on [-23/60,-13/60]. Its endpoint values are

    F(-23/60)=3133/3600,
    F(-13/60)=3433/3600.

Both are less than one. This again contradicts the two original
half-unit disks. Therefore y_R>3/5, proving (2) on the complete domain.
All comparisons include the proposed boundary y_R=3/5.

**Immediate five-square consequence.** Section 3 also proved
y_P>y_L>17/20, independently of the low-R contradiction in Section 4.
Since h_P<=1/sqrt(2)<3/4, it follows that y_P-h_P>1/10. Thus any
original selected triple in this lemma with y_P>3/5 already supplies
all three upper-square hypotheses of the
[five-square cap](FIVE_SQUARE_CAP.md): L and R are opposite high
shoulders and P is the central original with a high whole floor.
Together with the actual-four outer endpoints this gives D<=2,
and contradicts every normalized span D>2.

## 5. Complete normalized (2,3,0) occupancy consequence

Retain the original nine squares, the actual-and-cone main chain, and
the designated outsider cone three-chain. Normalize any hypothetical
strict counterexample by common center expansion to closed-disjoint
units in Q. This consequence concerns outsider count (2,3,0) at those
normalized positions; it does not assume an unnormalized count remains
unchanged. The adjusted original endpoint span then satisfies D>2.

There is no right-side outsider. The selected triple cannot have all
three members central because its horizontal span exceeds sqrt(2),
while the central width is 29/30. Its middle is central by the usual
single-edge bounds. Hence its original L is on the left side and P,R
are distinct central originals. The same horizontal gap bounds give
|x_P|<23/60 and x_R>19/60. As in Section 1, P has physical vertical
gap greater than 3/4 from both inner mains. It cannot lie between their
heights, since |y2-y1|<31/30. Choose the common vertical reflection
putting P above both.

The selected L cannot lie below M1: its own-half clearance 97/100
would then give y_P-y_L>3/4+97/100>22/15, whereas its cone gap is
x_P-x_L<23/60+13/12=22/15. Similarly, the central positive R cannot
lie below M2: its own-half central clearance would give
y_P-y_R>3/4+59/60>2l, whereas x_R-x_P<2l. Equality with a main
height is excluded by the same clearances. Thus selected L is above
M1 and selected R is above M2. This routing argument does not depend
on a caller that assumes two upper central outsiders.

Selected L is already a high shoulder before any center-height estimate
on P. Indeed y_L>y1+97/100>-113/600. Its horizontal gap from M0 is
less than 3/5, so their original half-unit disks give
|y_L-y0|>4/5. The lower alternative would imply
y_L<1/8-4/5=-27/40, a contradiction. Hence

    y_L>27/40>3/5.                                  (7)

The full left side's main is either bottom or middle; it cannot be top
because selected L is above it. In both possibilities the same selected
original P has center height greater than 3/5.

* If the main is bottom, the other left outsider S is also above it.
  The signed side-pair cap in [ACTUAL_FOUR_FULL_SIDES.md](ACTUAL_FOUR_FULL_SIDES.md)
  Section 2 gives y_S<7/16, since L is already above 27/40. Thus S is
  the lower outsider, and Section 3 of that chapter gives
  y_S>-113/600 and |x_S|<zeta=2211/4000. Both S and P are in the
  negative horizontal half-plane, with x_S<=-l<x_P<0, so their
  horizontal gap is less than zeta. Since zeta^2<11/36, their original
  half-unit disks give |y_P-y_S|>5/6. Also P's own-half central
  clearance gives y_P>-139/120+59/60=-7/40. If P were below S, it
  would instead have y_P<7/16-5/6=-19/48, a contradiction. Therefore
  y_P>y_S+5/6>129/200>3/5.
* If the main is middle, y1>-7/20. The original cone comparison P<R
  places P on the negative side by (3). Its own-half central clearance
  consequently gives y_P>y1+59/60>19/30>3/5.

The immediate five-square consequence above now gives D<=2 in either
case, contradicting the normalized D>2. No separate whole-floor
extraction or coupled cone-loss input is needed in this caller.

This closes every normalized (2,3,0) configuration in the stated
actual-and-cone / designated-cone-triple domain, with no split according
to the third central original's vertical position. All nine originals
and their constraints are retained; the terminal can already be
extracted from a subset. Horizontal reflection closes (0,3,2).

The shared caller inputs are the actual-four localization and center
clearances, the reviewed side-pair and low-side center geometry in
[ACTUAL_FOUR_FULL_SIDES.md](ACTUAL_FOUR_FULL_SIDES.md), and the completed
[five-square cap](FIVE_SQUARE_CAP.md). Their exact local contracts are
used above. No coupled-floor input, two-low-main certificate, or
central-right interval certificate is needed.
