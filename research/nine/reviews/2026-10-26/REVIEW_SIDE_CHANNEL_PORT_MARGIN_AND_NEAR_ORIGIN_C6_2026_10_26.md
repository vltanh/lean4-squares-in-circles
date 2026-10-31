# Independent review of the uniform side port margin and near-origin three-unit obstruction

Date: October 26, 2026.

Reviewer: C6 side-channel agent, independently of the source author.

Reviewed source:
`SIDE_CHANNEL_PORT_MARGIN_AND_NEAR_ORIGIN_THREE_UNIT_EXCLUSION.md`.

Reviewed SHA256:
`c56f056821eeda3d3c9536885e6edb56c028814d9a3567c99ff9e0abe98bbf3a`.

**Decision: ACCEPT the two unconditional geometric theorems and the
explicitly conditional complete C6 implication, exactly as stated.**
The review does not supply the missing occupied-cap proximity premise
and does not close an original four-load gate.

## 1. Whole physical side-channel domain

The original applications are retained as

    P_X=(-a,h), P_Y=(b,h), a+b=1,
    U=[-a,b] times [v,v+1], v<=h<=v+1, h>0.

The assumptions that the endpoint units meet the circle and have the
stated horizontal and vertical center signs are the complete actual
channel consequences used by the source. No concurrence hypothesis,
single-corner circle mask, positive individual corner weight, or fixed
application height is introduced.

I checked the center estimate M=91/60 from

    M^2+M+1/2-Q=31/57600>0.

The minimum half-width 1/2 then gives a,b<61/60 and a,b>-1/60 before
their signs are established.

## 2. Endpoint inequalities and strict port margin

For an axis owner, the whole original mean interval lies in the side
with upper coordinate B, and the nonnegative center height gives B>=1/2.
Both inequalities (3) and (6) are immediate from h<=B<=h+1.

For an oblique endpoint, I reconstructed the four physical vertices
p,p-u,p+v,p-u+v and the own coordinates k=-ac+hs, j=as+hc. Since j>0,
the farthest corner is exactly the adjacent or opposite corner listed
in the source, including the k=1/2 physical tie.

For k>=1/2, h>ac/s and j>a/s>=a prove the lower radius inequality.
For k<=1/2, expansion gives

    R^2-[(a+1)^2+h^2]=1+2a(c+s-1)+2h(c-s).

When c<s, substituting h<=(1/2+ac)/s with the correct reversed sign
reduces this exactly to

    c/s+2a(1-s)/s>=0.

When c>=s every term is nonnegative. The additional upper estimate
for h>=a follows from

    a(c+s)+h(c-s)=(a+h)c+(a-h)s<=a+h

in the opposite case, and j<=sqrt(a^2+h^2)<=a+h in the adjacent case.
This proves the endpoint bounds over every actual mask and mean.

If a<=0, the reflected endpoint gives h^2<=Q-4=81/256. Together with
a>-1/60 this gives |P_X|<23/40, contradicting R>=2 through the actual
unit diameter and sqrt(2)<57/40. Reflection gives b>0.

If 0<a<=7/100, h<=a contradicts R>=2 directly. Thus h>a, and combining
the two endpoint bounds gives h>=1-3a. Consequently

    R^2>=5-10a+10a^2>=4349/1000>Q.

The last reserve is exactly 1043/32000. The quadratic is decreasing
throughout the complete interval used. Reflection proves the other
port bound. Every unchanged U vertex therefore has norm greater than
7/100, independently of its transverse slider.

## 3. Complete angular obstruction

I checked all positions of O relative to a unit S whose vertices have
norm greater than d and which meets the closed disk D_delta, with
0<delta<d/2 and d<1/2.

If O is outside S, its nearest point cannot be a vertex. The own-frame
description with 0<a<=delta and b<0<b+1 is therefore exhaustive. The
strict lower distances of the two nearest-face vertices imply that
the entire open circle arc x>a lies in the open square. Its length is
2 arccos(a/d)>2pi/3.

If O is on the square boundary, it is in a relative side interior.
The strict vertex bounds give an open semicircle in the square.

If O is inside S, at most two adjacent faces cut the circle because
2d<1. When two do, the common-vertex condition a^2+b^2>d^2 implies
arccos(a/d)+arccos(b/d)<pi/2. Their total removed angular measure is
strictly below pi. Tangencies remove zero measure. With zero or one
cutting face the asserted bound is immediate.

Thus each actual square occupies strictly more than 2pi/3 of the same
circle in its open interior. Three pairwise disjoint open interiors
are impossible. The chosen delta=1/40,d=3/50 satisfy delta/d=5/12<1/2.
The proof does not need the occupied arcs to be connected in the last
case and does not assume general position.

## 4. Original C6 routing and the precise remaining premise

I checked the local inner-square conclusions used from Section 5 of
`SHORT_DIAMETER_CONTACT_RING_CENTRAL_CAPACITY_ONE.md`. They retain the
actual central extra and every actual ring body and give own center
coordinates of magnitude less than 1/2+121/7200, and every central
vertex norm greater than 19/300. Hence

    dist(O,T)<sqrt(2)*121/7200<121/5040<1/40,
    every vertex norm of T>19/300>3/50.

The last rational reserves are 1/1008 and 1/300 respectively. The two
actual side transmitters have every vertex norm greater than 7/100 by
the independently reviewed port theorem. Thus the full original
all-side (1,1,1) allocation is excluded as soon as both actual
transmitters are known to meet D_(1/40).

For completeness, the sharp supporting-height bound used in the
source's conditional sufficient criterion has a short direct proof.
If an actual unit is wholly above a positive height H, choose its
orientation c>=s>=0, c^2+s^2=1. The midpoint of its upper edge has
height at least H+c+s/2. On 0<=s<=1/sqrt(2), c+s/2>=1, as is verified
by squaring c>=1-s/2. The mean squared norms of the two endpoints of
that edge equal the midpoint squared norm plus 1/4. Consequently

    R^2>=(H+1)^2+1/4,
    H<=sqrt(R^2-1/4)-1<61/60.

The last strict comparison follows from
(121/60)^2-(Q-1/4)=31/57600>0. Therefore, under the source's explicitly
additional hypothesis that a cap extra lies wholly above U's outward
side y=v+1, we have v<1/60, v+1>=h>0 and -a<0<b. These conditions imply
dist(O,U)<1/60; likewise for V. The three-unit lemma applies exactly
as claimed.

The source does not assert that this whole vertical separation follows
from local channel routing. It identifies it as an unproved sufficient
premise and also allows the weaker direct proximity conclusion. The
review accepts that conditional implication only. No original family
is declared closed, and no missing force, load, mask, square, or mean
has been discarded.

No numerical sampling, Lean compilation, or CI was used in this review.
