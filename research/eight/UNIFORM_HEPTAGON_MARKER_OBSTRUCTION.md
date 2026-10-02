# Negative result: a uniform heptagon-gap marker is too strong

This rules out a specific tempting proof strategy, not the eight-square
conjecture. Even after the central-core reduction, the usual single-state
quarter-window marker cannot separate EVERY disjoint pair by 2*pi/7 at
squared radius 39/10.

## 1. Two exact admissible states

Use sorted states with negative transverse sign:

    S=(a,b)=(693/500,-1/12),
    T=(A,v)=(11/12,-7/8).

Both satisfy 0<=|b|<=a and have farthest-corner squared distance strictly below
39/10. They also avoid the disk of radius 1/12 by a wide margin: their nearest
closed-square distances exceed 1/12. Thus the central-core condition does not
remove these states.

Create two SEPARATE ordered pair configurations, both about the same disk
center. This is not a claim that the two configurations form one physical
four-square packing.

### First ordered pair: S then T

Put S in frame angle zero and T in frame angle pi/2. The vertical center
separation is

    A-b=11/12+1/12=1.

Their edge orientations agree modulo pi/2, so their open interiors are
disjoint. Both fit the same radius-sqrt(39/10) disk.

### Second ordered pair: T then S

Put T in frame angle zero and S in frame angle

    d=2 arctan(1/9),
    cos d=40/41, sin d=9/41.

The positive vertical separating margin in the first frame is

    (693/500) sin d-(1/12) cos d+7/8
      -(1+cos d+sin d)/2
    =47/123000>0.

Thus this pair also has disjoint interiors, with exactly rational frames and
centers. Rotating a state about the disk center preserves its containment.
The two positive relative frame angles sum to

    pi/2+2 arctan(1/9) < pi/2+2/9 < 4*pi/7,

where the first inequality follows from arctan x<x for x>0, and the second
from pi>28/9 (already implied by pi>157/50).

## 2. Obstruction to a single-state quarter-window marker

Suppose a marker for a negatively signed state uses angle

    frame_angle - ell(a,|b|),  with 0<=ell<=pi/4.

Let ell_S and ell_T be the two labels and put Delta=ell_S-ell_T, so
- pi/4<=Delta<=pi/4. The two ordered marker differences above are

    g1=pi/2+Delta,
    g2=d-Delta.

If g2<=0, its absolute value is at most pi/4-d<pi/4<2*pi/7. The desired
pairwise marker separation already fails in the second pair.

If g2>0, both g1 and g2 lie between zero and pi. They are therefore their
actual circular distances. But

    g1+g2=pi/2+d<4*pi/7,

so at least one is strictly below 2*pi/7.

Consequently NO label function of this natural quarter-window form can prove
pairwise separation >=2*pi/7 for all the admissible states above. This is
independent of whether that function is affine, nonlinear, learned, piecewise,
or defined by a large certificate.

The restriction on the marker window matters: this argument does not exclude
arbitrary discontinuous marker assignments that abandon the usual relation to
the square's side frame. It does rule out the direct n=7-style uniform-gap
shortcut proposed for the present n=8 state model.

## 3. Research implication

A sharp seven-exterior-ring proof must use more than a single universal
pair-gap lower bound at the heptagonal average. Possible additional information
includes the cyclic length SEVEN, transitions between state types, a coupled
three-square inequality, or the actual central obstacle.

Exploratory finite-state calculations show cheap two-step cycles but a higher
minimum for seven-step cycles. They suggest an odd-cycle obstruction, but do
not prove its continuous version. The exact two-pair argument above is the
proved negative result; the suggested seven-cycle mechanism remains open.
