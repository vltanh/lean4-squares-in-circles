# A diagonal channel incident to a physical radial endpoint forces radius squared below 17/4

Date: October 26, 2026.

**Status: complete degree-free local geometric theorem, accepted after
independent full-source root review in REVIEW_RADIAL_BOUNDARY_DIAGONAL_RADIUS_ROOT_2026_10_26.md.**
The original strict point-normal and diagonal
avoidance conventions are retained. No new normal is selected.

## 1. Full local statement

Work in the original radius window

\[
        79/40\le R\le\sqrt{1105}/16,\qquad
                  d=\sqrt{R^2-1/4}-1.
\tag{1}
\]

Suppose the original selected positive graph has an actual channel
X--V--Y, where:

- V is a true unloaded degree-two diagonal transmitter, with exact
  reserve sqrt(2) and unchanged common transverse application mean;
- X is physically radial, meaning that it has two physical circle
  corners;
- Y is physically circle-touching.

The two endpoints may have arbitrary true graph degrees, other
positive contacts, and any allowed circle-weight masks. X need not
carry equal circle weights, and a physical circle contact at either
endpoint need not have positive individual weight. No equation at
an endpoint beyond its actual support is used.

**Theorem.**

\[
                           d<1,\qquad R^2<17/4.
\tag{2}
\]

In particular a known radius lower bound R^2>=17/4 excludes every
such actual channel anywhere in the packing, independently of its
larger component, root, load allocation or other forces.

The original diagonal-avoidance prerequisite makes the channel
normal a side axis of both X and Y. This is an explicit hypothesis
from the common selected certificate, not an assumption that the
transmitter's diagonal direction is a side direction of V.

## 2. The complete radial axis cover

Use X's actual radial frame

\[
 X=[d,d+1]e+[-1/2,1/2]f,\qquad f=Je.
\tag{3}
\]

Its channel normal g toward Y is one of the four side axes.
The outer radial axis g=e is impossible by containment: the
actual reserve and the unit width of Y place a point at projection
at least d+1+sqrt(2)+1>R.
For a tangential axis g=+f or -f, the corresponding projection
is at least 1/2+sqrt(2)+1>R, also impossible.
The original radius upper bound is less than 25/12, so these
strict comparisons hold on the whole window.

Only g=-e remains. Its unchanged application is

\[
                P_X=de+yf,\qquad |y|\le1/2,
\]
\[
                P_Y=(d-\sqrt2)e+yf.
\tag{4}
\]

Because e is a side axis of Y and P_Y is its maximum e support,
Y has exactly the e-coordinate interval

\[
                  [d-\sqrt2-1,\ d-\sqrt2].
\tag{5}
\]

This retains the actual mean y; it is not replaced by a midpoint.

## 3. The far circle corner cannot retain that transverse mean at d>=1

Suppose d>=1 and set delta=d-1. The original upper radius bound
gives

\[
             0\le\delta<1/60,\qquad d<61/60<\sqrt2.
\]

Both endpoints of (5) are negative. The farthest absolute
e-coordinate of Y is therefore delta-sqrt(2).
If M is the larger absolute f-coordinate of its unit interval,
physical boundary contact gives

\[
 \begin{split}
 M^2&=R^2-(\delta-\sqrt2)^2\\
    &=9/4+(4+2\sqrt2)\delta.
 \end{split}
\tag{6}
\]

For delta>0, M>3/2. A unit interval whose maximum absolute
coordinate is M>3/2 lies either wholly above 1/2 or wholly below
-1/2. It therefore cannot contain the original y in (4).
This excludes the entire strict high-radius interval at once.

At delta=0, equation (6) gives M=3/2. The two possible unit
f-intervals of Y are exactly [1/2,3/2] and [-3/2,-1/2].
The only common transverse value with X's inner face is then
y=+1/2 or y=-1/2. Thus P_X is an inner vertex of X.
The diagonal normal strictly exposes a vertex of V, so this actual
X--V contact is point-only vertex/vertex. Its selected normal is
the side axis -e of X, contrary to the existing strict point-normal
convention. This explicitly excludes the original endpoint R^2=17/4
and every possible endpoint mean there.

No d>=1 alternative remains, proving (2).

## 4. Uniform applications and their exact scope

The theorem applies wherever the three physical-channel premises
in Section 1 hold. In particular:

| Existing setting | Additional proved fact | Exact consequence |
| --- | --- | --- |
| Any simple or chorded positive component | R^2>=17/4 | No actual diagonal transmitter can join a physical radial body to a physical boundary body. |
| Aligned S-leaf C5 load13, after the forced-radial far-endpoint theorem | C is radial and d>1 | The original B--V--C transmitter has reserve one. |
| A genuine D-leaf root with any actual positive-reserve normal channel to a physical boundary endpoint | The root contains the origin in its open interior, so the channel forces d>1 | Every other actual radial-to-boundary diagonal channel anywhere in the same packing is excluded. |

For the last row, the root channel's support h is strictly positive.
Its exact reserve w>=1 and the sharp center/half-width inequality
at its boundary endpoint give h+w<=d, hence d>1. This argument
retains every other root force and does not require root degree
three or a simple cycle.

These are structural consequences, not whole original graph gates.
A channel whose far endpoint is circle-clear, whose transmitter has
additional positive edges, or whose width is one does not meet
the local theorem's premises. Likewise the lower-radius domain
R^2<17/4 remains explicit.

No circle weight is reassigned, no physical body contracted, and
no endpoint concurrence or force balance is substituted. The proof
uses the original actual support and the exact original application
mean. There is no coefficient certificate, sampled sign, Lean
compilation or CI premise.
