# A D-leaf three-loaded C4 cannot have a shared vertical-force contact at A

**Status: complete hand branch theorem; root and separate independent full hand
audits passed.** This source closes the entire nonparallel
articulation branch in which one cycle reaction is vertical and its
application is an arbitrary mean on a positive-length shared side. It
uses the complete nonparallel concurrence and owned-tip estimates of
`D_FOUR_CYCLE_NONPARALLEL_SINGLETON_EXCLUSION.md`, Sections 2--3. No
shared mean is fixed before the multipliers are extracted. All physical
circle masks, all other contact owners and all four extra squares are
retained.

## 1. Full branch and the actual mean

Work in the declared window
\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\qquad
 s=1+\sqrt2-R,\qquad r=1-s=R-\sqrt2.
\]
Let the selected positive graph be the cycle `A-B-U-C-A` with a radial
D leaf attached to its physically clear articulation A. Its three other
cycle bodies are loaded and physically circle-touching. Normalize the
leaf east. The full articulation is
\[
 A=[-s,r]\times[-v,H],\qquad H+v=1,\qquad H,v>0,
 \tag{1}
\]
and the leaf is the unit diamond with vertices
\[
 (r,0),\quad(r+\sigma,\sigma),\quad(R,0),
 \quad(r+\sigma,-\sigma),\qquad \sigma=1/\sqrt2.
 \tag{2}
\]
Reflect across the horizontal axis so that the shared cycle contact is
AB on A's top side. Its outward normal is `e_y`, and its actual
weighted-mean application is
\[
                  P_B=(q,H),\qquad -s\le q\le r.
 \tag{3}
\]
The other cycle normal is necessarily strictly southwest: the positive
horizontal leaf force and the positive upward AB force determine both
of its coordinate signs. Write
\[
 P_C=(-s,-v),\qquad n_C=(-d,-c),\qquad
 c,d>0,\quad c^2+d^2=1.
 \tag{4}
\]
This AC contact is a singleton because its normal exposes the strict
lower-left A vertex. It can initially be either C-owned or a genuine
vertex/vertex contact.

The general nonparallel articulation theorem in
`D_FOUR_CYCLE_NONPARALLEL_SINGLETON_EXCLUSION.md`, Section 2, applies
with the actual mean (3), all physical circle masks, and no AC ownership
assumption. It gives a positive concurrence on the leaf axis. A's own
force and torque equations identify it exactly:
\[
                  q=q_A=-s+\frac{vd}{c},\qquad 0<q\le r.
 \tag{5}
\]
Indeed, if the AC magnitude is `mu`, vertical balance makes the AB
magnitude `mu c`; torque then reads
`mu c q + mu(sc-vd)=0`. In particular (5) does not replace an unknown
side mean by a vertex or by the side midpoint.

## 2. A compatible strict selection removes the free AC alternative

The following choices are made before the multiplier theorem, together
with the existing finite generic conditions. They preserve strict
vertex/vertex normals, nonradiality and the mirrored four-square-junction
convention. They do not choose an axis normal at a point contact.

Suppose the physical AC contact is vertex/vertex. A's outward normal
cone there is the closed southwest quadrant, of angle `pi/2`. The
negative of C's outward vertex-normal cone also has angle `pi/2`.
Their interiors intersect in the nonempty open interval from which a
strict common normal must be selected. An endpoint of this interval is
an A-axis direction, either `-e_x` or `-e_y`. To see this, two intervals
of equal length `pi/2` cannot have one strictly contained in the other;
if their endpoints coincide, the same assertion is immediate.

Write the selected strict southwest normal as
\[
             n_C=(-\cos\psi,-\sin\psi),
             \qquad 0<\psi<\pi/2.
\]
If an available A-axis endpoint is `-e_x`, choose this normal in a
sufficiently small open neighborhood of that endpoint within the
admissible interval. Then
\[
                    -s+v\cot\psi>r.
\]
If the available endpoint is `-e_y`, choose a sufficiently small strict
neighborhood of that endpoint instead. Then
\[
                    -s+v\cot\psi<0.
\]
Both alternatives contradict (5). The two strict inequalities are
possible because `v>0`, `s>0`, and the limiting values are respectively
positive infinity and `-s`. Thus a positive free AC edge cannot survive
these choices.

Here is the simultaneous-choice justification. There are only finitely
many physical candidate stars in a fixed packing. Every physical D-leaf
articulation in this window contains the origin in its interior, by
(1); disjoint interiors therefore give at most one such physical
square A. If that A admits more than one candidate D-leaf direction,
each is one of its side axes. For every role of the present kind,
*either* available A-axis endpoint makes the corresponding strict
concurrence bound fail: one is parallel to its leaf axis, and the
other has its concurrence at the negative support coordinate.
Consequently the endpoint neighborhoods can be chosen small enough
for all candidate roles sharing a physical point.

At a four-square junction all four frames are aligned. The admissible
opposite-edge normals use the existing mirrored parameter pair
`(a,b),(a,-b)` with `a,b>0`. Taking the common ratio toward zero or
positive infinity keeps both normals strict and makes both approach
coordinate axes. The edge incident to A therefore has the just-proved
forbidden-concurrence property; the other diagonal cannot belong to a
second D articulation. The previously required finite nonzero
determinants and nonradial conditions can still be imposed inside
these open parameter intervals. At non-fourfold points the normal
parameters are independent. The C7 endpoint-neighborhood selections
concern edges between physical boundary bodies and do not constrain an
edge incident to this physically clear A. At a matched four-junction,
the other diagonal cannot be a boundary--boundary pair either: C is
already a boundary body, so that would put three boundary squares at
one point, contrary to `CYCLIC_GLOBAL_CONTINUATION.md`, Section 7.
Thus the new conditions are
compatible with the existing selected certificate. Uncrossing and
thinning leave every surviving point-edge normal unchanged.

We conclude that AC is C-owned. Moreover, `P_C` is in the relative
interior of its C side. Otherwise both bodies would meet at vertices
and the common normal would be an endpoint of C's vertex cone,
contrary to the retained strict point convention.

## 3. The owned lower tip makes the entire upper shared neighbor too central

Put `L=q+s`. Equation (5) gives `0<L<=1`. The full owned-lower-tip
estimate of `D_FOUR_CYCLE_NONPARALLEL_SINGLETON_EXCLUSION.md`,
Section 3, now applies: it assumes only (1), (4), the positive
concurrence, C ownership, and `q<=r`. It does not require a singleton
AB application. Its conclusion, including every physical C mask, is
\[
                         v>\frac34,\qquad H<\frac14.
 \tag{6}
\]

Because AB is a positive-length shared side, B has the aligned form
\[
                    B=[x,x+1]\times[H,H+1].
 \tag{7}
\]
Its actual mean `(q,H)` belongs to that side. Since `q>0`,
\[
                         x\ge q-1>-1,
                         \qquad x\le q\le r.
 \tag{8}
\]
Actual disjointness from the D leaf forces
\[
                              x+1\le r+H.
 \tag{9}
\]
For a direct proof, the leaf's horizontal interior at height
`y in (0,sigma)` is the interval `(r+y,R-y)`. If `x+1>r+H`, choose
a sufficiently small positive epsilon so that `H+epsilon<sigma` and
`x+1>r+H+epsilon`. Since `x<=r`, at height `H+epsilon` the interiors
of (7) and the leaf then overlap. This contradicts the packing.
The inequality `H<1/4<sigma` ensures this argument also handles the
endpoint tangencies in (9).

Use `r<2/3` and (6)--(9). Every point of B lies in the strict rectangle
\[
                        -1<X<\frac{11}{12},
                        \qquad 0<Y<\frac54.
\]
Consequently every B corner satisfies
\[
                       |z|^2<1+\frac{25}{16}
                              =\frac{41}{16}
                              <\left(\frac{79}{40}\right)^2.
 \tag{10}
\]
Thus B is physically circle-clear, contradicting the branch hypothesis.
This last step bounds all four corners at once and does not assume a
unique B circle corner or a particular B load split.

The lower shared-side alternative is the reflected argument. This
closes the entire nonparallel D branch with a vertical A reaction on a
positive-length shared side. Combined with the companion singleton
source, all nonparallel A-reaction branches are excluded. The parallel
horizontal A reactions remain a separate gate until their own complete
argument is supplied.

No numerical pose scan, Lean compilation, or CI is a premise.
