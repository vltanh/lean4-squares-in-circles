# Three balanced boundary squares cannot have one short and two channel-sized center gaps

**Status: complete reconstructed source, frozen for fresh full root and
independent review.** The workspace rollback removed the previously
reviewed version at SHA256
`c7722b12f07bd066865b785a188d3ecb1e977effc14586645ea871e2868a30e2`.
This text restores the complete proof and exact original caller; it
does not claim byte identity with that historical version or transfer
its review pin automatically.

Put \(Q=1105/256\), and work with actual interior-disjoint unit
squares in the same disk \(D_R\), where

\[
                       2\le R\le\sqrt Q.
\tag{1}
\]

## 1. Uniform metric theorem

Let \(A,B,C\) be three distinct physical boundary squares. Give
each square nonnegative weights at its actual physical circle
corners, with strictly positive total weight on each, and let
\(F_A,F_B,F_C\) be the corresponding circle resultants, omitting
the same harmless common normalization factor from all of them.
Assume

\[
                     F_A+F_B+F_C=0.
\tag{2}
\]

**Theorem.** It is impossible that their actual centers satisfy

\[
 |c_A-c_B|\le\sqrt2,\qquad
 |c_A-c_C|\le1+\sqrt2,\qquad
 |c_B-c_C|\le1+\sqrt2.
\tag{3}
\]

The theorem has no pair-force, degree, concurrence, owner, or
transmitter premise. Only the three actual circle resultants must
balance as in (2). Every physical radial mask and every zero
individual corner weight is retained.

## 2. Actual resultant order and the strict 210-degree bound

The one-square calculation in
`FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md`, Section 1, proves that
each physical circle corner has angular distance less than15 degrees
from its square's center direction whenever \(R^2>2+\sqrt3\).
This holds throughout (1). Every nonzero nonnegative resultant of
those corners lies in the same open30-degree cone and is nonzero.

For clarity, in outward own coordinates a circle corner and its
center are

\[
 z=(a,b),\quad a\ge b\ge\tfrac12,\quad a^2+b^2=q,
 \qquad c=(a-\tfrac12,b-\tfrac12).
\]

Their angular tangent is
\((a-b)/(2q-a-b)\). With \(t=a+b\), differentiation of
\(\sqrt{2q-t^2}/(2q-t)\) shows that its maximum is at \(b=1/2\)
and equals \(1/(2\sqrt{q-1/4})\). Since
\(q>2+\sqrt3\), this is less than \(\tan15^\circ\).
Continuity includes the diagonal circle corner and both radial masks.

`CIRCLE_CONTACT_ANGULAR_ORDER.md`, Lemma 2.1, gives pairwise minor
center separation greater than36 degrees. Thus the three open
15-degree intervals around the center directions are disjoint, and
their resultant directions have exactly the same cyclic order.
In particular the three resultant directions are distinct.

Three distinct nonzero planar vectors summing to zero cannot all be
collinear, because a line has only two directions. Their three
consecutive circular gaps are therefore strictly below180 degrees.
Indeed, a gap at least180 degrees would place all three vectors in
a closed half-plane through the origin; their sum could vanish only
if all three lay on its boundary line.

Choose compatible lifts of the center and resultant directions in
their common cyclic order. Each center-to-resultant correction has
absolute value less than15 degrees. Hence every consecutive
**directed** gap of the three center directions is strictly below

\[
                            210\text{ degrees}.
\tag{4}
\]

This is a directed-gap statement. It is not yet an assertion that
all three directed gaps are minor arcs; that point is proved next.

## 3. The three metric bounds force incompatible angular gaps

Every physical boundary center has radius at least
\(R-1/\sqrt2\). In the whole window (1),

\[
             |c_i|\ge2-\frac1{\sqrt2}>\frac97.
\tag{5}
\]

The last strict inequality follows from \(1/\sqrt2<5/7\).
Also

\[
                   \sqrt2<\frac{10}{7},\qquad
                   1+\sqrt2<\frac{17}{7}.
\tag{6}
\]

For center lengths \(r,s\) and minor center angle \(\gamma\),

\[
 |c_i-c_j|^2=(r-s)^2+4rs\sin^2(\gamma/2).
\]

Equations (3)--(6) consequently imply

\[
 \gamma_{AB}<2v,\qquad
 \gamma_{AC}<2u,\qquad
 \gamma_{BC}<2u,
 \quad
 v=\arcsin\frac59,\quad u=\arcsin\frac{17}{18}.
\tag{7}
\]

The exact comparison needed here is

\[
                            2u+v<\pi.
\tag{8}
\]

To prove it, \(u\in(\pi/4,\pi/2)\) and

\[
 \sin(2u)=\frac{17\sqrt{35}}{162}>\frac59=\sin v.
\]

The strict comparison is the positive integer identity
\(17^2\cdot35-90^2=2015>0\). Both \(\pi-2u\) and \(v\)
are in \((0,\pi/2)\), so sine is increasing there and yields
\(\pi-2u>v\), which is (8).

Since \(v>\pi/6\), (8) also gives

\[
                             2u<\frac{5\pi}{6}.
\tag{9}
\]

Thus every pairwise minor center angle in (7) is below150 degrees.
If any directed gap in the cyclic order were a major gap, it would
be the complement of such a minor angle and would exceed210 degrees.
This contradicts (4). A directed gap equal to180 degrees is likewise
impossible by (7)--(9). Hence all three directed gaps are their
respective minor angles.

Their sum is exactly \(2\pi\), whereas (7)--(8) make that sum
strictly less than \(2v+4u<2\pi\). This contradiction proves the
uniform theorem.

## 4. Actual side channels provide the two longer distance bounds

An actual one-unit side transmitter has opposite application points
\(P,Q\) at the same transverse coordinate and with
\(|P-Q|=1\). For its two endpoint squares \(X,Y\), every such
pair of actual aggregate means gives

\[
 |c_X-c_Y|
 \le |c_X-P|+|P-Q|+|Q-c_Y|
 \le\frac1{\sqrt2}+1+\frac1{\sqrt2}
 =1+\sqrt2.
\tag{10}
\]

This applies to the original means; no mean is moved to a vertex.
Whenever the original positive path is a true unloaded degree-two
channel and there is an actual unit square touching both endpoints,
`UNIT_BYPASS_NORMAL_CHANNEL.md` gives exactly one side transmitter,
with width one and the unchanged original common transverse mean.
The endpoint degrees and loads remain arbitrary in that theorem.

## 5. Entire original three-spoke pentagon load013 join

Use the original graph from
`SIX_BODY_INNER_PENTAGON_LOAD_COVER.md`: the exterior rim is
\(0-1-2-3-4-0\), and the interior unit \(H\) has the three
positive spokes \(H0,H1,H3\). There is no rim chord. Consider the
whole positive-load set \(\{0,1,3\}\), namely the original gate

\[
                  \boxed{\texttt{M6.B6.PENTAGON.H3.L013}}.
\]

Bodies \(2,4\) are genuine unloaded degree-two vertices. The
original paths \(1-2-3\) and \(0-4-3\) each have an actual unit
bypass \(H\), since \(H\) touches both of their endpoints.
The full unit-bypass theorem therefore makes both actual channels
side channels of width one. Equation (10) gives

\[
 |c_1-c_3|\le1+\sqrt2,\qquad
 |c_0-c_3|\le1+\sqrt2.
\]

The original rim contact \(01\) gives
\(|c_0-c_1|\le\sqrt2\). The three actual boundary squares
\(0,1,3\) thus satisfy every metric premise of Section 1.

Sum the original force equations over all six vertices of this
positive component. Each pair force cancels with its equal opposite
at its other endpoint. Since precisely \(0,1,3\) have positive
circle load, the remaining equation is

\[
                            F_0+F_1+F_3=0.
\]

This summation retains all three original spoke forces and all
original rim forces. The clear \(H\) keeps degree three, and each
of the loaded vertices \(0,1,3\) keeps its actual degree three.
None is treated as a degree-two loaded unit. The three strictly
positive actual circle resultants therefore satisfy (2), and the
uniform theorem gives a contradiction.

This excludes the complete original load representative and every
graph-preserving image, for all original physical masks, means,
circle-weight splits, selected normals, positive pair weights, and
all three unrestricted extra squares. A zero circle load at one of
the other component vertices is not turned into a physical
circle-clear assumption. The three extra squares remain part of
the original nine-packing throughout.

The same-nine radius-two lower bound supplies \(R>2\) in the
original counterexample setting; the local metric theorem includes
the weak endpoint \(R=2\). No other pentagon load set or entire
coarse six-body cell is declared closed here.
