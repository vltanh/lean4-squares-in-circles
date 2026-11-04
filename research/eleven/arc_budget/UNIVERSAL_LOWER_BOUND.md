# An unconditional squared-radius lower bound of 9/2

Every packing of eleven unit squares with disjoint interiors in a circular
disk has squared disk radius strictly greater than \(9/2\). Square
orientations are unrestricted.

For a square \(S\), write \(L_r(S)\) for its angular intersection measure
with the circle of radius \(r\) about the disk center. Define

\[
W(S)=\frac{41}{200}L_{3/10}(S)
 +\frac{63}{1000}L_{9/10}(S)
 +\frac{17}{50}L_{6/5}(S)
 +\frac7{25}L_{13/10}(S)
 +\frac{14}{125}L_{7/5}(S).
\]

The five weights are positive and sum to one. The finite exact certificate
`UNIVERSAL_BOUND_COVER.json` proves the single-square statement

\[
S\subseteq\overline B_{\sqrt{9/2}}
\quad\Longrightarrow\quad W(S)\ge23/40.
\tag{1}
\]

The sum of occupied angular measures of disjoint-interior squares is at
most \(2\pi\) on every positive-radius circle. Indeed the boundary of a
square meets a circle in only finitely many points, so any positive-measure
overlap would include an interior point of both squares. Positive weighted
summation therefore gives \(\sum_S W(S)\le2\pi\). Eleven copies of (1)
would instead give

\[
\sum_S W(S)\ge\frac{253}{40}>\frac{44}{7}>2\pi.
\]

The strict rational difference \(253/40-44/7\) is \(11/280\). This proves
the theorem, including exclusion of equality \(q=9/2\).

The individual-pose cover uses exactly the elementary geometry and rational
arc lower bounds proved in `WEIGHTED_ARC_EXCLUSION.md`. Express the center
in the square's own frame and use frame reflections and coordinate exchange
to assume \(a\ge b\ge0\). The exact containment condition is

\[
(a+1/2)^2+(b+1/2)^2\le9/2.
\]

The initial closed box \([0,7/4]^2\) covers this domain because
\(9/2<81/16\). A leaf box \([a,A]\times[b,B]\) is discarded only if
\(A<b\) or \((a+1/2)^2+(b+1/2)^2>9/2\). Both tests are strict, preserving
all boundaries. Every other terminal box proves (1) by summing exact lower
bounds for the intersections of the five circles with the universal
contained rectangle

\[
[A-1/2,a+1/2]\times[B-1/2,b+1/2].
\]

Every internal node bisects a coordinate interval at its exact midpoint,
with both closed children recorded. The resulting tree has 2,385 nodes,
980 arc leaves, 213 discard leaves, and maximum depth 21. The elementary
function bounds use only rational arithmetic, integer square roots,
alternating arctangent series, and the Machin identity for pi.

Run `python generate_universal_bound.py` to regenerate the tree and
`python check_universal_bound.py` to replay it. The replay imports the
already audited elementary-function module `exact_arcs.py`, but does not
import or trust the generator. It checks all metadata, every cover split,
every strict discard reason, and every one of the 980 arc inequalities.
The scripts reject Python's `-O` mode, which would disable assertions.

This is a global lower bound, not the conjectured sharp n=11 value near
\(4.9012064\). Its useful consequence for stress classifications is that
any proposed exact minimizer class forcing \(q\le9/2\) is impossible.
