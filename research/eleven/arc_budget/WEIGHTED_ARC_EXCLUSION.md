# At most four centers within radius 41/40

Assume eleven closed unit squares have disjoint interiors and lie in the disk
centered at the origin with squared radius at most

\[
U=49013/10000.
\]

No common-frame assumption is made. Put \(r_0=41/40\). This note proves
that at most four square centers can have distance at most \(r_0\). In
particular it excludes all cases with five or more centers at this threshold,
with either convention at the core/ring boundary.

The certificate consists of two closed covers of a two-dimensional domain
of individual square poses. It does not enumerate packings. The already
proved lower bound of three core centers is separate; combining it with
this result leaves only three or four core centers.

## A weighted circle measure

For a square \(S\), let \(L_r(S)\) be the angular measure, in radians, of
its intersection with the circle of radius \(r\) centered at the origin.
Define

\[
W(S)=\frac3{100}L_{3/10}(S)
     +\frac{17}{40}L_{3/5}(S)
     +\frac{109}{200}L_{5/4}(S).
\]

All three weights are positive and sum to one. The two certified estimates
are

\[
\begin{aligned}
 |p_S|\le41/40&\quad\Longrightarrow\quad W(S)\ge43/50,\\
 |p_S|\ge41/40,\ S\subseteq\overline B_{\sqrt U}
   &\quad\Longrightarrow\quad W(S)\ge17/50.
\end{aligned}
\tag{1}
\]

For a packing, \(\sum_S L_r(S)\le2\pi\) on every positive-radius circle:
positive-length overlap would contain a point in both square interiors,
because each square boundary meets the circle in only finitely many points.
Thus \(\sum_S W(S)\le2\pi\). If at least five centers have distance at
most \(r_0\), use the first estimate for all such centers and the second
for the others. The resulting sum is at least

\[
5\frac{43}{50}+6\frac{17}{50}
=\frac{317}{50}>\frac{44}{7}>2\pi.
\]

The first strict rational difference is \(19/350\). Additional core
centers only increase the lower bound. This proves the assertion.

## Individual-pose domains and closed covers

Express a square center in its own orthonormal frame. Reflection in either
frame axis and exchange of the two axes preserve concentric-circle angular
measure, so assume the center is \((a,b)\) with \(a\ge b\ge0\). The
square is the axis rectangle

\[
[a-1/2,a+1/2]\times[b-1/2,b+1/2].
\]

Its farthest-corner squared distance is exactly
\((a+1/2)^2+(b+1/2)^2\). Consequently the two domains to certify are

\[
\begin{aligned}
D_c&=\{a\ge b\ge0:a^2+b^2\le r_0^2\},\\
D_r&=\{a\ge b\ge0:a^2+b^2\ge r_0^2,
                  (a+1/2)^2+(b+1/2)^2\le U\}.
\end{aligned}
\]

The initial closed boxes are \([0,r_0]^2\) and \([0,7/4]^2\), respectively.
The second covers \(D_r\), because \(U<81/16\) implies
\(a,b<\sqrt U-1/2<7/4\).

A box \([a,A]\times[b,B]\) may be discarded only for one of these strict,
exact rational reasons:

- `below-diagonal`: \(A<b\);
- `outside-core`, for the core cover: \(a^2+b^2>r_0^2\);
- `inside-core`, for the ring cover: \(A^2+B^2<r_0^2\);
- `outside-disk`, for the ring cover:
  \((a+1/2)^2+(b+1/2)^2>U\).

All boundaries therefore remain covered. Otherwise a terminal box must
prove the corresponding lower bound in (1). Every nonterminal box splits
one coordinate interval at its exact midpoint, into two closed children.
The certificate records the entire binary tree, including every discard
leaf. No sampling, floating-point feasibility decision, or tolerance is
used in the proof.

## A lower bound valid throughout a pose box

The rectangle

\[
T=[A-1/2,a+1/2]\times[B-1/2,b+1/2]
\]

is contained in every square with center in that box. If either interval
is empty, take the lower bound zero. Otherwise compute a lower bound for
its circle intersection separately in each quadrant. Reflect the quadrant
into the first quadrant and intersect the resulting coordinate intervals
with \([0,r]\), giving \([l_x,u_x]\times[l_y,u_y]\).

If these intervals are nonempty, the allowed angle interval has endpoints

\[
\begin{aligned}
\theta_{\min}&=\max(\arccos(u_x/r),\arcsin(l_y/r)),\\
\theta_{\max}&=\min(\arccos(l_x/r),\arcsin(u_y/r)).
\end{aligned}
\]

Its measure is \(\max(0,\theta_{\max}-\theta_{\min})\). Lower-bound
\(\theta_{\max}\), upper-bound \(\theta_{\min}\), and sum over the four
quadrants. The axes contribute measure zero, so their repeated endpoints
cause no overcount. Positive weighted sums of these bounds prove each
terminal `arc` leaf.

## Exact elementary-function bounds

`exact_arcs.py` uses rational arithmetic throughout. For rational \(x\ge0\),
integer square root at scale \(10^{14}\) returns rational endpoints
\(l\le\sqrt x\le u\), checked by \(l^2\le x\le u^2\).

For \(0\le t\le1/2\), the alternating series

\[
\arctan t=t-t^3/3+t^5/5-\cdots
\]

is enclosed between an 18-term partial sum and that partial sum plus its
next signed term. The same rule with 30 and 10 terms at \(1/5\) and
\(1/239\) gives rational bounds for

\[
\pi=16\arctan(1/5)-4\arctan(1/239).
\]

For completeness, the tangent double-angle identity gives
\(\tan(4\arctan(1/5))=120/119\), hence the tangent subtraction identity
gives \(\tan(4\arctan(1/5)-\arctan(1/239))=1\). The angle lies in
\((0,\pi/2)\), proving this Machin identity. The resulting upper bound is
checked to be less than \(22/7\).

For \(0\le z\le3/4\), use

\[
\arcsin z=2\arctan\frac{z}{1+\sqrt{1-z^2}},
\]

whose arctangent argument is less than \(1/2\). For \(3/4<z<1\), first use
\(\arcsin z=\pi/2-\arcsin\sqrt{1-z^2}\); the new argument is less than
\(3/4\), even after the specified outward square-root rounding. The
endpoints 0 and 1 are handled exactly using the rational pi bounds. Finally
\(\arccos z=\pi/2-\arcsin z\). Every use of monotonicity and subtraction
selects the outward endpoint.

## Files and replay

- `exact_arcs.py`: exact rational elementary-function and arc lower bounds.
- `generate.py`: deterministic complete-cover generator.
- `CORE_ARC_COVER.json`, `RING_ARC_COVER.json`: full closed-cover trees.
- `check_weighted_arc_cover.py`: structural and arithmetic replay, independent
  of the generator's subdivision or discard code.

Run `python generate.py` to regenerate both certificates, then
`python check_weighted_arc_cover.py` to replay them. File paths are resolved
relative to the script. JSON trees have schema `weighted-circle-arcs-v1`;
`split` gives axis 0 or 1 and the two child nodes, `discard` names one of the
strict tests above, and `arc:true` requires fresh exact evaluation of the
weighted lower bound. Leaf bounds themselves are not trusted input.

The core cover has 4,367 nodes, 1,933 arc leaves, 251 discard leaves, and
maximum depth 20. The ring cover has 423 nodes, 104 arc leaves, 108 discard
leaves, and maximum depth 18. These finite certificates establish only the
count restriction; the remaining three- and four-core geometric cases
still require further arguments.
