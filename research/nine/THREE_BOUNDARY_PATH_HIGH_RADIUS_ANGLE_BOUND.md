# A high-radius three-body boundary path has endpoint angle below 11/4

Date: October 26, 2026.

**Status: complete geometric implication, accepted after fresh root and
separate independent full-source reviews.** See
REVIEW_D_LEAF_C5_THREE_LOADS_AND_ANGLE_ROOT_2026_10_26.md and
REVIEW_D_LEAF_C5_THREE_LOADS_AND_ANGLE_C6_2026_10_26.md.
This source is independent of all body degrees and force-balance
equations. It adds no finite sign packet.

Let B,M,C be three distinct actual unit squares with disjoint open
interiors in the disk of radius R, where
\[
 \frac{\sqrt{17}}2<R\le\frac{\sqrt{1105}}{16}.
\tag{1}
\]
Suppose all three physically touch the circle, and B touches M while
M touches C. Assign arbitrary nonnegative weights of positive total
to the physical circle corners of each endpoint. Let F_B,F_C be the
resulting nonzero radial vectors. Both physical two-corner masks and
all individual zero weights are allowed.

**Theorem.** Along the actual B--M--C boundary-path order, the endpoint
resultant angle is strictly less than
\[
 \frac{11}{4}\ \text{radians}.
\tag{2}
\]
This is less than pi, so it is also their minor angular separation.
The same conclusion applies to any choice of one physical circle
corner at each endpoint.

## 1. A stronger whole-radius center estimate

Every boundary-square center c obeys
\[
 |c|\ge R-\frac1{\sqrt2}>\frac{27}{20}.
\tag{3}
\]
Indeed \(\sqrt{17}/2>103/50\), with squared reserve \(4/625\),
and \(1/\sqrt2<71/100\), with squared reserve \(41/10000\).
Their difference is exactly \(27/20\).

Two touching unit squares have center distance at most \(\sqrt2\).
For their actual minor center angle gamma, the cosine law and (3)
give, allowing unequal center radii,
\[
\begin{split}
 \cos\gamma
 &=1-\frac{|c_1-c_2|^2-(|c_1|-|c_2|)^2}{2|c_1||c_2|}\\
 &>1-\frac1{(27/20)^2}=\frac{329}{729}.
\end{split}
\tag{4}
\]
In particular
\[
 \gamma<\frac{111}{100}.
\tag{5}
\]
For an exact elementary verification, Taylor's theorem on
\(0\le x\le111/100<\pi/2\) gives
\(\cos x\le1-x^2/2+x^4/24\): take the order-five Taylor
polynomial at zero and use the nonpositive sixth derivative.
At the stated endpoint,
\[
 \frac{329}{729}
 -\left(1-\frac{(111/100)^2}{2}
             +\frac{(111/100)^4}{24}\right)
 =\frac{2391249037}{583200000000}>0.
\tag{6}
\]
Cosine is strictly decreasing on this angular interval, so (4)
implies (5). This one exact comparison bounds the full angle
continuum; no angle samples are used.

## 2. Original path order and both endpoint corner cones

CIRCLE_CONTACT_ANGULAR_ORDER.md gives the actual consecutive
circular order of a touching boundary pair. At the middle M,
its two distinct boundary neighbors occupy opposite neighboring
positions in that order. Thus both steps of B--M--C traverse
the center circle in the same direction. Reflect the description
if necessary and choose center-angle lifts
\[
 \alpha_B<\alpha_M<\alpha_C,\qquad
 \alpha_C-\alpha_B<\frac{111}{50}.
\tag{7}
\]
No other physical boundary body is inserted into either touching
minor arc.

Section 1 of FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md proves that
every physical circle corner, and every nonzero nonnegative circle
resultant, differs from its own center direction by strictly less
than \(\pi/12\). Its hypothesis \(R^2>2+\sqrt3\) follows from (1).
The body intervals are disjoint because distinct boundary centers
have separation greater than \(2\pi/9>\pi/6\).
Hence the endpoint resultant lifts preserve the actual order in
(7), and
\[
 0<\beta_C-\beta_B
 <\frac{111}{50}+\frac{\pi}{6}
 <\frac{111}{50}+\frac{11}{21}
 =\frac{2881}{1050}
 <\frac{11}{4}.
\tag{8}
\]
The last rational reserve is \(13/2100\), using the classical
strict bound \(\pi<22/7\). The right side is less than pi,
so there is no complementary-arc ambiguity.

The two-corner endpoint intervals retain all physical circle
corners and every independent nonnegative weight split. This
proves the theorem with no force equation, concurrence, selected
contact owner, shared mean, or degree restriction.

## 3. Scope

The conclusion is available for an actual physical boundary
three-path inside any larger graph, even if its contacts have
zero selected stress. Other physical units remain fixed. It is
an angular necessary condition, not by itself a packing-capacity
or original-gate exclusion. Its high-radius premise (1) must be
established in any application; it is not asserted over the
entire earlier lower-radius window without that additional step.
