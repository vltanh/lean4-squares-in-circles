# Small cyclic stress components and parallel transmission paths

**Status:** independently reviewed exact conditional reductions for the
remaining positive components, including the angular consequences. These results do
not exclude every cyclic component and do not close the unrestricted n=10
lower bound.

Use the physical stress certificate and positive body-pair graph of
[PHYSICAL_TREE_REDUCTIONS.md](PHYSICAL_TREE_REDUCTIONS.md). A body is
**loaded** if it has positive circle load. All references to degree and
components concern the positive graph, not the full geometric contact graph.
We work in the window

\[
                         79/40\le R\le3/\sqrt2.             \tag{1}
\]

The imported n=8 justification of this lower window, including its exact
source and remaining arithmetic dependency, is recorded in
[EXPANDED_TREE_INVENTORY.md](EXPANDED_TREE_INVENTORY.md). The conclusions
below are hand deductions within (1). The earlier inventory already excludes
all tree components for a ten-square packing.

For signs in this manuscript, contact forces point into their receiving
body. A contact with outward unit normal n on body i applies the force
`-mu n` to i and `+mu n` to the other body j, where mu>0. Circle forces
point toward the origin. Each body balances force and torque.

## 1. An unloaded set needs at least two outside neighbors

Let U be a nonempty set of unloaded bodies in a nonzero positive component.
Its outside neighbors cannot consist of just one body H. They cannot be
empty either.

For the one-neighbor assertion, dot the force equation of each i in U with
`c_i-c_H` and sum. At an internal contact i--j, choose n from i toward j.
The two contributions sum to

\[
 \mu n\mathbin\cdot(c_j-c_i)
       =\mu\bigl(h_i(n)+h_j(n)\bigr)>0,                    \tag{2}
\]

where h denotes a square's directional halfwidth. At a boundary contact
i--H the contribution is the same positive expression. There are no circle
terms because U is unloaded. The resulting strictly positive sum contradicts
the sum of the zero force equations. For an empty outside-neighbor set, use
any fixed reference point instead of c_H; the internal terms give the same
contradiction. A nonzero component supplies at least one positive term.

Consequently every connected component of `G-H` contains a loaded body.
In particular, a leaf block of the block-cut decomposition has a loaded body
other than its articulation vertex. This applies also when the unloaded
subgraph itself contains cycles.

## 2. Transmission paths realize the distance between their endpoints

Consider a path from H to L whose internal bodies are unloaded and have
degree two in the full positive graph. At each internal body, opposite
equal forces and torque balance give a side transmitter of width 1 or a
diagonal transmitter of width sqrt(2). The force magnitudes agree along
the path, and all application points lie on one line. Orient its unit
direction d from H toward L. If p_H and p_L are its endpoint contacts, then

\[
                   p_L-p_H=W d,\qquad
                   W=\sum\hbox{ internal widths}.          \tag{3}
\]

The endpoint squares lie on the corresponding sides of their support lines:

\[
 d\cdot x\le d\cdot p_H\quad(x\in H),\qquad
 d\cdot y\ge d\cdot p_L\quad(y\in L).
\]

Thus `|y-x|>=d dot(y-x)>=W`, with equality at the displayed contacts.
In particular

\[
                         \operatorname{dist}(H,L)=W.        \tag{4}
\]

For two fixed convex sets, the displacement vector of a closest pair is
unique: if two distinct minimizing displacement vectors existed, their
average would still be a displacement between points of the sets, and
strict convexity of squared norm would make it shorter. Therefore every
nonempty unloaded transmission path between the same H,L has the same
W and the same direction d.

Two immediate consequences are useful.

* The endpoints of a nonempty transmission path cannot touch at all.
  In particular an unloaded degree-two body cannot lie in a contact triangle.
* In a leaf triangle block, both non-articulation vertices are loaded:
  they have degree two in the full graph, and an unloaded one would violate
  the preceding consequence.

Coincident transmission lines are not excluded by this argument. A side
transmitter can have its force line along one of its other sides. Two
physical paths may therefore share a boundary line. The argument below
allows this case.

The universal center bound

\[
             |c|\le(\sqrt{17}-1)/2<25/16
\]

implies, by projecting the two endpoint centers, `1+W<25/8`. Hence

\[
                   W\in\{1,\sqrt2,2\}                    \tag{5}
\]

for a nonempty path. Width 2 means exactly two side transmitters.

## 3. Two-terminal cyclic components are impossible for ten squares

Suppose a whole positive component is the union of at least two internally
vertex-disjoint paths from H to L, all internal bodies being unloaded and
degree two. There are no other positive edges or bodies in this component.
This includes a simple-cycle component with exactly two loaded bodies.

A direct H--L edge is impossible by Section 2 if any other path is nonempty.
All paths are therefore nonempty. By (3)--(4), their forces have a common
direction and their widths agree. Every force at H points in the same
direction, and likewise at L, so both endpoints must be loaded.

Aggregate the parallel forces at H using their positive path weights. The
weighted effective point lies on H's support face. Do the same at L with
the same weights. The effective points still differ by Wd. The circle
loads have zero torque about the origin, so the effective contact line at
each endpoint is radial. The ordinary loaded-leaf argument consequently
applies even though there are several physical paths: each endpoint is
either a radial side-normal S body or a radial diagonal D body.

Write

\[
 A=\sqrt{R^2-1/4}-1,\qquad B=R-\sqrt2.
\]

Their inward support radii are A and B respectively. The two endpoints lie
on opposite rays and

\[
                      W=a_X+a_Y,\qquad a_S=A,\quad a_D=B.  \tag{6}
\]

The radius window gives

\[
 A>9/10,\quad B>11/20,\quad
 A\le\sqrt{17}/2-1,\quad B\le1/\sqrt2.
\]

Here `B>11/20` follows from `sqrt(2)<57/40`, and the lower bound on A
follows by squaring. Apply (5) to (6).

* **S--D:** `A+B>29/20>sqrt(2)` and
  `A+B<2`. No allowed width remains.
* **D--D:** `1<2B<=sqrt(2)`, so W=sqrt(2) and R=3/sqrt(2).
  Each path consists of a single diagonal transmitter. The two D endpoints
  have unique inward support vertices, so all paths use the same two
  endpoint contacts. The diagonal transmitter between them has a unique
  center and square orientation. Distinct paths would therefore use
  identical unit squares, which is impossible.
* **S--S:** `sqrt(2)<2A<1+sqrt(2)` forces W=2 and R²=17/4.
  Either path gives exactly the four-square S--S chain: centers
  `(-3/2,0),(-1/2,t_1),(1/2,t_2),(3/2,0)` with `|t_i|<=1/2`, after rotation.
  The arbitrary-orientation completion theorem in
  [WIDE_NECK_THREE_POINT_STABBING.md](WIDE_NECK_THREE_POINT_STABBING.md)
  bounds the entire packing by nine squares.

Every case is excluded for a ten-square packing. A simple-cycle component
with only one loaded body is already excluded by Section 1, by deleting
that body; zero loaded bodies are impossible by the same force sum.
Thus every simple-cycle component has at least three loaded bodies.

## 4. Loaded contact angles and an open-semicircle obstruction

Define

\[
 \alpha=2\arcsin\!\left(\frac1{\sqrt2R-1}\right),\qquad
 \beta=\arcsin\!\left(\frac1{2R}\right).                    \tag{7}
\]

A loaded square has center norm at least `R-1/sqrt(2)`. If two loaded
squares touch, their center distance is at most sqrt(2). If delta is the
minor angle between their center rays, then

\[
 |c_i-c_j|^2
   =(|c_i|-|c_j|)^2+4|c_i||c_j|\sin^2(\delta/2)
   \ge4(R-1/\sqrt2)^2\sin^2(\delta/2).
\]

Consequently delta<=alpha.

Every circle vertex of a loaded square lies within beta of the center ray.
To see this, reflect its own axes so the center coordinates are a,b>=0.
A farthest vertex is `(a+1/2,b+1/2)`, with the evident other sign choices
when a or b is zero. If r is the center norm and epsilon is the angle
between this vertex and the center, then

\[
              |\sin\epsilon|=\frac{|a-b|}{2Rr}
                         \le\frac1{2R}.                   \tag{8}
\]

The dot product is positive, so `|epsilon|<pi/2` and (8) proves the claim.
Every circle vertex is farthest because all vertices are contained in the
radius-R disk.

The constants in (7) satisfy the strict bounds

\[
                   \alpha<2\pi/5,\qquad
                   \alpha+\beta<\pi/2.                   \tag{9}
\]

Here is a rational check. Since `sqrt(2)>24/17` and R>=79/40,

\[
 \sin(\alpha/2)<85/152<9/16,\qquad
 \cos\alpha>47/128>20/79\ge\sin\beta.
\]

Also `cos(2pi/5)=(sqrt(5)-1)/4<5/16<47/128`, using sqrt(5)<9/4.
These inequalities establish both assertions of (9).

If one loaded body touches every other loaded body in its positive
component, all circle-load directions in the component lie within
`alpha+beta<pi/2` of that body's center ray. They therefore lie in one
open semicircle. Summing the component's body force equations cancels all internal
contact forces, whereas a positive sum of vectors in an open semicircle
cannot vanish. This is a contradiction.

This statement concerns all loaded bodies of the component. A loaded
contact star inside a larger component does not suffice if other loads
lie outside the star.

## 5. Consequences for short cycles

First suppose a simple-cycle component is entirely loaded and has m<=5
bodies. Give every successive contact its principal signed center-angle
increment. Its magnitude is at most alpha. The sum is an integer multiple
of 2pi, and its absolute value is less than `m(2pi/5)<=2pi`; hence it is
zero. The center angles therefore have a consistent real lift around
the cycle.

For any two vertices, either arc of the cycle bounds their lifted-angle
difference. The shorter arc has at most floor(m/2) edges, so the full
range of lifted angles is at most `floor(m/2)alpha<=2alpha`. By (8),
all circle loads fit in an interval of length at most
`2alpha+2beta<pi`. This again contradicts their zero sum.

In fact an **entirely loaded positive component with at most five bodies**
is impossible even if it has extra edges. Every bridge has an unloaded
endpoint by the central bridge-cover theorem, so an entirely loaded
component has no bridge. It also has no isolated vertex: a single body's
circle loads can balance only if the origin lies in the convex hull of
its loaded vertices, hence in the square, contradicting R>sqrt(2).
Its minimum degree is consequently at least two. On at most five vertices
its graph diameter is at most two: vertices at distance at least three
would have disjoint closed neighborhoods, each containing at least three
vertices.

Every simple cycle has length at most five, so the winding calculation
above makes every cycle's center-angle increment sum zero. Decomposing
closed walks into simple cycles gives a consistent real angle lift on
the whole connected graph. Its diameter-two bound puts the lifted range
within 2alpha, and the same open-semicircle contradiction applies.

Combining the earlier sections gives the following precise inventory for
components whose whole positive graph is a simple cycle.

* A component has at least five bodies and at least three loaded bodies.
* A five-cycle has either three or four loaded bodies.
* In a five-cycle with three loaded bodies, the two unloaded bodies are
  nonadjacent. Otherwise the three loaded bodies are consecutive and their
  middle one touches the other two, contradicting Section 4.

For the first item, cycles with at most two loaded bodies are excluded by
Section 3. An all-loaded cycle of length at most four is excluded above.
The only remaining four-cycle pattern has three loaded bodies, and its
middle loaded body touches the other two, so Section 4 excludes it too.

These are restrictions on selected component types. Components with
branching cyclic blocks, a five-cycle with three or four loaded bodies,
and larger cycles remain to be treated. In particular, this manuscript
does not infer that a torque cycle surrounds the origin, or that every
positive component is a simple cycle.
