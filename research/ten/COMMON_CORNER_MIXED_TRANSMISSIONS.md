# The remaining common-corner side/diagonal pair

**Status:** independently reviewed exact conditional hand proof. In
combination with
[COMMON_CORNER_SIDE_TRANSMISSIONS.md](COMMON_CORNER_SIDE_TRANSMISSIONS.md),
this excludes every coincident-contact case at C in the three-loaded
five-cycle. Distinct contacts on C remain open.

Consider an entire positive component

\[
                         A-U-C-V-B-A
\]

with precisely A,B,C loaded, where U is a side transmitter, V a diagonal
transmitter, and their two contacts on C coincide. Work in
\(79/40\le R\le3/\sqrt2\), and set

\[
                  b=R-\sqrt2,\qquad k=b/\sqrt2.
                                                               \tag{1}
\]

## 1. The strict normal choice and its side-contact exception

We use the selected physical certificate from
[PHYSICAL_TREE_REDUCTIONS.md](PHYSICAL_TREE_REDUCTIONS.md), including its
strict normal selection at point-only vertex/vertex contacts. The precise
source is Section 2.2 of
[PHYSICAL_CONTACT_STRESS.md at commit 901678d95a5197017db81343c7d0182661cc92fc](https://github.com/vltanh/lean4-squares-in-circles/blob/901678d95a5197017db81343c7d0182661cc92fc/research/nine/PHYSICAL_CONTACT_STRESS.md).
It chooses a normal exposing the contact vertex uniquely in both squares,
in the interiors of both appropriate normal cones, and fixes it in a
neighborhood. Thus at a point-only vertex/vertex contact the selected
positive normal cannot be a side normal of either incident square.
Positive-length side contacts use the separate endpoint-constraint branch;
their endpoint force applications remain allowed.

The aggregate-contact reduction in
[COMMON_CORNER_SIDE_TRANSMISSIONS.md](COMMON_CORNER_SIDE_TRANSMISSIONS.md)
applies. A common contact in the relative interior of a C side gives
parallel directions, excluded by
[PARALLEL_MIXED_FIVE_CYCLE.md](PARALLEL_MIXED_FIVE_CYCLE.md).
For a common vertex, C is radial diagonal type. Rotate so its inward
corner is P=(−b,0) and its outward normal cone there has angles
[−pi/4,pi/4]. Reflect if necessary so U transmits at angle theta>=0 and
V at angle −eta<=0. Force balance on C puts the two outgoing directions
on these opposite sides, with theta,eta<=pi/4.

The point P cannot lie in the relative interior of a U side. If it did,
U would locally occupy an open half-plane with inward normal n_theta.
The diagonal transmitter's open pi/2 tangent cone is centered at
n_(−eta). Since theta+eta<=pi/2, that cone has an open intersection with
the U half-plane, giving overlapping interiors near P. Hence P is a U
vertex.

If theta<pi/4, the C support point for n_theta is unique, so C and U
intersect only at P. But n_theta is a side normal of U, contrary to the
strict normal convention above. Therefore

\[
                             \theta=\pi/4.                 \tag{2}
\]

At this boundary direction, C and U must share a positive-length side
segment: a point-only contact would be forbidden for the same reason.
Their incident sides have unit length and share the endpoint P, so they
coincide along that whole side. This fixes the placement of U.

Its other force application is Q=P+n_(pi/4). This is a vertex of U. The
endpoint square A must be parallel to U. Indeed, if A has side support
at Q, its side normal is n_(pi/4), fixing its frame. If A has vertex
support and the intersection is a segment, the shared side again fixes
that frame. The remaining point-only vertex/vertex alternative is
forbidden because the positive normal is a side normal of U.

## 2. The loaded endpoint has an exact height

Use the orthonormal coordinate frame

\[
                 e_1=(1,1)/\sqrt2,\qquad
                 e_2=(-1,1)/\sqrt2.
\]

In this frame the three parallel squares have centers

\[
 C=(-k-1/2,k+1/2),\qquad
 U=(1/2-k,k+1/2),\qquad
 A=(3/2-k,k+\tau),                                         \tag{3}
\]

where \(-1/2\le\tau\le1/2\). The last interval follows because Q,
whose new coordinates are (1−k,k), belongs to A's left face.

The radius bounds give k<=1/2 and, using sqrt(2)<99/70,

\[
 k=\frac{R}{\sqrt2}-1
 >\frac{157}{396}>\frac{41}{104}>\frac3{10}.                \tag{4}
\]

A's first center coordinate is positive. If its second coordinate were
nonpositive, then \(-1/2\le\tau\le-k\), and its maximum squared
vertex norm would be at most

\[
                     (2-k)^2+(1-k)^2.
\]

This is strictly below R²=2(1+k)², since the difference is 10k−3>0.
That would contradict loading. Thus k+tau>0, and A's farthest vertex
has coordinates (2−k,k+tau+1/2). Loading gives

\[
 (2-k)^2+(k+\tau+1/2)^2=2(1+k)^2,
\]

and hence

\[
                   \tau=\sqrt{k^2+8k-2}-k-1/2.
                                                               \tag{5}
\]

Since k>41/104,

\[
       k^2+8k-2-(k+3/4)^2=\frac{13}{2}k-\frac{41}{16}>0.
\]

Consequently tau>1/4. Every point of A therefore has second coordinate

\[
                              y>k-1/4.                     \tag{6}
\]

## 3. The diagonal endpoint lies below that height

Write c=cos(eta), s=sin(eta). In the new frame, the diagonal
transmission direction is

\[
          n=(d,-e),\qquad
          d=(c-s)/\sqrt2,\quad e=(c+s)/\sqrt2,
          \qquad 0\le d\le e.
\]

Its far contact on B is P+sqrt(2)n, which has new coordinates

\[
                         Q_B=(-k+c-s,k-c-s).               \tag{7}
\]

A unit square supported at a point with inward normal (d,−e), where
0<=d<=e, can rise at most d above that point. For vertex support, at most
one of its two incident edges points upward, and that edge's vertical
component is at most d. The other edge has nonpositive vertical component.
For side support, the tangent's absolute vertical component is d and
translation in the inward normal direction lowers height. These arguments
also include endpoint and horizontal-edge cases.

Apply this bound to B at Q_B. Every point of B satisfies

\[
 \begin{aligned}
 y&\le k-c-s+\frac{c-s}{\sqrt2}\\
  &=k-\left(1-\frac1{\sqrt2}\right)c
       -\left(1+\frac1{\sqrt2}\right)s\\
  &\le k-1+\frac1{\sqrt2}
   <k-1/4.                                                \tag{8}
 \end{aligned}
\]

For the penultimate inequality, the subtracted expression increases on
\(0\le\eta\le\pi/4\): its derivative is
\(-(1-1/\sqrt2)s+(1+1/\sqrt2)c>0\). The final inequality uses
\(1/\sqrt2<3/4\).

The strict height bounds (6) and (8) separate A and B. They cannot touch,
contradicting the positive edge A--B. This excludes the mixed side/diagonal
case, including the genuine side-contact boundary exception to strict
normal selection.

Together with the equal-type exclusions, the two transmission contacts
on C must be distinct in any remaining three-loaded five-cycle component.
