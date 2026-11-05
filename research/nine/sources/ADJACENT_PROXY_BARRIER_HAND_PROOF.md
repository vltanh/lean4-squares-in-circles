# A whole-square barrier above two adjacent inner squares

November 2, 2026. Hand proof. This is a physical geometric lemma; it does
not assume coordinate separation between the outsider and either main
square. No mathematical program, sampled angles, Lean, Lake, or CI is used.

## 1. Exact statement

Let two axis-aligned closed squares have centers
\((x_1,y_1),(x_2,y_2)\), halfwidths \(g_1,g_2\), and

\[
 \frac14\le g_i\le\frac12,\qquad
 D=x_2-x_1\ge1,\qquad
 0\le G=D-g_1-g_2\le\frac14.
 \tag{1}
\]

Let a physical unit square F have center \((X,Y)\), arbitrary orientation,
and interior disjoint from both squares. Suppose

\[
 x_1\le X\le x_2,\qquad Y>\max(y_1,y_2).
 \tag{2}
\]

Write \(h_F\) for its vertical projection halfwidth. Then its **whole
lower edge** satisfies

\[
 Y-h_F\ \ge\ \min(y_1+g_1,y_2+g_2)-\frac G2.
 \tag{3}
\]

The two main heights can be unequal. In particular, no overlap between
their vertical projections is assumed. Reflection gives the corresponding
upper-edge bound for a unit below both main centers.

## 2. Two elementary section facts

First consider F and one of the aligned squares. If

\[
 |X-x_i|<g_i+\frac12,
 \tag{4}
\]

their horizontal chords through their respective centers have a common
interior x-coordinate. Indeed F contains its centered radius-1/2 disk.
On the vertical line at that coordinate, the two nondegenerate vertical
sections contain their respective center heights in their interiors.
Since \(Y>y_i\), the F section is above the other section.

This vertical order persists across their entire common horizontal
projection. On its interior both sections are nondegenerate, and their
continuous boundary functions cannot exchange vertical order without
overlap of interiors. Consequently, for every common interior x-coordinate,
the lower boundary of F is at least \(y_i+g_i\). The same holds at
projection endpoints by continuity. We call index i **active** when (4)
holds. This word refers only to the present proof.

Second, put

\[
 a\ge b\ge0,\qquad a^2+b^2=1,\qquad
 h=\frac{a+b}{2},\qquad k=\frac{a-b}{2}.
\]

These are the absolute side-axis components, halfheight, and horizontal
offset of a bottom vertex of F. For b>0, a bottom vertex has x-coordinate
\(x_0=X-k\) or \(x_0=X+k\). At height d above this vertex, for
\(0<d\le h\), the bottom-left case \(x_0=X-k\) has section endpoints

\[
 L(d)=x_0-\frac ba d,
 \qquad
 R(d)=x_0+\min\left\{\frac ab d,\frac{1-bd}{a}\right\}.
 \tag{5}
\]

The other case is its horizontal reflection. Thus the section length is

\[
 \ell(d)=
 \begin{cases}
 d/(ab),&0<d\le b,\\
 1/a,&b\le d\le h,
 \end{cases}
 \qquad
 \ell(d)\ge\min(2d,1).
 \tag{6}
\]

For b=0 every nonextreme horizontal section has length one. In the
bottom-left case, \(R(d)>X\) whenever \(b\le d\le h\); this follows
directly from (5), whose second expression at d=h is
\(X+1/(2a)>X\). The reflected statement is \(L(d)<X\) in the
bottom-right case for the same range.

We will also use

\[
 k\ge\frac14\quad\Longrightarrow\quad \frac ba<\frac12.
 \tag{7}
\]

For if b/a were at least 1/2, then
\(a-b=(1-b/a)/\sqrt{1+(b/a)^2}\le1/\sqrt5<1/2\), contrary to
\(a-b=2k\ge1/2\).

## 3. The center is above the lower top level

Set

\[
 B=\min(y_1+g_1,y_2+g_2),\qquad f=Y-h.
\]

In fact Y>B. Otherwise the horizontal chord of F through its center has
length at least one and contains X between x1 and x2. The gap between the
two main horizontal projections has length G<1. This chord therefore
meets the interior of at least one main horizontal projection.
The height Y is strictly above both main center heights, by (2), and
at most both main top heights. Thus this intersection gives an overlap
of interiors; even if Y is a main top height, F has an open neighborhood
below its interior center chord. This is a contradiction.

At least one index is active. If neither were, then (2) would give

\[
 X-x_1\ge g_1+\frac12,\qquad
 x_2-X\ge g_2+\frac12,
\]

so G>=1, contradicting (1).

Suppose now, contrary to (3), that f<B-G/2. Choose a horizontal height t
with

\[
 f+\frac G2<t<B<Y,
 \qquad d=t-f>\frac G2.
 \tag{8}
\]

The section of F at t is nondegenerate, and 0<d<h. By Section 2 it avoids
the open horizontal projection of every active main square, since
t<B<=y_i+g_i. We will show that this is impossible.

## 4. Both main indices active

If both are active, the section interval lies wholly in one of the three
components of the complement of their open horizontal projections:

\[
 (-\infty,x_1-g_1],\quad
 [x_1+g_1,x_2-g_2],\quad
 [x_2+g_2,\infty).
 \tag{9}
\]

If it lies in the middle gap, (6) and G<1 give \(2d\le G\), contrary
to (8).

Suppose it lies in the left component. The aligned case b=0 is impossible:
its right endpoint is X+1/2>x1-g1. For b>0 the bottom-right orientation
is also impossible, because its right endpoint is at least
\(x_0=X+k\ge x_1>x_1-g_1\). In the bottom-left orientation, d>=b
would imply R(d)>X>=x1. Hence d<b, and (5) gives

\[
 d\le (x_1-g_1-X+k)\frac ba
    \le(k-g_1)\frac ba.
 \tag{10}
\]

Positivity of d forces k>g1>=1/4, so (7) applies. Also

\[
 \frac12-g_1\le G,
\]

because D>=1 and g2<=1/2. Consequently (10) gives

\[
 d\le\frac{1/2-g_1}{2}\le\frac G2,
\]

again a contradiction. The right component follows by reflection.

## 5. Exactly one index active

Suppose only index 1 is active. The other condition fails, so

\[
 X\le x_2-g_2-\frac12=x_1+g_1+G-\frac12.
 \tag{11}
\]

The section at t avoids the first main projection, and hence lies wholly
to its left or to its right. The left possibility is excluded by exactly
the outer-component argument (10), which did not use activity of index 2.

Suppose it lies to the right, so its left endpoint is at least x1+g1.
If b=0, that endpoint is X-1/2, which is less than x1+g1 by (11).
In the bottom-left orientation, (5) likewise gives

\[
 L(d)\le X-k\le x_1+g_1+G-\frac12<x_1+g_1.
\]

Thus the orientation is bottom-right. If d>=b, its left endpoint is at
most X-1/(2a), again below x1+g1 by (11). Therefore d<b, and the reflected
first expression in (5) gives

\[
 d\le (X+k-x_1-g_1)\frac ba
    \le\left(G-\frac12+k\right)\frac ba.
 \tag{12}
\]

Since d>0, this implies k>1/2-G>=1/4. Equation (7) applies, while
\(G-1/2+k\le G\). Thus (12) gives d<=G/2, contradicting (8).
The case in which only index 2 is active is the horizontal reflection.

All cases contradict (8), proving the whole-square barrier (3).

## 6. Specialization to the central pair of an actual four-chain

Let

\[
 M_0<_xM_1<_xM_2<_xM_3
\]

be an actual horizontal four-chain in the closed disk with squared radius
Q=1105/256. Put h_i=1/2+e_i and g_i=1/(4h_i), and write the actual
successive projection gaps as

\[
 \delta_i=x_{i+1}-x_i-h_i-h_{i+1}\ge0.
\]

The universal center bound |c_i|<91/60 gives

\[
 e_0+2e_1+2e_2+e_3+\delta_0+\delta_1+\delta_2<\frac1{30}.
 \tag{13}
\]

Since

\[
 \frac12-g_i=\frac{e_i}{2h_i}\le e_i,
\]

the horizontal gap between the two central inscribed aligned squares is

\[
 G_{12}=x_2-x_1-g_1-g_2
       =\delta_1+(h_1-g_1)+(h_2-g_2)
       \le\delta_1+2e_1+2e_2<\frac1{30}.
 \tag{14}
\]

Both halfwidths are in [1/4,1/2], and x2-x1>=1. Hence every physical
outsider with x1<=X<=x2 and Y>max(y1,y2) obeys

\[
 Y-h_F\ge\min(y_1+g_1,y_2+g_2)-\frac{G_{12}}2
          >\min(y_1,y_2)+\frac{869}{1860}.
 \tag{15}
\]

Here g1,g2>15/31 follows from h1,h2<31/60, and
15/31-1/60=869/1860. For the outer adjacent pairs the safe gap bound is
G01,G23<1/15, not the stronger central-pair bound (14).

For example, if min(y1,y2)>=-221/7440, every such outsider lies wholly
above y=7/16. Three such outsiders would therefore meet the sharp
three-square half-plane terminal. This is a derived caller, not a claim
that every actual-four configuration satisfies that main-height condition.

The reflected form of (15) holds below both inner main centers. This
lemma alone does not close the remaining joint five-outsider geometry or
the unrestricted nine-square theorem.
