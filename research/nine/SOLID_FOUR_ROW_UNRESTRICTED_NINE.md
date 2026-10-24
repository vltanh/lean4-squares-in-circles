# n=9: sharp completion of a solid four-square row, allowing oblique free squares

**Status:** complete hand theorem for this entire explicitly stated
structural class. The other five squares may rotate independently and
may require oblique separating axes. No global coordinate-separability
hypothesis is used.

This is not the unrestricted nine-square theorem: extraction of a solid
row from an arbitrary packing is neither asserted nor proved. The row
hypothesis below includes common height and edge-to-edge contiguity; a
staggered projection chain is not sufficient.

## 1. Statement

Write \(Q=1105/256\). Suppose nine unit squares with pairwise disjoint
open interiors fit a disk centered at zero with squared radius
\(0\le q\le Q\). Suppose four of them, in some orthonormal frame, are
the axis-parallel squares centered at

\[
 (\xi-3/2,t),\quad(\xi-1/2,t),\quad
 (\xi+1/2,t),\quad(\xi+3/2,t).                              \tag{1}
\]

Their union is the solid rectangle
\(B=[\xi-2,\xi+2]\times[t-1/2,t+1/2]\).
There are no assumptions on the orientations or contact pattern of the
other five squares.

**Theorem.** Then \(q=Q\). Up to reflecting the vertical coordinate,
\(\xi=0\), \(t=1/16\), and exactly three of the other squares lie
below the row. These three are axis-parallel with centers

\[
 (-1,-15/16),\quad(0,\gamma),\quad(1,-15/16),
 \qquad
 \frac12-\frac{\sqrt{1041}}{16}\le\gamma\le-15/16.           \tag{2}
\]

The last two squares lie above the row. Their own orientations and
mutual separating axes need not be aligned with the row.

The existing record construction and the exact oblique upper-pair
construction in `NO_GLOBAL_ORTHOGONAL_FRAME.md` demonstrate attainability.

## 2. Every other square is trapped above or below the row

Containment of the farthest rectangle corner gives

\[
             (2+|\xi|)^2+(1/2+|t|)^2\le q\le Q.            \tag{3}
\]

Therefore

\[
                 |t|\le1/16,\qquad |\xi|<1/40.             \tag{4}
\]

For the first bound use \(Q-4=(9/16)^2\). For the second, at
\(|\xi|=1/40\) the left side of (3) is at least

\[
                   (81/40)^2+1/4=6961/1600>Q.
\]

Every independently oriented unit square with center \(c\) in the disk
has its farthest vertex at squared radius

\[
 \|c\|^2+\frac12+|c\cdot u|+|c\cdot v|
       \ge\|c\|^2+\|c\|+\frac12.
\]

Since \((61/40)^2+61/40+1/2=6961/1600>Q\), all nine centers obey

\[
                          \|c\|<61/40.                    \tag{5}
\]

Let \(T\) be one of the remaining five squares, with center \((x,y)\).
Its center is horizontally inside the rectangle's horizontal span:
(4)–(5) imply

\[
            \xi-2<-79/40<x<79/40<\xi+2.
\]

The open inscribed disk of radius \(1/2\) in \(T\) cannot intersect
\(\operatorname{int}B\). Indeed, any nonempty open intersection with
\(\operatorname{int}B\) contains a point in one of the four individual
row-square interiors; the three internal seams cannot fill an open set.
Since its center lies horizontally inside \(B\), the disk's distance
from \(B\) is its vertical clearance. Thus

\[
                   |y-t|\ge1,
             \quad |y|\ge15/16.                            \tag{6}
\]

Combining (5)–(6) shows \(|x|<49/40\), because

\[
 (49/40)^2+(15/16)^2-(61/40)^2=69/1280>0.                   \tag{7}
\]

A unit square's coordinate halfwidth is at most \(\sqrt2/2<3/4\).
Hence **every point** of \(T\) has horizontal coordinate of magnitude
strictly less than

\[
                         49/40+3/4=79/40.                   \tag{8}
\]

The entire square is horizontally inside the solid row's span; it
cannot pass around either end. A closed point of \(T\) cannot lie in
\(\operatorname{int}B\): otherwise nearby points of \(\operatorname{int}T\)
would also lie there. By convexity, its vertical projection is an
interval. Equations (6)–(8) now force exactly one of

\[
                      T\subset\{y\ge t+1/2\},
       \qquad\text{or}\qquad T\subset\{y\le t-1/2\}.       \tag{9}
\]

This is a **derived** whole-square separation, not a common-axis
assumption about other-square pairs. Those pairs may be obliquely
separated.

## 3. Five completions force a sharp cap

Among five squares assigned to the two sides in (9), at least three
lie on one side. Reflect vertically if necessary to place at least
three below the row. Their reflected copies are contained in

\[
                         D_Q\cap\{y\ge1/2-t\}.
\]

By (4), \(1/2-t\ge7/16\). Apply the arbitrary-orientation three-square
cap theorem in `UNRESTRICTED_THREE_SQUARE_CAP.md`.
It forces \(q=Q\), the three cap squares to be aligned, and the two
outer ones to have bottom height exactly \(7/16\) in the reflected
coordinates. They cannot all be contained above a strictly higher
floor. Therefore

\[
                        1/2-t=7/16,
             \qquad t=1/16.                                \tag{10}
\]

Substituting (10) into (3), with \(q=Q=4+(9/16)^2\), yields
\(\xi=0\). The cap equality gives exactly (2).
The cap theorem also rules out four squares below the row, so precisely
three are below and the other two are above. This proves the theorem.

## 4. A wider seven-square terminal: remove the short row's projection hypothesis

The same cap theorem improves the old four-over-three terminal.
Suppose four independently rotated squares have pairwise disjoint
horizontal open projections and lie entirely above \(y=\sigma\).
Suppose three other physically interior-disjoint squares lie entirely
below \(y=\sigma\), with **no projection-order assumption on these three**.
Assume all seven fit \(D_q\), \(q\le Q\).

Then \(q=Q\), \(\sigma=-7/16\), and both groups align with the frame
and have the seven-anchor boundary coordinates.

*Proof.* If \(\sigma\le-7/16\), reflect the lower three squares and
apply the new cap theorem. It forces \(q=Q\) and their two extremal
corners to be at the exact cap floor; thus \(\sigma=-7/16\).
If \(\sigma>-7/16\), choose a floor
\(s_0=\min(\sigma,1/2)>-7/16\) for the upper four squares.
The previously proved projection-separated cap-row inequality
in `ORIENTATION_STABLE_SEVEN_ANCHOR.md` applies, since
\(0<s_0+1\le3/2<2\), and gives

\[
                       q\ge4+(s_0+1)^2>Q,
\]

a contradiction. At the only possible seam, equality in the old
four-square cap-row theorem and the new three-square cap theorem
supplies alignment and all outer anchor positions. QED.

This is a whole structural class allowing arbitrary oblique separators
among the three initially unordered squares. It still requires a
common seam between the two groups, and does not establish that every
nine-square packing has one.

## 5. Logical boundary

Closed by these arguments:

- all arbitrary-orientation completions of a **solid**, four-square
  axis-aligned row at or below the candidate radius;
- the seven-square seam terminal with a projection-separated four-group
  and a completely unrestricted physically disjoint three-group;
- the relevant equality outer anchors and the oblique freedom of the
  other two squares in the solid-row case.

Still open: extracting these hypotheses, or another sharp terminal,
from every unrestricted nine-square packing or physical minimizing
stress network. A four-projection chain with staggered center heights
is not a solid row. This document may not be invoked for that broader
class without an additional argument.

Imported to the draft GitHub research branch on 2026-10-23. No Lean build, CI run or independent end-to-end mathematical audit is claimed for this hand derivation.