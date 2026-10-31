# A radius-two side channel of height greater than one quarter has exterior capacity at most two

Date: October 26, 2026.

**Status: complete hand whole-pocket theorem, accepted after root and separate
independent full-source and physical-scope reviews in REVIEW_RADIUS_TWO_CHANNEL_CAPACITY_TWO_ROOT_2026_10_26.md
and REVIEW_RADIUS_TWO_SIDE_CHANNEL_CAPACITY_TWO_C6_2026_10_26.md.**
It has no force-ratio,
orientation-box or computational-certificate premise.

Work in the original radius range \(79/40\le R\le2\), where the
entire original selected positive component is a simple cycle having
at least three loaded bodies.
Let X,Y be consecutive loaded boundary squares joined by one actual
unloaded degree-two side-normal transmitter of reserve one. Keep
both original endpoint circle masks, every individual nonnegative
circle weight, their positive totals, all original application means,
the original transmitter slider, and every other physical square.

Assume that the actual outward channel height is
\[
                              H>1/4.
\tag{1}
\]

**Theorem.** The entire actual exterior X-transmitter-Y pocket
contains at most two additional unit squares, of arbitrary independent
orientations and with any individual circle weights.

The original masks may be physically unique or radial. This theorem
requires the actual width-one channel and the physical pocket routing;
it does not assign degree-two equations to any higher-degree body.

## 1. A uniform bound on the actual outward center gap

Use the channel-cap frame
\[
 P_X=(l,H),\quad P_Y=(l+1,H),\qquad
 X\subseteq\{x\le l\},\quad Y\subseteq\{x\ge l+1\}.
\tag{2}
\]
The unchanged physical endpoint theorem gives center angles
\[
        0\le\phi_Y<\pi/2<\phi_X\le\pi,
                  \qquad\gamma=\phi_X-\phi_Y\in(0,\pi].
\tag{3}
\]
This is the actual outward consecutive gap in
SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md, not an arbitrarily selected
minor or complementary arc.

Each actual application is a point of its unit square, hence is
at distance at most \(1/\sqrt2\) from that square's center. The
actual reserve-one relation therefore gives
\[
                             |C_X-C_Y|\le1+\sqrt2.
\tag{4}
\]
Every physical boundary unit has an actual circle corner, so
\[
 |C_X|,|C_Y|\ge R-1/\sqrt2
     \ge79/40-1/\sqrt2
     >79/40-5/7=353/280>63/50.
\tag{5}
\]
The first strict bound uses \(\sqrt2>7/5\); the last reserve
is \(353/280-63/50=1/1400\).

If \(\gamma\ge5\pi/6\), the cosine law gives
\[
 \begin{split}
 |C_X-C_Y|^2
 &\ge |C_X|^2+|C_Y|^2+\sqrt3|C_X||C_Y|\\
 &>(2+\sqrt3)(63/50)^2\\
 &>\frac{26}{7}(63/50)^2
       =\frac{35}{6}+\frac{119}{1875}
       >\frac{35}{6}>(1+\sqrt2)^2.
 \end{split}
\tag{6}
\]
Here \(\sqrt3>12/7\) has squared reserve \(3/49\), and
\(\sqrt2<17/12\) gives \((1+\sqrt2)^2<35/6\).
This contradicts (4). Thus the actual gap always satisfies
\[
                              \gamma<5\pi/6.
\tag{7}
\]

## 2. All pocket extras use one free inner-circle interval

Put \(\rho=5/4\). The channel-cap theorem places every whole
extra E of this actual pocket in \(D_R\cap\{y\ge H\}\).
By (1) and the strengthened
RADIUS_TWO_CAP_INNER_ARC_QUARTER_TURN.md, the entire intersection
of \(E^\circ\) with \(|p|=\rho\) is a connected open arc
of length greater than \(\pi/4\), containing its radial-center
point. No boundary contact or positive circle weight is required
of the extra.

Both endpoint boundary units meet the inner circle in one connected
closed arc containing their radial-center points in their relative
interiors. The complete closed-intersection formulas of
ANNULAR_CENTER_ARC_AT_23_25.md apply, since their center norms
in (5) exceed \(23/25\). Their radial points lie in the open
endpoint squares and therefore have horizontal coordinates strictly
below l and strictly above \(l+1\), respectively.

The actual occupied crosscut is \(z_X-P_X-P_Y-z_Y\), joined
to its outward outer-circle arc. Its bounded region is the actual
pocket, and its whole boundary lies above H. The middle segment
can meet the upper inner semicircle only at angles between
\(\phi_Y\) and \(\phi_X\), by monotonicity of cosine. Its
other two pieces lie in the closed endpoint squares.

Each endpoint's inner-circle arc, restricted to the upper semicircle,
remains one interval containing its center angle: every point p of
that endpoint square satisfies
\[
                  C\cdot p\ge |C|^2-|C|/\sqrt2>0,
\]
so its full arc lies in the open angular semicircle about its center.
The upper-quadrant center directions in (3) give the stated interval
restriction. Neither endpoint interval passes through the other
center's radial point, which lies inside the other open square.

An inner-circle point of \(E^\circ\) cannot have angle less than
\(\phi_Y\). If it did, the path along the upper inner semicircle
to angle zero would avoid both endpoint intervals and the middle
crosscut segment. It also avoids the outer-circle arc, since
\(R>\rho\). The positive horizontal ray then escapes to infinity
below H, contradicting the bounded pocket label. An angle greater
than \(\phi_X\) is excluded by the corresponding path to
\(\pi\) and the negative horizontal ray. This is the full actual
crosscut argument, not an assumed sector containment for E.

Finally CENTERED_INNER_ARC.md puts each endpoint's entire closed
centered arc of half-width \(\pi/9\) in its open interior. Thus
all pocket-extra arcs lie in the same intervening free interval
\[
                       (\phi_Y+\pi/9,\phi_X-\pi/9).
\tag{8}
\]
If this interval is empty there is no extra. Otherwise its length is
strictly less than
\[
                    5\pi/6-2\pi/9=11\pi/18<3\pi/4.
\tag{9}
\]

Three actual extras with disjoint open interiors would have disjoint
open arcs with combined length strictly greater than \(3\pi/4\),
contradicting (8)--(9). This proves the whole-pocket capacity two.

The physical cap theorem's compact-interior homotopy argument retains
the same routing at shared junctions and every original mean endpoint.
Additional zero-weight contacts may subdivide the pocket but cannot
move any extra's connected interior across the occupied crosscut or
into a different free inner-circle interval. All original physical
squares and weak radial corner-weight endpoints remain.

## 3. Exact consequence for the remaining all-unique one-share C6

The accepted whole-orbit radius bound gives \(R<2\), and
SIX_CYCLE_REMAINING_CHANNEL_2_HEIGHT.md gives \(H_2>1/4\).
Thus this theorem applies to its original actual channel-2 pocket:
\[
                               n_2\le2.
\tag{10}
\]
The empty pocket-1 theorem, central capacity one, and pocket-0
capacity one remain unchanged. Writing the original extra allocation
as \((n_c,n_0,n_2)\), the exact remaining list is therefore
\[
                         (0,1,2),\qquad(1,0,2),\qquad(1,1,1).
\tag{11}
\]
Only the previously retained allocation \((0,0,3)\) is removed
by this new theorem. Repeated pocket-2 occupancy by two extras and
the simultaneous one-central/one-in-each-cap possibility remain.
No unrestricted C6 gate or global nine-square theorem is declared
closed. There is no numerical premise, sign packet, Lean compilation
or CI in this proof.
