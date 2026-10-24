# A selected simple positive cycle has at most eight bodies

**Status: complete hand implication for simple positive body cycles,
pending independent audit.** In the radius window

\[
\frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},
\qquad Q=\frac{1105}{256},                               \tag{1}
\]

a connected positive physical stress component whose aggregated
body-pair graph is a simple cycle has at most eight bodies. The
certificate uses the point-only vertex/vertex convention from
`PHYSICAL_CONTACT_STRESS.md`: such a contact normal strictly exposes
the common vertex in both squares.

The proof includes contact junctions shared by several squares; an
embedding of the body cycle is derived rather than assumed. It uses
the new `CENTERED_INNER_ARC.md` and the existing degree-two physical
transmission lemma. It does **not** settle completion of a smaller
cycle by additional unstressed squares, nor components with branching
or multiple cycles.

It suffices throughout to consider a cycle of order at least nine.
The same geometric argument gives the stated upper bound for every
cycle of order at least five; smaller cycles already satisfy it.

## 1. A small top-cap fact

**Lemma 1.1.** If a unit square \(T\subset D_Q\) lies in
\(y\ge1\) and contains \((x,1)\), then \(|x|<7/10\).

Write its absolute tilt coefficients as \(A\ge B\ge0\),
\(A^2+B^2=1\). Its vertical width is \(A+B\), so

\[
A+B\le R-1<\frac{27}{25}.
\]

Here \(R<52/25\) follows by squaring against \(Q\).
The function \(\sqrt{1-B^2}+B\) increases on
\([0,1/\sqrt2]\). Thus \(B\ge1/10\) would imply

\[
A+B\ge\sqrt{99/100}+1/10
       >\frac{109}{100}>\frac{27}{25},
\]

a contradiction. Consequently

\[
B<\frac1{10},\qquad A>\frac{99}{100}.                  \tag{2}
\]

Suppose \(x\ge7/10\). If \(B>0\), the bottom point is
a vertex, and one of its adjacent vertices has height \(1+A\)
and horizontal displacement of absolute value \(B\). If
\(B=0\), translate the given bottom point upward by one to obtain
a point of the top side. In either case \(T\) contains a point
with coordinates

\[
X>\frac35,\qquad Y>\frac{199}{100}.
\]

Its squared norm exceeds

\[
\frac9{25}+\frac{39601}{10000}
 =\frac{43201}{10000}>\frac{1105}{256},
\]

contrary to containment. Reflection gives the negative case.
\(\square\)

## 2. Opposite cycle edges cannot cross at a four-square junction

**Lemma 2.1.** Suppose four physical squares meet at one point \(p\)
and a selected simple positive cycle uses the two pairs of opposite
squares as positive edges at \(p\). This is impossible in (1).

Four disjoint square interiors at a point each contribute at least a
right angle. Therefore all four have that point as a vertex, their
four right-angle sectors exactly fill the plane, their frames agree,
and their union is an aligned \(2\times2\) block centered at \(p\).
Use that common frame. Its four members are denoted by their quadrant
relative to \(p\).

First consider a circle-clear member in quadrant unit-diagonal
direction \(n\). It has zero circle load and degree two in the
positive graph. One of its contacts is the opposite-quadrant vertex
contact at \(p\), whose selected normal is strictly exposing. The
two-force transmission lemma therefore forces diagonal transmission:
its other contact is the opposite vertex

\[
p+\sqrt2\,n,
\]

and its outward normal there is \(n\). The neighboring square begins
at that support plane and has width at least one in direction \(n\).
Containment of that neighbor gives

\[
n\cdot p+\sqrt2+1\le R,
\qquad n\cdot p\le R-\sqrt2-1<0.                       \tag{3}
\]

The same conclusion applies to any zero-load member, even if it
physically touches the circle.

If both coordinates of \(p\) are nonzero, at most one of the four
block members touches the circle: only one of the block's four outer
corners maximizes the norm. There are then at least three circle-clear
members. But among four diagonal directions in two opposite pairs,
at most two have negative scalar product with \(p\), contradicting
(3). If \(p=0\), all four members are circle-clear since
\(R>\sqrt2\), and (3) again fails.

After reflection and a quarter turn, the sole remaining possibility
is

\[
p=(a,0),\qquad a>0.
\]

Both right members must touch the circle; otherwise at least three
members are circle-clear. Therefore

\[
R^2=(a+1)^2+1,
\qquad
a>\frac7{10},                                          \tag{4}
\]

where the last comparison follows from
\(R^2-1\ge4641/1600>(17/10)^2\).
The left members are circle-clear diagonal transmitters. The right
members cannot have zero circle load, by (3) and their positive
diagonal scalar products with \(p\).

Let \(U=[a,a+1]\times[0,1]\) be the upper-right member. No physical
square outside this four-member block can touch \(U\):

* At a relative interior point of its left or bottom side, the
  neighboring block square already fills the other half-plane.
* The common point \(p\) already contains four square vertices.
* The outer circle corner \((a+1,1)\) cannot belong to another
  square, by the strict inward-sector lemma for a disk boundary point.
* Every remaining point of its top side, including \((a,1)\), is
  a relative interior point of the top side of the full block.
  A square touching there must lie wholly in \(y\ge1\), by convexity
  and local nonoverlap with the block. Lemma 1.1 and (4) exclude this.
* Every remaining point of its right side, including \((a+1,0)\),
  is a relative interior point of the full block's right side. A
  touching square must lie wholly in \(x\ge a+1\); its width at
  least one then puts a point at \(x\ge a+2>R\).

Thus the second positive neighbor of \(U\) is one of its two
adjacent block members. It cannot be the upper-left member: that
circle-clear square already has its opposite-quadrant force pointing
down and right, and a force toward \(U\) points right, so its two
positive forces cannot balance.

It cannot be the lower-right member either. The circle corner of
\(U\) is uniquely \(z=(a+1,1)\). Its opposite-quadrant contact
force is \(-\mu(1,1)/\sqrt2\), because the lower-left member is a
diagonal transmitter, and its force toward the lower-right member
would be \(-\nu e_y\). With its positive circle weight \(\lambda\),
force balance would require

\[
2\lambda(a+1,1)-\frac\mu{\sqrt2}(1,1)-\nu(0,1)=0.
\]

The first coordinate gives \(\mu/\sqrt2=2\lambda(a+1)\),
and the second then gives \(\nu=-2\lambda a<0\), a contradiction.
This proves the lemma. \(\square\)

## 3. The cycle has a noncrossing drawing with its circle corners outside

Draw every positive body-pair edge by the two straight segments from
the incident square centers to its actual application point. Each
segment, except for its contact endpoint, lies in the corresponding
open square. Hence two such drawn edges can meet away from their
body centers only at a shared contact junction.

At a junction, the involved square sectors occur in their geometric
cyclic order, and there are at most four sectors. Work in small
pairwise disjoint disks about the finitely many junctions. These
disks lie strictly inside \(D_R\), because a shared contact point
cannot lie on the containing circle. They can avoid all
center-to-circle-corner segments except at
their incident centers, because a circle corner belongs to only its
own square and no other boundary ray from that center passes through
it.

The incident strands of the body cycle can be separated locally into
noncrossing strands unless two edges join opposite pairs of four
distinct sectors. Indeed, with at most four sectors, crossings of
two chords require four distinct endpoints alternating in the
cyclic order. If a body has both cycle contacts at the same junction,
use two parallel strands in its center-to-junction tube, ordered
according to the two neighboring sectors; they join only at that
body's center. Shared contact-side segments can likewise be separated
by a small local displacement. Since the body graph is a single cycle
of order at least five, its edges at any one junction form a union of
paths rather than a closed local cycle.

Lemma 2.1 excludes precisely the opposite-pair crossing. Consequently
these local replacements give a simple Jordan drawing of the body
cycle. The replacements can be arbitrarily small and can preserve
disjointness from every center-to-circle-corner segment. Therefore
each circle-touching body has a path from its cycle vertex to its
circle corner in the exterior of this Jordan cycle, meeting the cycle
only at that vertex. Those paths are pairwise disjoint. Their order
along the Jordan cycle equals their order on the outer circle.

The outer-circle order is also their **center-direction** order.
To see this without assuming it, put \(\rho=5/4\) and use
`CENTERED_INNER_ARC.md`: the point \(q_i=\rho C_i/|C_i|\)
is in the open square. Connect \(q_i\) to \(C_i\), then to a chosen
circle corner \(z_i\), inside that square. These paths are disjoint
and stay in the closed annulus \(\rho\le |x|\le R\).
In fact \(|C_i|>\rho\), and

\[
z_i\cdot\frac{C_i}{|C_i|}
 =|C_i|+H_i\!\left(\frac{C_i}{|C_i|}\right)>|C_i|,
\]

so the second segment stays strictly outside the inner circle too.
Disjoint arcs joining the two boundary circles of an annulus preserve
cyclic endpoint order (cut the annulus along one arc and apply the
Jordan separation theorem in the resulting rectangle). This proves
the asserted center-direction order.

Thus consecutive circle-touching bodies along the graph cycle are
consecutive in their circular center order, with one of the two
orientations fixed for the entire cycle.

## 4. Every clear transmission body consumes another forty degrees

Let \(b\) be the number of physical circle-touching bodies of the
cycle, including any with zero circle multiplier. The component has
at least two loaded bodies, so \(b\ge2\). Between consecutive
circle-touching bodies, all internal bodies are circle-clear, hence
unloaded degree-two transmitters.

Their common oriented normal is \(n\). If the channel has \(k\)
internal bodies, adding its exact support gaps yields

\[
n\cdot(C_{\mathrm{end}}-C_{\mathrm{start}})
 =H_{\mathrm{start}}(n)+H_{\mathrm{end}}(n)
       +\sum_{j=1}^{k}w_j\ge1+k,                       \tag{5}
\]

where each \(w_j\in\{1,\sqrt2\}\). All centers have norm
less than \(\rho_0=61/40\), so \(k\ge3\) is impossible.
There are only \(k=0,1,2\).

Let \(\gamma\) be the minor angular separation of the two endpoint
center directions. Their radii are less than \(\rho_0\).

* If \(k=0\), `CENTERED_INNER_ARC.md` gives
  \(\gamma>2\pi/9\).
* If \(k=1\), equation (5) gives endpoint distance at least two.
  Were \(\gamma\le4\pi/9\), then
  \(\cos\gamma\ge\cos(4\pi/9)>1/6\). Separate convexity
  in the two radii on \([0,\rho_0]^2\) gives
  \[
  |C-D|^2<\frac53\rho_0^2
        =\frac{18605}{4800}<4,
  \]
  a contradiction. For the exact trigonometric comparison, write
  \(t=\sin(\pi/18)\): the increasing polynomial
  \(3t-4t^3\) takes value \(1/2\) at this \(t\), whereas
  its value at \(1/6\) is \(13/27<1/2\). Thus
  \(\cos(4\pi/9)=t>1/6\).
* If \(k=2\), equation (5) gives endpoint distance at least three.
  Were \(\gamma\le2\pi/3\), then
  \[
  |C-D|^2\le |C|^2+|D|^2+|C|\,|D|
       <3\rho_0^2=\frac{11163}{1600}<9,
  \]
  again a contradiction.

In every case the positive circular-order gap between the endpoints
is at least their minor separation and is therefore strictly greater
than

\[
\frac{2\pi}{9}(k+1).                                   \tag{6}
\]

The circular-order gaps sum to \(2\pi\). If the whole cycle has
\(m\) bodies, the sum of \(k+1\) over its channels is exactly
\(m\). Summing (6) therefore gives

\[
2\pi>\frac{2\pi}{9}m,
\qquad m<9.
\]

Hence \(m\le8\), as claimed. \(\square\)

## 5. Scope of the consequence

This excludes an entire nine-body selected simple-cycle component
in the declared window. It retains all independently rotated squares,
all choices of circle-loaded and circle-clear members, and degenerate
shared junctions allowed by the selected physical certificate.

A hypothetical nine-square minimizer may still have a smaller
simple-cycle component and additional physical completion squares, or
a positive component with a different graph. Those cases are not
excluded by this theorem.
