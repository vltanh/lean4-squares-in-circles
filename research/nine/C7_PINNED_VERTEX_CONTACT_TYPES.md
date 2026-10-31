# Only two geometric types of free vertex edge remain in a pinned C7

**Status: complete pinned-edge classification with an open normal selection;
root and separate independent hand audits passed.** Suppose a selected positive C7 is in the
remaining radius range

\[
                 \frac{\sqrt{17}}2\le R\le\frac{\sqrt{1105}}{16}.
 \tag{1}
\]

For smaller R, `CENTER_COVER_PIERCING.md` already gives completion
capacity one from the origin-centered disk of radius three-halves.
Use the simultaneous choices from
`C7_SHARED_SIDE_BLOCK_GENERIC_SELECTION.md` and
`C7_TWO_CIRCLE_CORNER_BLOCKS.md`.

Every remaining free point-only vertex/vertex edge can be reduced to
one of these two complete geometric types:

1. A contact between two radial bodies, at their inner vertices.
2. A contact between the outer-adjacent vertices of the unique-corner
   ends of two pinned blocks, each containing exactly two squares.
   These two blocks are mirror images about the contact-point ray.

All other free vertex contacts between pinned blocks are excluded
below. This classifies their geometry; it does not yet exclude these
two types or prove the C7 two-square completion bound. Owned edges
and all two-owner/zero-owner transitions remain unrestricted.

## 1. Constants and the pinned-block reduction

Put

\[
 q=R^2,\quad c=\sqrt{q-9/4},\quad
 a_0=\sqrt{q-1/4},\quad d=a_0-1,
\]

\[
 b=\sqrt{4c-7/4},\qquad
 e=\sqrt{6c-27/4},\qquad
 f=\sqrt{q-(2-e)^2}.
 \tag{2}
\]

The useful bounds are

\[
 \sqrt2\le c\le23/16<3/2,\qquad d\ge1,
 \qquad 39/20<b\le2,
\]

\[
                 13/10<e<11/8,\qquad 19/10<f<2.
 \tag{3}
\]

Here \(b^2\ge4\sqrt2-7/4>77/20>(39/20)^2\), using
\(\sqrt2>7/5\); its upper bound is immediate at \(c=23/16\).
Likewise \(e^2\ge6\sqrt2-27/4>(13/10)^2\), since
\(\sqrt2>211/150\), and \(e^2\le15/8<(11/8)^2\).
For f, the lower bound follows from
\(q\ge17/4\) and \(2-e<7/10\), giving \(f^2>94/25>(19/10)^2\).
The upper bound follows from
\(q\le1105/256\) and \(2-e>5/8\), giving
\(f^2<1005/256<4\).

The preceding block theorem says that each maximal shared-side block
incident to a free vertex edge has exactly one radial body. That body
is an endpoint, or is the singleton block, and both of its circle
corner weights are positive.

A vertex contact at a radial body forces the neighbor to be radial
by the vertex-shell lemma. Thus a free vertex edge either joins the
two radial endpoints, already type 1, or joins two unique-corner ends
of nonsingleton pinned blocks. The latter two blocks are distinct:
a single block closed by one free edge would join its radial endpoint
to its unique-corner endpoint, contradicting the vertex-shell lemma.
If their lengths are k and l, then

\[
                         k,l\ge2,\qquad k+l\le7.
 \tag{4}
\]

We now classify every possibility in (4).

## 2. The first five bodies of a pinned block are forced

Rotate and, if necessary, reflect the configuration so its radial
endpoint is

\[
             S_1=[d,d+1]\times[-1/2,1/2],
\]

and the shared-side path proceeds in positive circular order from it.
All frames in the path are parallel. The successive centers and circle
corners, if the block is long enough, are exactly:

| Body | Center | Circle corner |
| --- | --- | --- |
| \(S_2\) | \((c-1/2,1)\) | \((c,3/2)\) |
| \(S_3\) | \((c-3/2,b-1/2)\) | \((c-2,b)\) |
| \(S_4\) | \((c-5/2,e-1/2)\) | \((c-3,e)\) |
| \(S_5\) | \((1/2-f,e-3/2)\) | \((-f,e-2)\) |

The corresponding incoming shared-side segments are:

\[
\begin{array}{ll}
 S_2:& y=1/2,\quad d\le x\le c,\\
 S_3:& x=c-1,\quad b-1\le y\le3/2,\\
 S_4:& x=c-2,\quad b-1\le y\le e,\\
 S_5:& y=e-1,\quad c-3\le x\le1-f.
\end{array}
 \tag{5}
\]

Here and below these are actual common segments, not prescribed force
application points.

To verify exhaustiveness, a parallel unit neighbor sharing a vertical
side has its center x-coordinate displaced by exactly one; a neighbor
sharing a horizontal side has its center y-coordinate displaced by
exactly one. Its remaining coordinate is fixed up to sign by the circle
equation

\[
                 (|x|+1/2)^2+(|y|+1/2)^2=q.
 \tag{6}
\]

For \(S_1\), the outward radial face is impossible by width and the
inward radial face by the shallow-contact lemma. The forward shared
neighbor is therefore on the upper tangential face, giving \(S_2\).

At \(S_2\), its upper and right neighbors would have a corner coordinate
larger than R. Its lower circle-touching neighbor returns to \(S_1\);
the other sign choice is too far to overlap the side. Its unique remaining
shared neighbor is the left one, \(S_3\).

At \(S_3\), the top is impossible by width, the right returns to
\(S_2\), and the left gives \(S_4\); the wrong vertical sign gives a
center-coordinate difference greater than one. A bottom neighbor would
have \(y=b-3/2\) and

\[
 |x|+1/2=A:=\sqrt{q-(b-1)^2}.
\]

But

\[
 A^2-(3-c)^2=2(c+b-3)>0.
\]

Hence \(|x|>5/2-c=1+|c-3/2|\). Its horizontal coordinate interval
cannot meet that of \(S_3\), so it does not share the proposed side.

At \(S_4\), the left and top are impossible by width, the right returns
to \(S_3\), and the unique bottom neighbor is \(S_5\). The other
horizontal sign has coordinate distance greater than one. The ranges
(3) verify every indicated overlap and exclude the other signs.
This proves the listed profiles and (5).

No longer profile is needed: by (4), a block meeting another
nonsingleton block at the free edge has length at most five.

## 3. A universal lower radius for a boundary/boundary contact

For any common point p of two interior-disjoint circle-touching unit
squares, there is the stronger general bound

\[
                         |p|\ge\sqrt{R^2-1}-1.
 \tag{7a}
\]

This includes side contacts and all common normals. In the range (1),
it gives the particular fact needed below:

\[
 \boxed{\text{Every boundary/boundary contact point has }|p|>1/\sqrt2.}
 \tag{7}
\]

To prove (7a), put \(r=|p|>0\) and \(u=p/r\). The positivity of r
follows because no circle-touching unit square can contain the origin
when \(R>\sqrt2\).

For a unit square S containing p on its boundary, if

\[
                   \max_{x\in S}u\cdot(x-p)>1,
\]

then u lies strictly inside its tangent sector at p. Indeed, at a
vertex write \(S-p=[0,1]v+[0,1]w\) for inward orthonormal side
vectors. If either \(u\cdot v\) or \(u\cdot w\) were nonpositive,
the displayed maximum would be at most one. At a side-interior point
write \(S-p=[-t,1-t]v+[0,1]w\), where \(0<t<1\) and w is the inward
normal. If \(u\cdot w\le0\), the maximum would again be at most one.
These are every boundary-point type.

The two touching squares cannot both have this forward support greater
than one: a sufficiently small positive displacement \(p+\epsilon u\)
would then lie in both open interiors. Thus at least one square S
satisfies \(u\cdot(z-p)\le1\) for each of its points z. Choose one of
its circle corners. Since \(|z-p|\le\sqrt2\),

\[
 R^2=|z|^2=r^2+2r\,u\cdot(z-p)+|z-p|^2
                 \le r^2+2r+2.
\]

Solving this quadratic gives (7a). Finally

\[
 \sqrt{R^2-1}-1\ge\frac{\sqrt{13}}2-1>\frac1{\sqrt2},
\]

where the final strict comparison reduces to \(7/4>\sqrt2\).
This proves (7).

## 4. Vertex-radius comparisons exhaust the unequal block lengths

A free edge at the far end of a block cannot use its circle corner.
It also cannot use a vertex in its incoming shared segment (5),
since that would put three circle-touching bodies at one point.
The remaining vertex possibilities have the following squared norms:

| Block length | Remaining vertices | Squared norms |
| --- | --- | --- |
| 2 | \((c-1,1/2)\), \((c-1,3/2)\) | \((c-1)^2+1/4\), \(q-2c+1\) |
| 3 | \((c-2,b-1)\), \((c-1,b)\) | \(q-2b+1\), \(q+2c-3\) |
| 4 | \((c-2,e-1)\), \((c-3,e-1)\) | \((2-c)^2+(e-1)^2\), \(q-2e+1\) |
| 5 | \((1-f,e-2)\), \((-f,e-1)\) | \(q-2f+1\), \(q+2e-3\) |

For length 2 the first value is at most \(113/256<1/2\), so (7)
excludes it. The surviving value satisfies

\[
                      \frac{12}{5}<q-2c+1\le\frac{625}{256}.
 \tag{8}
\]

For length 3 the two ranges are

\[
                   \frac54\le q-2b+1<\frac32,
 \qquad             q+2c-3>4.
 \tag{9}
\]

For length 4 the first value is less than \(1/2\). Indeed
\(2-c<19/32\) and \(e-1<3/8\), giving an upper bound
\(505/1024<1/2\). It is excluded by (7). The surviving value has

\[
                        \frac52<q-2e+1<3.
 \tag{10}
\]

For length 5,

\[
                    \frac54<q-2f+1<2,
 \qquad              q+2e-3>\frac{77}{20}.
 \tag{11}
\]

All these bounds follow directly from (3); (8) also uses the monotonicity
of \((c-1)^2+9/4\) on the stated c interval. Their margins are strict
where used.

The unordered length pairs allowed by (4) are

\[
 (2,2),\ (2,3),\ (2,4),\ (2,5),\ (3,3),\ (3,4).
\]

A shared vertex must have the same squared norm in both profiles.
Equations (8)--(11) therefore exclude every unequal pair. Only
\((2,2)\) and \((3,3)\) remain, with matching vertex types.

## 5. The length-three pair has no surviving free edge

### 5.1. The high vertex violates the centered forty-degree arc bound

For the high vertex \(p=(c-1,b)\) of \(S_3\), let C be its center
\((c-3/2,b-1/2)\). Their positive scalar product satisfies

\[
 C\cdot p=(c-3/2)(c-1)+(b-1/2)b>\frac{261}{100},
\]

using \(7/5<c<3/2\), \(19/10<b\le2\). Their determinant has
absolute value

\[
             |\det(C,p)|=\frac{b-c+1}{2}<\frac45.
\]

The angle \(\delta\) between C and p consequently satisfies
\(\tan\delta<1/3\). For two length-three profiles sharing this high
vertex, their center directions differ by at most
\(2\arctan(1/3)<2\pi/9\). To check the last strict inequality,
\(\tan(3\arctan(1/3))=13/9<\sqrt3\), with both compared angles in
\((0,\pi/2)\). This contradicts `CENTERED_INNER_ARC.md`.

### 5.2. Both side-axis endpoints prohibit the low-vertex block stress

It remains to consider the low vertex

\[
                       p=(c-2,b-1).
\]

Its genuine outward normal cone has endpoints \(-e_x\) and
\(-e_y\). Let n be the outward force direction at p, normalize its
magnitude to one, and let \(\mu>0\) be the incoming shared-side force
magnitude on \(S_3\). Its application is \((c-1,s)\), where

\[
                             b-1\le s\le3/2.
 \tag{12}
\]

The circle corner is \((c-2,b)\). Translation and torque give

\[
 \lambda=-\frac{n_y}{2b},\qquad
 \mu=-n_x-\frac{2-c}{b}n_y,
\]

\[
             s=\frac{-(2-c)n_y-(b-1)n_x}{\mu}.
 \tag{13}
\]

At \(n=-e_y\), equations (13) require \(s=b>3/2\), contradicting
(12). This is a strict failure.

At \(n=-e_x\), they instead give \(\lambda=0\), \(\mu=1\), and
\(s=b-1\). The middle body \(S_2\) has the two internal shared-side
forces along \(-e_x\) and \(-e_y\) and its unique circle corner
\((c,3/2)\). Its translation and torque equations force its application
on the radial body's upper side to have first coordinate

\[
                  t=\frac{2c}{3}s
                    =\frac{2c}{3}(b-1)
                    \le\frac{23}{24}<1\le d.
 \tag{14}
\]

But that actual shared segment requires \(d\le t\le c\), by (5).
Again the failure is strict. This calculation retains the zero load
of \(S_3\); the middle body's two nonparallel positive forces force
its circle load to be positive.

The expressions (13) are continuous near either axis endpoint, with
\(\mu>0\). Hence (12) or (14) continues to fail for all normals in
some one-sided open neighborhood of that endpoint. The conclusions
are independent of the load split at the radial endpoint and of its
other external contact.

At any common vertex/vertex normal cone, an interval endpoint is an
actual side axis of at least one body. For a length-three/length-three
pair, choose such an endpoint and then choose a strict common normal
sufficiently near it. The corresponding block cannot carry the
required positive stress. Thus this entire pair type is excluded by
an open normal restriction.

## 6. Compatibility of the choices and the remaining length-two module

The physical circle-contact graph underlying an all-boundary positive
C7 is precisely that cycle. Its maximal physical shared-side blocks
are fixed by the packing, so each free edge has an unambiguous pair
of profiles. A length-three pair therefore supplies only the one
local open restriction just described, rather than conflicting
restrictions from several different block assignments.

The two pinned blocks have different frame directions: their radial
endpoints cannot be parallel by
`C7_TWO_CIRCLE_CORNER_BLOCKS.md`, Section 6. Hence their vertex contact
cannot be a four-square junction, since four squares at a point have
parallel frames. The choice is independent of the matched-junction
parameters. It also concerns a different physical edge from the
radial/radial edges restricted in the no-three-radial-run argument.
The remaining finite open-dense generic choices can be made inside
all these open intervals. Uncrossing and thinning preserve every
surviving fixed point normal as before.

Only the length-two pair remains among unique-corner endpoints. Its
vertex is necessarily

\[
                       p=(c-1,3/2)
\]

in the first radial endpoint's frame. The profile is fixed by R.
Let

\[
                 \phi=\arctan\frac{3}{2(c-1)}\in(\pi/4,\pi/2).
\]

The two embeddings sharing p must be mirror images about its radial
ray. Equal choices of the sign of this relative angle would place
the two radial endpoints at the same center and give overlapping
squares. The radial endpoint directions are therefore separated by
\(2\phi\), and the entire four-body module is determined by R up to
rotation and reflection. This is type 2 in the statement.

Together with the radial/radial vertex-shell case, this exhausts every
surviving free vertex edge after the stated choices. Both modules and
the arbitrary owned edges between other bodies still require a full
positive-C7 completion argument. No capacity conclusion is asserted
by this classification alone. \(\square\)

## 7. The complete free-edge graph has at most two edges

Use the symmetric run selection from Section 8 of
`C7_TWO_CIRCLE_CORNER_BLOCKS.md`. Every radial/radial edge now joins
two nonsingleton pinned blocks. The other surviving free-edge type
already joins two blocks of length two. Consequently **every block
incident to a free edge has length at least two and at most five**.
The profiles in Section 2 therefore cover every such individual
block, including those whose free edge is at the radial endpoint.
A length-six block with a radial singleton at its other end is
excluded by the symmetric run choice.

Contract each maximal shared-side block, retaining singleton blocks.
The remaining point edges form the cyclic order of these blocks;
with two blocks the two connecting point edges are retained as two
distinct edges. Every free edge joins pinned blocks, and there are at
most three such blocks because each has at least two of the seven
bodies.

Each nonsingleton pinned block has one radial endpoint and one
unique-corner endpoint. A free edge connects equal endpoint types:
radial to radial, or unique-corner to unique-corner. A block with two
free incident edges therefore has one edge of each type. A cycle
consisting entirely of free edges would alternate these edge types
and have an even number of blocks. There cannot be four such blocks
with only seven bodies. With two blocks, the unique-corner edge
forces both lengths to be two, leaving only four bodies and so not
the entire seven-body cycle. A single-block closing free edge would
join its radial and unique endpoints and is already impossible by
the shell lemma. Thus the free-edge subgraph has no cycle.

Two disjoint free edges would require four distinct nonsingleton
pinned blocks, again at least eight bodies. It follows that the
surviving free-edge graph is exactly one of:

* no free edge;
* one radial/radial edge between two pinned blocks of lengths at
  least two, whose sum is at most seven;
* one unique/unique edge, the exact mirror length-two module of
  Section 6;
* a path of two free edges on three pinned blocks, one edge of each
  type.

In the last case, the middle block and the endpoint block on its
unique/unique side both have length two. The third block has length
two or three. If its length is three, these are all seven bodies and
the sole remaining point edge is owned. If its length is two, there
is one additional singleton body on the remaining owned path. That
singleton cannot be radial: one end of the remaining path is a
radial pinned endpoint, and a contact between two radial bodies
would be a free vertex edge incident to a prohibited singleton.
Thus this additional body has a unique physical circle corner.

This is an exhaustive graph and individual-block profile reduction
for all remaining free normals in the C7 branch. The arbitrary owned
contacts on the complementary path are retained, with their true
positions, orientations, circle masks and every ownership transition.
A capacity argument for these complete layouts, or the all-owned
layout, is still required; no full C7 closure follows from the
normal form alone.
