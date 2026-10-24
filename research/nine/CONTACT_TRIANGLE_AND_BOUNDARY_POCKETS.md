# Empty contact-triangle holes and empty exterior boundary-contact pockets

**Status: complete hand geometric arguments; two separate hand audits passed.**
Two kinds of complementary regions cannot contain a further unit square:

1. a bounded region enclosed by a physical contact cycle of three unit
   squares, at any containing radius;
2. the exterior pocket between two touching circle-boundary unit squares,
   throughout the declared nine-square radius window.

The first statement uses area only after an exact winding localization.
The second uses simultaneous dilation and the angular-neighbor contact
rule; it does not require seven circle-touching bodies to be present.

## 1. A three-square contact hole is too small

Let \(S_0,S_1,S_2\) be three closed unit squares with disjoint open
interiors. Suppose they have respective shared contact points

\[
 p_0\in S_0\cap S_1,\qquad
 p_1\in S_1\cap S_2,\qquad
 p_2\in S_2\cap S_0,                                   \tag{1}
\]

and that the center/contact loop

\[
 \Gamma=c_0p_0c_1p_1c_2p_2c_0                           \tag{2}
\]

is a simple Jordan curve. Distinct contact points guarantee this:
each open center-to-contact segment lies in its own square's interior,
and the two segments from any one center have distinct rays.

Let \(T\) be a further closed unit square, interior-disjoint from
all three, whose open interior lies on the bounded side of \(\Gamma\).
For each \(i\), move the center vertex \(c_i\) linearly to the
midpoint of its two adjacent contact points, keeping every \(p_i\)
fixed. The two segments incident to \(c_i\) stay in the convex
square \(S_i\) throughout. At the end the loop is the boundary
of the contact triangle

\[
                     \Delta=\operatorname{conv}(p_0,p_1,p_2),
                                                               \tag{3}
\]

with its edge midpoints inserted.

Every point of \(\operatorname{int}T\) is disjoint from the
**closed** three squares: an open neighborhood of a point in a closed
square always meets that square's open interior. Thus the preceding
homotopy avoids every point of \(\operatorname{int}T\). Its winding
number there remains the nonzero winding number of \(\Gamma\).
It follows that \(\operatorname{int}T\subset\operatorname{int}\Delta\).
If the contact triangle is degenerate, its boundary has zero winding
about every point outside it, and the same argument already gives a
contradiction. Otherwise taking closures gives \(T\subseteq\Delta\).

Every side of \(\Delta\) joins two points of a single unit square,
so its length is at most \(\sqrt2\). A triangle all of whose side
lengths are at most \(\sqrt2\) has area at most \(\sqrt3/2\).
For an elementary verification, take a side of length \(d\le\sqrt2\)
as base. The third vertex's distances to the two endpoints are at most
\(\sqrt2\), so its height is at most \(\sqrt{2-d^2/4}\). Hence

\[
 \operatorname{area}(\Delta)^2
       \le \frac{d^2}{4}\left(2-\frac{d^2}{4}\right)
       \le \frac34,                                    \tag{4}
\]

the expression being increasing for \(0\le d^2\le2\).
Consequently \(\operatorname{area}(T)=1\le\sqrt3/2<1\), impossible.

**Theorem 1.1.** No additional unit square can lie on the inner side of
a simple three-square center/contact ring. The argument retains all
individual square orientations and all choices of actual shared contact
points. A triple whose three chosen contacts coincide gives no physical
bounded hole; the theorem makes no artificial-face assumption at such a
junction.

## 2. Circle corners have the same circular order as square centers

For the remainder assume

\[
                   \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
                                                               \tag{5}
\]

We use the following previously proved geometric facts:

- distinct circle-touching square center directions differ by more than
  \(2\pi/9\), by `CENTERED_INNER_ARC.md`;
- touching circle-boundary squares have center separation less than
  \(2\pi/5\), and their minor center arc contains no other
  circle-touching center direction, by `CIRCLE_CONTACT_ANGULAR_ORDER.md`;
- each circle-touching square's full angular shadow has length less than
  \(\pi/3\), from the same source.

We also need the following direct bound, so that the choice of a circle
corner on a body with two circle corners creates no order ambiguity.

**Lemma 2.1.** Every circle corner of a square in (5) differs in angular
direction from that square's center by strictly less than \(\pi/9\).

*Proof.* In the outward side frame at the circle corner, write

\[
 z=(a,b),\qquad a\ge b\ge\frac12,\qquad a^2+b^2=R^2,
 \qquad c=(a-\tfrac12,b-\tfrac12).                       \tag{6}
\]

The lower coordinate bounds follow by comparing the adjacent square
corners with the radius \(R\). Since \(z\cdot c>0\), the angular
difference \(\delta\) satisfies

\[
 \tan\delta
   =\frac{a-b}{2R^2-a-b}
   <\frac{R-1/2}{2R^2-(3/2)R}<\frac13.                 \tag{7}
\]

Here \(a-b\le R-1/2\), \(a+b\le\sqrt2R<(3/2)R\), and the
denominators are positive. The last inequality is equivalent to

\[
                  2R^2-\frac92 R+\frac32>0.
\]

This polynomial is increasing for \(R\ge79/40\), and at the
lower endpoint it equals \(331/800>0\). Finally
\(\arctan(1/3)<\pi/9\): the tangent of three times this angle
is \(13/9<\sqrt3\), with all angles in the monotone branch of
the tangent. Thus \(\delta<\pi/9\). \(\square\)

The open angular intervals of radius \(\pi/9\) about the
circle-touching center directions are disjoint, by the strict
\(2\pi/9\) center separation. All circle corners of each body
lie in its own such interval. Therefore selecting one circle corner
from each body preserves the circular center order. In particular, if
two circle-touching bodies touch each other, their selected corners are
consecutive among all selected corners along the corresponding minor
arc. That arc has length less than

\[
                     \frac{2\pi}{5}+\frac{2\pi}{9}<\pi.
                                                               \tag{8}
\]

## 3. Define the exterior pocket of a touching boundary pair

Let \(A,B\) be touching circle-boundary squares in a packing
satisfying (5). Choose any shared point \(p\in A\cap B\)
and any circle corners \(z_A\in A\), \(z_B\in B\). The path

\[
                  z_A,c_A,p,c_B,z_B                         \tag{9}
\]

is a simple crosscut of the disk. Its open parts are inside the two
squares, and a circle point cannot be shared by two packing squares.
The two shadows of \(A,B\) overlap at the direction of \(p\)
and have total union length less than \(2\pi/3<\pi\). Thus
(9), together with the shorter circle arc from \(z_A\) to \(z_B\),
bounds the outer pocket \(\Omega\), the region on the exterior
side of this two-square link. This choice is unambiguous: the link and
that circle arc lie in the same closed angular sector of aperture less
than \(\pi\), so the bounded region between them does not contain
the origin.

Parts of \(A\) or \(B\) may themselves lie in \(\Omega\).
That causes no problem. Every connected component of
\(D_R^\circ\setminus(A\cup B)\) meeting \(\Omega\) is
confined to \(\Omega\), since its interior boundary crosscut is
entirely in those two obstacles. A second circle corner of either body
may further subdivide the pocket, still using only those same obstacles.

Every other square's open interior avoids the crosscut (9), and is
therefore either entirely in \(\Omega\) or entirely on its other
side. If a square in \(\Omega\) touched the circle, each of its
circle corners would be strictly on the selected open arc from
\(z_A\) to \(z_B\). It cannot share either endpoint. Lemma 2.1
and the circular order just proved would then put its center direction
strictly between those of \(A,B\) on their minor center arc. This
contradicts the angular-neighbor contact rule for the touching pair.
Therefore every square in \(\Omega\) is initially strictly
circle-clear.

## 4. Dilation empties the entire exterior pocket

Suppose the pocket contains one or more additional packing squares.
Take all of them and, keeping their orientations fixed, move each center
\(c_j\) to

\[
                         c_j(s)=p+s(c_j-p),\qquad s\ge1.
                                                               \tag{10}
\]

The simultaneous dilation lemma in `C7_COMPLETION_LOCALIZATION.md`,
Section 1, proves that this preserves every mutual separation and every
separation from \(A,B\). For completeness, a unit separator \(n\)
from \(A\) to square \(j\) satisfies

\[
 n\cdot p\le h_A(n)\le n\cdot c_j-H_j(n),
 \qquad n\cdot(c_j-p)\ge H_j(n)\ge\frac12.
\]

Thus its separation gap increases strictly for \(s>1\). The same
holds for \(B\). A separator between two moving squares has its
center-difference projection multiplied by \(s\), while its two
support halfwidths remain fixed, so that separation also persists.

While the moving squares remain in the disk, their open interiors stay
in the same components of \(D_R^\circ\setminus(A\cup B)\).
They therefore stay in \(\Omega\) and cannot overlap any fixed
square on the other side of the crosscut. There were no initially
circle-touching squares in the moving group. Their centers are unbounded
as \(s\to\infty\), since the preceding support inequality gives
\(c_j-p\ne0\). Hence a first circle contact occurs at a finite
\(s_*>1\), with all packing constraints still valid by continuity.

At that time a new circle-touching square has its circle corner strictly
on the open selected arc between \(z_A\) and \(z_B\). This again
contradicts the angular-neighbor rule, because \(A,B\) are unchanged
and still physically touch.

**Theorem 4.1.** The exterior pocket of any touching pair of
circle-boundary squares is empty of additional unit squares throughout
(5). No assumption on the number of other circle-touching bodies or on
their stress weights is used.

## 5. Scope for mixed positive components

Theorem 1.1 removes completion squares from every genuine triangular
contact-ring hole. Theorem 4.1 removes them from every exterior pocket
bounded by a touching pair of circle-boundary squares. Both statements
retain all other physical squares and arbitrary independent frames.

For a triangle-plus-leaf component, the two nonarticulation triangle
vertices are the potentially adjacent loaded boundary pair. Once both
are loaded, these theorems remove the inner triangle hole and that
pair's exterior pocket. The two larger complementary regions involving
the leaf and articulation still require capacity bounds. No full
triangle-plus-leaf completion or unrestricted nine-square theorem is
claimed by these two exclusions.
