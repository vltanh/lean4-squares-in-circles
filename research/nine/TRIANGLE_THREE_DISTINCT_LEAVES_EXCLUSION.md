# One radial leaf at each triangle root cannot complete nine squares

**Status: complete whole-attachment hand exclusion; root and separate
independent full hand audits passed.** Work in
\[
                         79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]
The exact positive graph is a triangle \(A_1,A_2,A_3\), with one
distinct genuine leaf \(L_i\) at each \(A_i\). All three roots
have exact positive degree three. The six bodies leave three
arbitrary physical squares, which remain in place throughout.

**Theorem.** This entire one-leaf-at-each-root attachment cannot
occur in the selected certificate of a nine-square minimizer.
Every S/D leaf type, parallel or nonparallel root star, actual
side mean and individual circle-weight endpoint is retained.
The critical-radius case is a physical capacity argument; the
other radii are excluded as cores.

Put
\[
 d=\sqrt{R^2-\tfrac14}-1,\qquad r=R-\sqrt2,\qquad
                       \varepsilon=\max(d-1,0)<1/60.
\tag{2}
\]
Each leaf is radial S or D and has positive resultant
\(\alpha_i e_i\), \(\alpha_i>0\), in its actual radial direction.
Every root is physically circle-clear by the central bridge
endpoint theorem. Its genuine leaf makes it meet \(D_\varepsilon\):
a D root contains0 in its interior, while the S root contains
the unit inward segment from \(d e_i\).

The full component force sum is
\[
                              \sum_{i=1}^3\alpha_i e_i=0.
\tag{3}
\]
The three directions are distinct, since the actual radial
leaf centers have these directions and distinct boundary
centers are separated by more than40 degrees. Thus (3) is
noncollinear, and its three successive circular gaps are
strictly less than \(\pi\).

In particular, for any actual root-to-root contact with normal
n directed from \(A_i\) to \(A_j\) and application p,
\[
                      -\varepsilon\le p\cdot n\le\varepsilon.
\tag{4}
\]
The lower bound uses \(A_i\cap D_\varepsilon\ne\varnothing\);
the upper uses \(A_j\cap D_\varepsilon\ne\varnothing\).
All actual shared-side means are included in (4).

## 1. Radii below the critical value are impossible

Suppose d<1. Every S root contains0: in a tilted frame the
coordinates of0 from its radial support vertex are both
strictly between0 and1, while in an aligned frame they
belong to the unit rectangle. Every D root contains0 in
its open interior.

No root can have0 in its open interior, since either of the
other roots also contains0. Thus all three leaves are S,
all roots are aligned with their own radial directions, and
0 lies in a relative side interior of each root. Each root
then occupies a tangent half-plane at0. Three such open
half-planes cannot be pairwise disjoint. This excludes d<1.

## 2. The entire critical value has capacity at most eight

Let d=1, so \(R^2=17/4\). Again all roots contain0, none
contains it in its interior, and all leaves are S.

There cannot be a root with0 in a relative side interior.
If there were, rotate it to
\[
                           [-a,1-a]\times[0,1],
                            \qquad0<a<1.
\]
Its only radial support of norm1 is \((0,1)\), so its leaf
points north. The other two root tangent cones must fill
the remaining lower half-plane. They are the two aligned
lower quadrants. Their respective S directions are
\[
                         \{-e_x,-e_y\},\qquad
                         \{e_x,-e_y\}.
\]
Choosing west/east leaves cannot cancel the north force.
Choosing west/south or south/east leaves cannot cancel
the nonzero horizontal force. Choosing south twice repeats
the same physical radial S unit. These exhaust the options
and contradict (3).

Hence0 is a vertex of each root. Its S direction is one
of the two unit side directions from0. The segment
\([0,e_i]\) is therefore a root boundary side.

The actual root and its terminal \(S(e_i)\) screen the
entire radial ray in direction \(e_i\). The segment
\([0,e_i]\) is occupied by the root, the segment from
\(e_i\) to \(2e_i\) is occupied by the terminal, and the
outer-face screen excludes the continuation beyond \(2e_i\).
This is precisely the physical ray argument of
Y_ALL_COMPLETION.md, Section 1.

Every one of the six nonterminal units—the three roots
and the three additional squares—has its open interior
disjoint from all three rays. For a root's own ray this
holds because that ray follows its boundary side and then
its terminal; for the other rays it follows from actual
interior disjointness and the open-ball argument. Thus each
whole unit belongs to one of the three closed origin wedges.

All three wedge apertures are strictly below \(\pi\) by
(3), and one is at most \(2\pi/3<3\pi/4\).
The strict-wedge consequence of
HALF_POCKET_TRIPLE_RIGIDITY.md gives capacity at most two
for each wedge. WEDGE_135_CAPACITY_ONE.md gives capacity
at most one for the smaller wedge. They apply to the actual
boundary S terminals and retain arbitrary unit orientations.
The total nonterminal capacity is therefore at most
\[
                                  2+2+1=5,
\]
whereas six nonterminal units remain. This excludes the
whole d=1 endpoint.

## 3. The full high-radius zero-moment alternative is impossible

Henceforth d>1, and write
\[
                      \varepsilon=d-1\in(0,1/60).
\tag{5}
\]
Let \(\mathcal H\) be the common directed triangle contact
moment. It is common because every external bridge force
is radial.

Suppose \(\mathcal H=0\). At most one root has parallel
cycle forces: two parallel pairs would make all three
cycle directions, and then all three external directions
in (3), collinear. Choose two nonparallel roots B,C.
Their cycle force-line intersections are0, since both lines
have zero origin moment. The physical proper-port lemma
of END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md, Section 2,
applies independently of loads at the roots. At BC it gives
\[
                       p=a n=-b n,\qquad a,b\ge0.
\]
Thus the actual BC application is0.

B,C contain0, and neither contains it in its open interior.
Neither can be a D root. A unit square with0 at a vertex
has no radial support of norm \(d\in(1,\sqrt2)\): its
possible nonzero radial support radii are1 and \(\sqrt2\).
Therefore both B,C are S roots with0 in a relative side
interior. Their tangent half-planes are complementary and
fill the plane.

A cannot contain0. In particular its actual contact P
with B is not0. Normalize B to
\[
                        [-a,1-a]\times[0,1],\qquad0<a<1.
\]
A radial S support of radius d>1 must be a top vertex.
Consequently
\[
            a\in\{c,1-c\},\qquad
            c=\sqrt{d^2-1}=\sqrt{2\varepsilon+\varepsilon^2}.
\tag{6}
\]
Here \(c>\varepsilon\) and \(c<11/60\), so
\[
                             \min(a,1-a)>\varepsilon.
\tag{7}
\]

At the nonzero BA contact the proper-port relation from
q_B=0 says \(P=\ell n\), \(\ell>0\), with n outward from
B. Thus P is a nonzero radial support of B, and its support
height is \(|P|\). But A meets \(D_\varepsilon\), so (4)
requires \(|P|\le\varepsilon\).

This is impossible in the complete frame (6). Its nonzero
radial support points are the two bottom endpoints at
distances a and \(1-a\), the perpendicular foot on the
top side at distance1, and the top vertices at still
larger distances. A radial support in the bottom side's
relative interior can only be0. Equation (7) excludes
every nonzero option.

This argument covers the case in which the third root
is parallel and every endpoint of its actual mean interval.
It proves
\[
                               \mathcal H\ne0.
\tag{8}
\]

## 4. The actual positive radial concurrences

RADIAL_TRIANGLE_CONCURRENCE.md now applies to the complete
three-root system: the actual external vectors in (3) are
nonzero and noncollinear, each has zero moment, and (8) holds.
At each nonparallel root its cycle-force intersection is
\[
                                  q_i=\tau_i e_i,\qquad\tau_i>0.
\tag{9}
\]
Each actual port lies in its outward-normal direction from
q_i. There is at most one parallel root, which retains
its true wall means and is not assigned a concurrence.

We will use the following full feature observation. If a
root is aligned with its external radial direction, rotate
that direction east. In a nonparallel cycle pair the two
vertical normal components must have opposite nonzero signs.
A horizontal axis normal would instead force both normals
horizontal. A vertical axis normal would make the other
vertical component have the same sign by the unit-triangle
nonobtuse lemma. Thus both normals strictly expose vertices.

They cannot expose opposite vertices, by the physical
support-span lemma. They cannot coincide or occupy the
same horizontal side, since their vertical components
must cancel. They therefore use the two endpoints of one
vertical side. The right-side alternative has both horizontal
components positive and cannot balance the positive east
external force. Hence the contacts are exactly the two
vertices of the left, inner side. Their proper-port lengths
are nonnegative and both first normal components are strictly
negative. Thus q lies on or to the right of that side; equality
would make both lengths zero and the two distinct ports equal.
Consequently q lies strictly to its right, both lengths are
positive, and the actual heights have opposite nonzero signs.

This observation retains all side-axis/mean alternatives:
it excludes them in the nonparallel case rather than
assuming singleton contacts at the outset.

## 5. Every D root is excluded

A D root is aligned with its external direction and, in
the east frame, has
\[
                            A=[r-1,r]\times[l,l+1],
                               \qquad -1<l<0.
\]
If its cycle forces are parallel, both point west. Its
neighbor would lie in \(x\le r-1<-1/3<-\varepsilon\),
contradicting the neighbor's intersection with \(D_\varepsilon\).

Otherwise Section 4 puts both contacts on the inner
vertices \(P=(-s,y)\), where \(s=1-r>1/3\).
By (9) their normals have the direction of
\((-s-\tau,y)\). Their support heights satisfy
\[
       \frac{s(s+\tau)+y^2}{\sqrt{(s+\tau)^2+y^2}}\ge s
                                      >\varepsilon.
\tag{10}
\]
The squared surplus over s is
\(y^2(s(s+2\tau)+y^2)\ge0\).
Equation (10) contradicts (4). Thus all three leaves are S.

## 6. Every tilted S root is excluded

Take a root whose frame is genuinely tilted relative to
its S direction e. The actual leaf point is its strictly
exposed vertex \(d e\). In outward own coordinates write
\[
 \begin{gathered}
 e=(a,b),\qquad a\ge b>0,\qquad a^2+b^2=1,\\
 \alpha=da,\quad\beta=db,\qquad
        A=[\alpha-1,\alpha]\times[\beta-1,\beta].
 \end{gathered}
\tag{11}
\]
Reflection and exchange of the own axes give this full cover.

A cannot contain \(D_\varepsilon\) in its open interior:
another root meets that disk and would then overlap A.
It follows that
\[
                        \alpha\ge1-\varepsilon,\qquad
                        0<\beta\le2\sqrt\varepsilon<13/50.
\tag{12}
\]
Indeed if \(\alpha<1-\varepsilon\), then
\(\beta^2=d^2-\alpha^2>4\varepsilon\), so
\(\beta>\varepsilon\). Since
\(\varepsilon<\beta\le\alpha<1-\varepsilon\),
all four side distances are greater than \(\varepsilon\),
the forbidden disk containment. The second inequality in
(12) now follows by subtracting squares.

If the cycle forces at this root are parallel, both point
in direction \(-e\) and use the unique opposite vertex
\(P=(\alpha-1,\beta-1)\). Its torque would give
\[
                     0=\det(P,e)=\frac{\alpha-\beta}{d}.
\]
This contradicts (12). The entire parallel tilted case is
therefore excluded, with no frozen contact mean.

In the nonparallel case use (9), so \(q=\tau e\), \(\tau>0\).
If \(\tau>d\), every port vector \(P-q\) has both own
coordinates negative. The proper-port property would put
both contacts at the same opposite vertex, contrary to
their nonparallel intersection q. Hence
\[
                                  0<\tau\le d.
\tag{13}
\]

We now exhaust every root feature whose actual support
height might satisfy (4).

The maximum-first-coordinate side has height \(\alpha\),
and the minimum-second-coordinate side has height \(1-\beta\).
Both exceed \(\varepsilon\), so they are impossible.
The vertex \((\alpha,\beta)\) is unshareable: the actual S
leaf occupies a half-plane there and A a right-angle sector.
Since e strictly exposes this A vertex, the two remaining
tangent sectors each have angle strictly below90 degrees.
No third unit's tangent cone can fit at that point.

At \((\alpha,\beta-1)\), any outward normal in its quadrant
has support at least
\[
                    \min(\alpha,1-\beta)>\varepsilon.
\tag{14}
\]
This includes its side-axis endpoints.

At \(P=(\alpha-1,\beta-1)\), consider a strictly exposing
normal. Put \(\eta=d-\tau\ge0\).
Its proper-port vector is
\[
                         P-q=(\eta a-1,\eta b-1).
\]
Both entries are negative at this feature. Each absolute
value is at most1, while the second is at least
\(1-\beta=:h>37/50\). The normalized negative second
component therefore has magnitude at least \(h/\sqrt2\).
Using \(\alpha-1\le\varepsilon\), its support is at least
\[
                         -\varepsilon+\frac{h^2}{\sqrt2}
                              >\frac13>\varepsilon.
\tag{15}
\]
For an entirely rational check, \(\sqrt2<3/2\) makes the
left side greater than \(871/2500>1/3\).
The axis endpoints at this vertex were already included
in the side cover.

The only remaining features are the minimum-first-coordinate
side, the maximum-second-coordinate side, and their common
vertex \((\alpha-1,\beta)\). Every such outward normal has
nonnegative second component. But the genuine external
leaf force has strictly positive second component b.
The complete root force equation cannot sum these vectors
to zero.

This contradiction excludes the entire tilted S frame,
including all actual side means and every possible
root-contact owner.

## 7. An aligned nonparallel S root has concurrence radius greater than4

All roots are now aligned S articulations. In their respective
radial frames,
\[
                           A_i=[\varepsilon,d]\times[l_i,l_i+1],
                               \qquad l_i\le0\le l_i+1.
\tag{16}
\]
At a nonparallel root, Section 4 gives the two inner-face
vertices as the actual cycle ports, with opposite nonzero
heights \(y_+,y_-\). They differ by1, so one has
\[
                              |y|\ge1/2,\qquad |y|\le1.
\]
The distinct-port argument in Section 4 gives
\(\tau>\varepsilon\) for the concurrence \(q=(\tau,0)\),
including the possible zero-length proper-port endpoints.
Set \(k=\tau-\varepsilon>0\).
The outward normal at the chosen port has direction
\((-k,y)\). Its support height must obey (4):
\[
                  \frac{-\varepsilon k+y^2}{\sqrt{k^2+y^2}}
                          \le\varepsilon.
\]
Equivalently,
\[
                  y^2\le\varepsilon\bigl(k+\sqrt{k^2+y^2}\bigr).
\tag{17}
\]
If k were at most4, the right side would be less than
\((4+\sqrt{17})/60<9/60<1/4\), contrary to \(|y|\ge1/2\).
Thus
\[
                                  \tau>4.
\tag{18}
\]
Every actual contact on such an inner face nevertheless
has norm at most
\[
                    \sqrt{1+\varepsilon^2}<61/60.
\tag{19}
\]

## 8. Three nonparallel roots are impossible

Among three distinct radial directions there is a pair
with minor gap at most \(2\pi/3\). For this pair, the
two positive concurrence points have radial distances
greater than4 by (18). Their projection on the unit
bisector is strictly greater than
\[
                               4\cos(\pi/3)=2.
\]
The actual contact between the two roots lies on the
segment joining their concurrences: each proper-port
length is nonnegative, and the two outward normals
are opposite along the common edge.

Every point of that segment therefore has norm greater
than2. This contradicts the actual contact bound (19).
Thus the all-nonparallel alternative is excluded.

## 9. The one-parallel-root alternative is impossible too

Let the unique parallel root point east. Its two cycle
normals both point west, and its actual means have the form
\[
                        P_B=(\varepsilon,y_B),\qquad
                        P_C=(\varepsilon,y_C),\qquad
                               |y_B|,|y_C|\le1.
\tag{20}
\]
The nonzero common moment makes the two heights opposite
and nonzero, though only their displayed bounds are needed.

The other two roots are nonparallel. Their normal toward
the parallel root is east. Their proper-port relations
and (18) give
\[
           (q_B)_x\le\varepsilon,\quad (q_B)_y=y_B,\quad |q_B|>4,
\]
and the identical bounds for \(q_C\).
Each first coordinate is strictly negative: if nonnegative,
its norm would be at most \(\sqrt{1+\varepsilon^2}<61/60\).

Consequently both radial directions \(e_B,e_C\) are within
\(\arcsin(1/4)<15\) degrees of west. The inequality follows
from \(\sin15^\circ>1/4\), equivalently
\(\sqrt6-\sqrt2>1\).
The two actual S leaf centers, whose directions are exactly
\(e_B,e_C\), would have separation angle below30 degrees.
This contradicts their strict boundary-center gap above40
degrees.

The parallel alternative is exhausted without assigning
it a concurrence or replacing either actual wall mean.

## 10. Whole-attachment conclusion

Sections 1--2 cover every radius up to and including
\(R^2=17/4\). Sections 3--9 exclude every high-radius
zero/nonzero moment, S/D leaf and aligned/tilted/parallel
root possibility. All three roots retain their actual
degree-three equations, and every physical contact remains
in the argument.

Thus the entire one-leaf-at-each-triangle-root attachment
is excluded from a nine-square minimizer. The only physical
capacity step was the full critical-radius wedge count,
which explicitly retained all three additional squares.
No numerical pose sampling, secondary minimizer, changed
post-extraction normal, Lean compilation or CI is used.

