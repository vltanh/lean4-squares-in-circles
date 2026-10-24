# A physical boundary seven-cycle has completion capacity one

**Status: complete hand theorem. Root and separate independent full hand
audits passed both final nonparallel branches and this assembly. The earlier
full prerequisite-chain audit remains a separate obligation.**

## 1. Exact statement

Let a finite family of unit squares have pairwise disjoint open
interiors and lie in a disk centered at the origin, of radius

\[
\frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
\tag{1}
\]

Suppose seven of the squares touch the containing circle and form a
physical seven-cycle. Then there is **at most one further unit square**
in the packing.

The two hypothetical further squares may have arbitrary independent
orientations, positions, and contacts. They need not touch each other or
the seven ring squares. No positive stress, equal angular spacing,
common orientation, side ownership convention, or regularity is assumed
in this geometric theorem.

The conclusion is strict at the upper endpoint of (1). Thus a physical
boundary C7 contributes no nine-square equality configuration there.
This is a completion theorem for the entire boundary-cycle family; it
does not assert that all positive components in the global packing
problem are boundary cycles.

## 2. Actual ring localization and center geometry

The angular-neighbor theorem
`CIRCLE_CONTACT_ANGULAR_ORDER.md` says that the circle-touching graph
has only path components unless it is one complete seven-cycle. Hence
the physical cycle in the hypothesis has no extra ring chords. All
circle-touching squares are its seven vertices.

By `C7_COMPLETION_LOCALIZATION.md`, every further square lies inside
the bounded region enclosed by this physical ring. This localization
retains every other completion square: simultaneous dilation of all
squares in any exterior pocket would produce an eighth circle-touching
square, contradicting the universal boundary-count theorem. In
particular no extra square is silently placed inside the ring by a
normalization.

Write the seven actual centers as \(C_0,\ldots,C_6\), and put

\[
P=\operatorname{conv}\{C_0,\ldots,C_6\},\qquad
M=\frac{91}{60},\quad Q=\frac{1105}{256}.
\]

The established geometric results give all the following properties:

* Every enclosed unit is contained in the convex center polygon \(P\),
  by `C7_CENTER_POLYGON_LOCALIZATION.md`.
* Every polygon edge has length at most \(\sqrt2\), since its endpoint
  squares physically touch.
* Every center is at distance at least \(1/2\) from every enclosed
  square, because the open radius-half disk about that center lies in
  its actual boundary square.
* Every boundary center has norm strictly less than \(M\).
* Any two boundary centers have distance strictly less than three, by
  `BOUNDARY_SEVEN_CYCLE_CENTER_DIAMETER.md`.
* Every actual boundary square is contained in \(D_Q\), by (1).

The distinction between a center bound and whole-square containment is
retained. The final nonparallel argument uses the actual corners of
boundary squares; a relaxation using only their centers is insufficient.

## 3. Exhaustion of two arbitrary enclosed units

Suppose two further interior-disjoint units \(T,U\) exist. Section 2
places both in \(P\), with all the clearance and edge-length
properties just listed.

### 3.1. Parallel frames

If their frames are parallel, the entire arbitrary-gap and
arbitrary-stagger theorem
`PARALLEL_INNER_PAIR_DIAMETER_EXTRACTION.md` gives two polygon vertices
at distance at least three. This contradicts the strict center-diameter
bound. Thus the two frames are genuinely nonparallel.

### 3.2. A fixed actual separator for the nonparallel pair

Choose an actual SAT axis owned by one member of the inner pair, call
that member \(T\), and direct the normal toward \(U\). Rotate the
whole picture about the fixed circle origin so this normal is \(e_x\).
A reflection and a quarter-turn relabeling of \(U\)'s frame give

\[
C_T=(-\alpha,\beta),\qquad C_U=\xi u+\eta v,
\quad u=(c,s),\quad v=(-s,c),\quad
c=\cos\theta,\quad s=\sin\theta>0.
\]

The actual separation is

\[
\alpha+\xi c-\eta s\ge\frac{1+c+s}{2}.
\tag{2}
\]

The uniform radial side/corner restrictions
`C7_INNER_SIDE_CORNER_RESTRICTIONS.md` and
`C7_INNER_OUTSIDE_FACE_CORNER_EXCLUSION.md` give

\[
|\alpha|,|\beta|,|\xi|,|\eta|<k:=\frac{3721}{7200},
\qquad 0<s<\frac4{15}.
\tag{3}
\]

The actual far-face theorem
`C7_INNER_PAIR_FAR_FACE_CENTERS.md` proves
\(\alpha,\xi>9/20\) and supplies two actual boundary centers

\[
C_L=C_T-(1+\delta)e_x+t e_y,
\qquad C_R=C_U+(1+\varepsilon)u+r v,
\]

with \(\delta,\varepsilon\ge0\), \(|t|,|r|\le1/2\).
The strict center-diameter bound yields

\[
r>\frac12-\frac32\tan(\theta/2).
\tag{4}
\]

Since \(\alpha,\xi>9/20>3/8\), the outside-face restriction also
forces \(|\beta|,|\eta|<1/2\). If both
\(\alpha\le1/2\) and \(\xi\le1/2\), then \(s>0\) and
\(\eta>-1/2\) make the left side of (2) strictly less than its
right side. Consequently the complete remaining cover is

\[
\boxed{\xi\ge1/2
\quad\text{or}\quad
\xi<1/2\ \text{and}\ \alpha>1/2.}
\tag{5}
\]

Both alternatives keep the same original left-owned separator.

### 3.3. Both nonparallel alternatives are excluded

`C7_RIGHT_OUTSIDE_INNER_EXCLUSION.md` excludes the entire first
alternative in (5). It identifies the outgoing ray witness of \(U\)
with the actual far-face unit \(C_R\), retaining every possible
outer frame and SAT owner/sign. Ray membership then contradicts the
height forced by (4).

`C7_LEFT_OUTSIDE_INNER_EXCLUSION.md` excludes the entire second
alternative. For clarity, its final continuous contradiction is as
follows. Set

\[
a=\xi,\quad d=1/2-a,\quad
e=k-1/2=\frac{121}{7200},\quad
L(d)=\sqrt{M^2-(3/2-d)^2}.
\]

The complete case analysis proves \(0<d<e\) and again identifies
the outgoing ray witness with the same actual \(C_R\). Upward
separators owned by the inner unit are ruled out using an actual outer
corner with projection greater than \(581/125\) on \((1,2)\);
its squared norm would exceed \(Q\). All other normal signs are
either impossible or force that witness to be \(C_R\).

Whole-square containment, ray membership, and the exact pair separator
then give incompatible bounds on the one tangential offset \(r\):

\[
r<W(d)<\frac{17}{40}+\frac{43}{10}d,
\qquad
r>\frac12-4(e-d),
\]

where

\[
W(d)=\frac{(11/10)(1/2-d)}{2-2d}
+\frac{L(d)}{3/2-d}.
\]

The former upper bound is below the latter lower bound throughout
\(0<d<e\), because their difference is at most

\[
-\frac3{40}+\frac{43}{10}e
=-\frac{197}{72000}<0.
\]

The proof of those bounds is continuous on the entire remaining
parameter domain; no pose table or numerical subdivision is a premise.

Parallel and nonparallel cases are exhaustive, and the alternatives in
(5) are exhaustive within the latter. Therefore two enclosed units are
impossible. Section 2 localized every possible completion square to
that region, proving the capacity-one theorem.

## 4. Consequences for the global positive-component reduction

For any nine-unit packing in the window (1), the complete physical
circle-touching graph is a disjoint union of paths. Indeed its only
possible cyclic alternative is the seven-cycle, and the theorem above
excludes the two remaining units required by a nine-square packing.

In particular an all-circle-touching selected positive component is
impossible. The exact result in
`CIRCLE_CONTACT_ANGULAR_ORDER.md`, Section 7, identifies every such
component as a physical C7; the present theorem now supplies its missing
completion obstruction. Every surviving positive component must
therefore include a physically circle-clear square.

These conclusions preserve the radius-window prerequisite (1). They
do not replace the independent lower-radius prerequisite or exclude
the remaining mixed cyclic components. No positive C7 equality case
survives at \(R=\sqrt{1105}/16\).

The earlier C7 force-polygon, free-normal, ownership, regular-cycle,
and positive-center-cover investigations are not additional gates for
this theorem. The present exit uses the geometric localization,
center-polygon, strict diameter, actual radial witnesses, and the
exhaustive two-square argument listed above.
