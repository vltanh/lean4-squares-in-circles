# Free A-tip normals can be removed throughout the unique-corner C4 mask

**Status: complete selected-certificate reduction; root and separate
independent hand audits passed.**
Consider the opposite-loaded-pair C4-with-leaf component

\[
                         A-B-U-D-A,\qquad A-L,
\]

in 79/40<=R<=sqrt(1105)/16. The radial leaf is L, the
degree-two body U has zero circle weight, and B,D are loaded.
Suppose B and D each have exactly one **physical** circle corner.
Then a compatible pre-certificate normal selection excludes every
positive point-only vertex/vertex edge AB or AD.

The proof retains arbitrary actual shared-side means on every other
edge, including BU,UD and the other A-tip edge. It uses force balance
to fix the free directions; it does not freeze an unknown application
point. No physical two-circle-corner mask is included in the hypothesis,
even if only one of its two circle weights is positive.

This is a full normal reduction for the stated circle mask, not a
closure of its remaining side-owner/shared-side realizations or of the
whole C4-with-leaf cell. The four completion squares remain.

## 1. The channel and one parallel-force degeneracy

By `UNIT_BYPASS_NORMAL_CHANNEL.md`, U is side-normal with reserve
one. Let n be the channel direction from B through U toward D.
It is one of the two side axes of U, with the appropriate sign.
The two transmission forces have a common magnitude gamma>0.

**Lemma 1.1.** Neither loaded unique-corner tip can have both of its
pair forces parallel to n.

*Proof.* Consider B. Force balance would make its unique circle
corner z parallel to n. Put e=z/R. No unit neighbor can touch B
on its maximum-e support, since that support is its circle vertex z.
Thus both pair forces point in direction -e and both actual
applications are B's unique minimum-e vertex p. Torque about p
makes p collinear with z. The opposite-corner difference then gives

\[
                          p=(R-\sqrt2)e.
\tag{1}
\]

Thus B is the radial D square and both A and U contain its inner
vertex p.

The channel force is a side-axis force on U. If p were a vertex of U,
the BU contact would be point-only vertex/vertex, with a normal not
strictly exposing U's vertex. This violates the existing selected
strict convention. Therefore p is in the relative interior of a side
of U. At p, U occupies the half-plane opposite e, while B occupies
the right-angle tangent sector symmetric about e. The two remaining
sectors each have angle pi/4. The tangent cone of another unit square
containing p has angle at least pi/2 and cannot lie in either of
those two sectors. Consequently A would overlap U or B in its open
interior, a contradiction. The proof for D is identical. \(\square\)

The lemma uses the transmitter's side-normal frame and the existing
strict convention. It does not invoke a boundary-neighbor concurrence
theorem or assume that A or U touches the circle.

## 2. All three external circle-force ratios are fixed

Let e be the radial direction of the leaf and z_B,z_D the two
unique physical circle corners. The leaf theorem gives its resultant
as a positive multiple of e, for either leaf type S or D. The global
component force equation is

\[
                   \alpha e+\beta z_B+\eta z_D=0,
                         \qquad \alpha,\beta,\eta>0.
\tag{2}
\]

The three resultant directions are distinct, by the inner-arc
resultant-piercing theorem in `CYCLIC_GLOBAL_CONTINUATION.md`,
Section 8. They cannot be collinear: three distinct nonzero rays
cannot all belong to the two directions of one line. In particular
z_B,z_D are linearly independent, since their antipodality would
force the third vector in (2) onto the same line.

Normalize alpha=1. The two remaining coefficients in (2), and hence
the vectors

\[
                          F_B=\beta z_B,
                          \qquad F_D=\eta z_D,
\tag{3}
\]

are now fixed by the physical pose, independently of every contact
normal and every shared-side application mean. A prelisted physical
candidate for which this normalized solution is not positive cannot
be the stated positive component and needs no normal exclusion.

Let n_B,n_D denote the unit normals on AB,AD, both pointing from A
to the corresponding tip, with positive magnitudes mu_B,mu_D.
The two tip force equations are exactly

\[
              \mu_B n_B=F_B+\gamma n,
              \qquad \mu_D n_D=F_D-\gamma n.
\tag{4}
\]

Lemma 1.1 shows that neither F_B nor F_D is parallel to n in any
surviving candidate. If either were parallel, the corresponding
A-tip force in (4) would also be parallel and the lemma would apply.

## 3. One free A-tip edge and one fixed side-axis edge

Suppose, for example, AD has a fixed actual side-axis normal n_D.
This includes every positive-length shared side, without specifying
its mean. If det(n_D,n)=0, (4) would force F_D parallel to n,
already excluded. Otherwise (4) determines the single scalar

\[
                   \gamma=\frac{\det(n_D,F_D)}{\det(n_D,n)}.
\tag{5}
\]

The vector F_B+gamma n is nonzero, since F_B is not parallel to n.
Thus any positive AB edge must have its normal parallel to that one
fixed vector. At a point-only vertex/vertex contact, this excludes
at most two unit normal directions from the permitted open interval.
Choose its strict normal outside those directions. This eliminates
the candidate independently of every shared-side mean.

The case with AB fixed and AD free is the same calculation with
the roles reversed. Cases where the value in (5) is nonpositive
already cannot supply the required positive transmission magnitude.

## 4. Two free A-tip point edges

Suppose both AB and AD are point-only vertex/vertex edges. Taking
cross products in (4) and eliminating gamma gives the necessary
condition

\[
\begin{split}
 P(n_B,n_D):={}&\det(n_B,F_B)\det(n_D,n)\\
              &+\det(n_D,F_D)\det(n_B,n)=0.
\end{split}
\tag{6}
\]

This is a nonzero condition on the product of the two permitted
normal intervals. To check this explicitly, fix any n_B with
det(n_B,n) nonzero and put

\[
                  g=-\frac{\det(n_B,F_B)}{\det(n_B,n)}.
\]

Then

\[
                   P(n_B,n_D)=\det(n_B,n)
                                \det(n_D,F_D-g n).
\tag{7}
\]

The second vector in (7) is nonzero because F_D is not parallel to
n. As n_D varies through any open interval, the second determinant
therefore vanishes only at isolated directions. Directions n_B
parallel to n are themselves isolated. Thus (6) has empty interior
in every product of allowed open intervals.

The two free parameters belong to distinct physical junctions. Indeed
the side-normal channel gives supporting values a and a+1 with

\[
       n\cdot q\le a\quad(q\in B),\qquad
       n\cdot q\ge a+1\quad(q\in D).
\tag{8}
\]

The applications of AB and AD lie in B and D respectively and
cannot be the same point. This establishes the independence needed
for the open-dense avoidance in (6), rather than assuming it from
the graph labels alone.

## 5. One finite compatible selection before the multiplier theorem

Prelist the finitely many physical assignments of A,B,U,D,L,
the two possible side-normal axes of U, and the S/D leaf types.
Retain every candidate with the declared physical unique-corner
mask and positive normalized ratios (2). Apply Lemma 1.1 to the
parallel degeneracies. For a remaining candidate with exactly one
free A-tip edge use the finite exclusion of Section 3; with two,
avoid the nonzero condition (6).

These restrictions can all be imposed simultaneously inside the
already permitted open normal intervals. At a four-square junction
keep the matched mirrored parameter for its two opposite pairs;
the two junctions in (8) are distinct, so their parameters remain
independent. All strict, nonradial and earlier finite open-dense
conditions can be retained.

No application mean is part of a new normal choice. All quantities
in (3)--(7) come from fixed physical circle corners, the radial leaf
direction, fixed side axes and the preassigned free normal variables.
Nothing is selected after multipliers are extracted.

Planar uncrossing preserves surviving point-edge normals and adds
only actual shared-side forces. Conic thinning only deletes atoms.
Every possible final candidate was prelisted, and the force-only
obstructions remain valid for its actual aggregate means. Therefore
the final selected certificate cannot have a free AB or AD point
edge in the entire physical unique/unique C4 mask.

## 6. Exact residual scope

In this circle mask both A-tip edges can now be taken to have actual
side-axis owners, with all shared applications retained. The
A/U-parallel family is separately excluded by
`FOUR_CYCLE_PARALLEL_BYPASS_EXCLUSION.md`. With A/U nonparallel,
the chart in which both oblique tips own their point contacts is
excluded by `FOUR_CYCLE_OBLIQUE_TIP_OWNER_EXCLUSION.md`.

The other A-owned/shared charts and the U-parallel-tip charts remain
open. Physical two-circle-corner tips also remain outside this force-
ratio selection theorem, since their variable corner-weight ratio
must not be replaced by a fixed resultant direction. No whole cell
or unrestricted nine-square closure is claimed.

No Lean compilation, CI, numerical pose grid or omitted completion
square is a premise of this argument.
