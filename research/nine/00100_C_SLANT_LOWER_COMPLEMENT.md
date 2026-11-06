# The lower-G complement: a complete hand table and nonpositive-D C-slant

This chapter removes the G-order dependency from the nonpositive-D
C-slant proof. Its inputs are the physical foundation, the
[primary-axis chapter](00100_C_SLANT_PRIMARY_AXES.md), and the common
rational frame and row definitions of
[the secondary-axis chapter](00100_C_SLANT_SECONDARY_AXES.md).
It does not import the archived G-order or C-slant results.

The complete finite arithmetic is supplied as plain text:

* [all 288 root cases](tables/c-slant-lower-roots.tsv);
* [all 1,039 terminal combinations and their complete subdivisions](tables/c-slant-lower.tsv).

Every coefficient is specified below or in the common row definitions.
There is no encoded proof packet, external certificate dependency,
numerical optimizer or saved success report in the mathematical argument.
The unrestricted nine-square theorem and all whole-original closures
remain open.

## 1. Fixed caller and the remaining complement

Use exactly the normalized original-nine `001/00` caller of the two
preceding chapters: all independent original frames, physical pairs and
corners in the closed Q-disk; AB,BC,EF,FG actual; CD strictly weak
and cone; d=x_D-x_C>=v=y_D-y_C>=2/3; and D's canonical tilt
nonpositive. Suppose for contradiction that

\[
                         y_C+(7/8)x_C\ge-7/32.                \tag{1}
\]

The primary-axis chapter, without any G-order input, reduces the C/D
separator to these three complete sign/owner cases:

* C nonpositive, owner C's positive secondary axis;
* C nonpositive, owner D's positive secondary axis;
* C nonnegative, owner D's positive secondary axis.

The secondary-axis chapter already excludes y_G>y_D under exactly
these hypotheses. This chapter proves the entire closed complement

\[
                              y_G\le y_D.                     \tag{2}
\]

In particular equality of the two heights is not discarded.
We use the localization and cap inequalities in that chapter's
Section 2 through its equation (4). Their derivations precede and do
not use the G-order assumption. None of its positive D/G height
clearances or G-left-of-D conclusions is imported here.

## 2. The C/G incircles give an eight-case rational union

Let X=x_G-x_C, Y=y_G-y_C. The original C and G contain disjoint
open radius-one-half disks, so X^2+Y^2>=1. Therefore at least
one of these eight closed linear inequalities holds:

| Octant index | Necessary alternative |
|---:|---|
| 0 | X>=12/13 |
| 1 | -X>=12/13 |
| 2 | Y>=12/13 |
| 3 | -Y>=12/13 |
| 4 | X+Y>=17/13 |
| 5 | X-Y>=17/13 |
| 6 | -X+Y>=17/13 |
| 7 | -X-Y>=17/13 |

Indeed, if all eight fail, (X,Y) lies strictly inside the octagon
|X|<=12/13, |Y|<=12/13, |X|+|Y|<=17/13. Its vertices are
the sign changes and coordinate swaps of (12/13,5/13), each of
squared norm one. Convexity of the squared norm, with strict
convexity along each edge, puts every strictly interior point at
squared norm less than one. This contradicts the original incircles.

This is a necessary-condition union, not an assertion that incircle
separation suffices for physical square nonoverlap. The complete
original physical pairs remain in the caller.

## 3. All usable D/G normals now point upward from G toward D

Put Delta_x=x_G-x_D and Delta_y=y_G-y_D<=0. The previously
proved bounds give -1459/1728<Delta_x<11/60, hence
|Delta_x|<1. An actual unit normal from G toward D with
nonpositive vertical component has projection at most
|Delta_x|<1, below the physical threshold R>=1.

Thus every actual separator toward D has positive vertical component.
For D's negative tilt the two possibilities are -u_D and v_D;
for negative G they are -u_G and v_G; for positive G they are
u_G and v_G. Each original owner is retained separately. At zero
tilt a horizontal option is impossible by the same strict bound;
keeping its empty endpoint in a larger root does no harm.

There are four owner/axis choices in each G-sign root. For a
secondary axis the horizontal component of D-G can have either
sign, and both closed alternatives are retained. No such sign
choice is needed for a primary axis.

## 4. Complete row recipe for this table

Keep exactly rows 0--121 of the secondary-axis chapter. These use
only original corner containment, center bounds, the original cap
load/transfer, the original cone and insets, and (1).
Keep row 123, its selected C/D secondary-axis row, unchanged.
The remaining rows are replaced as follows.

Row 122 is Delta_y<=0, from (2).

Let O be the selected D/G owner, and let s_O be its canonical
sign. Put F=R^-_{DG}/A_O, with all rational frame quantities
defined by (9)--(10) in the secondary-axis chapter.

For a primary axis, row 124 is

\[
                       s_O Delta_x+t_O^+ Delta_y\le-F.         \tag{3}
\]

To verify it, the original upward normal toward D, before unit
normalization, is (s_O,t_O). Its projection on D-G is
-s_O Delta_x-t_O Delta_y. Since -Delta_y>=0, replacing
t_O by t_O^+ enlarges this projection. Equation (3) is the
resulting necessary inequality.

For a secondary axis the root gives epsilon in {-1,+1}, meaning
epsilon(x_D-x_G)>=0. Define

\[
 p=\begin{cases}
 t_O^+,&s_O=-1,\ \epsilon=+1,\\
 t_O^-,&s_O=-1,\ \epsilon=-1,\\
 -t_O^-,&s_O=+1,\ \epsilon=+1,\\
 -t_O^+,&s_O=+1,\ \epsilon=-1.
 \end{cases}
\]

Row 124 is then

\[
                              p Delta_x+Delta_y\le-F.          \tag{4}
\]

The actual unnormalized normal is (-s_O t_O,1). On the
selected horizontal sign, choosing p as above gives an upper
bound for its projection on D-G. This proves (4) over the whole
closed angle box. Row 126 is epsilon Delta_x<=0, the selected
closed sign condition. Primary-axis roots have no row 126.

Finally row 125 is -n\cdot(c_G-c_C)<=-q, where (n,q) is the
selected row of the eight-case octagon in Section 2. These are
the only C/G constraints needed in this finite proof. No frame
of C or G has been replaced by a new packing object.

All row indices are thus fixed: the common 0--121 and 123,
the changed height row 122, the selected physical row 124,
the octagon row 125, and the optional sign row 126.

## 5. Every terminal is an explicit positive rational contradiction

The [terminal table](tables/c-slant-lower.tsv) uses exactly the
same path notation and integer-weight convention as the
secondary-axis table. Start each magnitude interval at [0,5/12].
Each C0,D0,G0 or C1,D1,G1 takes the lower or upper closed
midpoint half of the indicated original's interval.

For weights w_j on rows A_j c<=B_j, put
a=sum_j w_j A_j, b=sum_j w_j B_j and W=sum_j w_j.
Every line prints a positive integer m satisfying

\[
                 -b-(91/60)\sum_{k=0}^5|a_k|
                                      \ge mW/100000>0.         \tag{5}
\]

The original center bounds imply a c>=-(91/60)sum|a_k|,
whereas the weighted sum gives a c<=b. Equation (5) is their
contradiction. All residual coefficients, including coefficients
of originals whose rows do not cancel, are paid in this inequality.

No row depends on a positive D/G height difference, the G-order
theorem or the C-slant conclusion. In particular the changed
height row is never accidentally the row from the other table.

## 6. Complete cover and unconditional nonpositive-D C-slant

The 288 roots comprise the three C-sign/C-D-owner cases, two
G signs, six D/G owner/axis/horizontal-sign cases, and all eight
C/G octagon alternatives: 3 times 2 times 6 times 8.
They are individually listed in
[the root table](tables/c-slant-lower-roots.tsv).

Each root's paths are a complete binary angle cover: every
nonterminal prefix has both closed midpoint halves of one original
interval as its two children. There are 751 internal splits and
1,039 terminal paths, with no unresolved child. Every terminal is
excluded by its displayed positive rational inequality (5).

This excludes all of (2). Therefore (1) forces y_G>y_D.
The complete secondary-axis table then excludes (1), while the
primary-axis chapter already excluded every other physical C/D axis.
This proves the hand/table theorem:

> In the normalized original-nine `001/00` domain, with nonpositive
> canonical D tilt and y_D-y_C>=2/3, one has
> **y_C+(7/8)x_C<-7/32**.

The proof is acyclic: assume the contrary half-plane, reduce C/D
axes, exclude the complete lower-G complement using this chapter,
then exclude the upper-G domain using the preceding table. The
archived G-order and C-slant forests are not inputs to this theorem.

Every original frame and contact face is retained. The other two
originals H,I remain physical members of the original caller; this
necessary-subsystem exclusion does not assume they were discarded
from a new packing. The theorem is a component of the full nine-square
proof, not a whole-mask or unrestricted packing theorem.

All table coefficients and positive integer multipliers are specified
in the manuscripts and the attached plain-text tables. Computation
found the combinations and checked their exact rational arithmetic;
the mathematical proof is the displayed finite cover and weighted
inequalities. No independent human review, Lean, Lake, CI or kernel
verification is claimed.

For the local validation boundary: reconstruction directly from the
manuscript's rational row definitions checked all 5,243 weighted leaves,
4,934 complete binary splits, 309 roots and 35,846 positive weight
occurrences across the two secondary-axis tables. The primary table's
67 rectangles were checked separately. These checks establish the
claimed finite arithmetic and coverage; the physical derivations above
remain part of the proof and are not replaced by a success report.
