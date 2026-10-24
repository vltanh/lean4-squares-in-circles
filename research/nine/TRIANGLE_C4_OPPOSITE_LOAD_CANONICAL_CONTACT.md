# The opposite-load C4 attachment has actual bypass contact at the canonical minimizer

**Status: complete whole-orbit canonical reduction; root and separate
independent full hand audits passed.** Choose a nine-square radius
minimizer that also minimizes the sum of squared center norms among all
radius minimizers. This is the same canonical choice already used in
FOUR_CYCLE_SECONDARY_CONTACT_REDUCTION.md. Work in
\[
                   \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
\tag{1}
\]
Suppose its selected positive component is
\[
                  H-A-U-C-H,\qquad H-X-Y-H,
\tag{2}
\]
with exact positive block loads A,C. The true degrees are four at H,
two at each of A,U,C,X,Y. A,C,X,Y are positively circle-loaded;
U has zero circle load; H is physically circle-clear. All three
remaining physical squares are arbitrary and retained.

**Theorem.** In a compatible selected certificate, H is oblique to U,
H and U physically touch, and the two H/A,H/C intersections are
singletons. The physical HU contact is not assigned positive stress.
All original channel means and all physical A/C masks remain.

## 1. A negative-pressure actual neighbor bounds the entire root center

Let M=F_X+F_Y be the actual circle-force sum of the whole attached
triangle. Its degree-two tips give c_H.M>0. Summing every genuine
component force equation therefore gives
\[
                  M+F_A+F_C=0,
                  \qquad c_H\cdot(F_A+F_C)<0.
\tag{3}
\]
Some actual circle corner z of A or C, with positive original weight,
thus satisfies c_H.z<0. This is also the premise supplied by
END_TRIANGLE_RADIAL_NEIGHBOR_OBSTRUCTION.md, which shows that this
neighbor is physically unique-corner. The next estimate needs only
the actual corner and the physical contact.

Choose any contact p of that neighbor with H. Unit-square diameter
and circumradius give
\[
                     |z-c_H|
                   \le |z-p|+|p-c_H|
                   \le\sqrt2+\frac1{\sqrt2}
                   =\frac3{\sqrt2}.
\]
Consequently
\[
               R^2+|c_H|^2<|z-c_H|^2\le\frac92,
               \qquad |c_H|^2<\frac92-R^2<1.
\tag{4}
\]
For every unit direction e the corresponding lower support obeys
\[
                 \min_{p\in H}e\cdot p
                   =e\cdot c_H-H_H(e)
                   \le |c_H|-\frac12<\frac12.
\tag{5}
\]
No actual triangle force or occupied square has been replaced by a
radial leaf. The bound follows from the whole four-load force sum.

## 2. The whole C4 hole is empty without a leaf premise

The winding and area proof of FOUR_CYCLE_LEAF_HOLE_EMPTY.md,
Sections 1--2, uses only an actual selected four-cycle and its four
interior-disjoint unit bodies. Any additional unit on its bounded
side forces the aligned four-neighbor cross. Its cycle applications
are the endpoints of one inward side of each ring unit. The proof
includes all contact coincidences and limiting physical embeddings.

Here U has exact degree two and zero circle load. Its two opposite
forces and torque require its application difference to be parallel
to their common channel normal. In the aligned cross this difference
is a side vector, so both channel normals are side-axis normals at
point-only vertex/vertex contacts. They fail the selected strict
convention. This is precisely the leaf-independent argument of that
source's Section 3.

Thus no additional unit occupies the bounded C4 region. This applies
to the actual units X,Y as well as all three completion units. It
does not delete their occupied geometry or their real H forces.

## 3. A positive transverse gap gives an allowed inward translation

UNIT_BYPASS_NORMAL_CHANNEL.md gives a side-normal transmitter and
transverse separation. Rotate and reflect about the fixed circle
origin so that
\[
 \begin{split}
 U&=[X_0-g-1,X_0-g]\times[Y_0,Y_0+1],\quad g\ge0,\\
 H&\subseteq\{x\ge X_0\},\quad \min_{p\in H}p_x=X_0,\\
 A&\subseteq\{y\le Y_0\},\qquad
 C\subseteq\{y\ge Y_0+1\}.
 \end{split}
\tag{6}
\]
H's vertical projection contains [Y_0,Y_0+1]. Equation (5) gives
X_0<1/2. If g>0, all four cycle contacts are distinct and the physical
center/contact loop is Jordan. At every height strictly between the
channel boundaries, the U and H portions cross exactly once, while
the A and C portions are absent. The full strip
\[
                     (X_0-g,X_0)\times(Y_0,Y_0+1)
\tag{7}
\]
lies on the bounded side. This is the complete slice argument of
FOUR_CYCLE_SECONDARY_CONTACT_REDUCTION.md, Section 3; its only
geometric premises are exactly (6).

The connected open interior of every other square lies on one side
of the loop. Section 2 rules out its lying inside. None has an interior
point in (7). Translating U by a sufficiently small t e_x, 0<t<g,
therefore preserves all nonoverlaps: U stays between the A,C supporting
half-planes, left of H, and its newly occupied interior is wholly in
(7). Its center first coordinate remains strictly negative, since
\[
                X_0-g-\frac12+t<X_0-\frac12<0.
\tag{8}
\]
For its fixed frame the maximum corner norm squared is
(|c_{U,x}|+1/2)^2+(|c_{U,y}|+1/2)^2. It strictly decreases, as does
the squared center norm. Thus the move stays in the same radius disk,
even if U has an unused physical circle contact, and contradicts the
canonical secondary minimum. Therefore g=0 and H physically touches U.

## 4. The full physical singleton and owner domain

FOUR_CYCLE_PARALLEL_BYPASS_GENERAL_EXCLUSION.md excludes H parallel
to U uniformly in every additional force at H. In the remaining frame
write
\[
 \begin{split}
 U&=[X_0-1,X_0]\times[Y_0,Y_0+1],\\
 P&=(X_0,y_0),\qquad Y_0<y_0<Y_0+1,\\
 v&=(a,b),\quad w=(b,-a),\quad a,b>0, a^2+b^2=1,\\
 H&=P+[0,1]v+[0,1]w.
 \end{split}
\tag{9}
\]
P is H's unique leftmost vertex. Its height is strictly inside the
channel because H's projection covers that interval and each of the
two vertical distances from P to an extreme vertex is less than one.
Thus HU is a vertex/relative-side-interior physical contact with
U-owned normal e_x. Both HUA and HUC are physical triangles, even
though HU has zero stress.

The triangle nonobtuse-normal lemma gives the actual owner signs
\[
 \begin{array}{c|c}
 \text{owner of the H-tip edge}&\text{necessary sign}\\ \hline
 H\text{ at HA or HC}&n_x\le0\\
 A\text{ at HA}&n_y\le0\\
 C\text{ at HC}&n_y\ge0.
 \end{array}
\tag{10}
\]
All normals here point out of H. These are exactly the physical
calculations in the earlier canonical source, Section 5.

Neither HA nor HC can have positive shared length. A shared HA normal
would have to be -v, since the other negative-x H face lies above
y_0>Y_0. The aligned neighbor would have the form
\[
                A=P-v+\tau w+[0,1]v+[0,1]w,
                \qquad -1<\tau<1.
\]
Its unique top vertex P+tau w must have height Y_0. Thus
tau=(y_0-Y_0)/a>0, and its first coordinate X_0+tau b exceeds U's
right support X_0. It cannot touch U. The reflected upper calculation
is identical. This is the complete earlier Section 6 argument, with
its leaf-independent premises now established.

Hence both H-tip contacts are singleton. A side-owned singleton is
a vertex/relative-side-interior contact; if both units owned its axis,
there would instead be positive shared length. Every AU/UC channel
mean remains arbitrary.

## 5. Exact canonical scope and compatible selection

The canonical packing is chosen before every normal choice and stress
extraction. The finite generic conditions of the general parallel
theorem can be imposed together with all previous ones. The resulting
strict certificate gives the empty-hole argument, and a positive gap
would contradict the already fixed secondary minimum. No normal is
changed afterward and no positive HU multiplier is inferred.

The reduction covers the entire AC orbit of C2.34.b0, all physical
masks, the full attached triangle and all three completion squares.
It is a canonical lower-bound reduction, not an exclusion of every
noncanonical positive core or an equality classification. The remaining
singleton owner/mask contradictions are separate. No Lean compilation,
CI or numerical premise is used.
