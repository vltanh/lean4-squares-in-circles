# Table-free quarter-word selection and the E-sign normalization

## Theorem

Let an eight-unit-square packing have squared containing radius at most
\(Q=9789/2500\). Apply the central-core, boundary-cycle, and
frame-concentration reductions. Up to a cyclic relabeling and a plane
reflection with reversal of cyclic order, its exterior quarter word is
\[
                         (0,1,0,1,0,1,1).                 \tag{1}
\]
Its seven roles may be named \((H,G,A,B,T,D,E)\). The remaining
reflection symmetry permits \(u_E\le0\), where \(u_i\) is the signed
own-frame tangent coordinate. All original separating-axis ties and
nearest-axis ties remain covered.

This closes the word-selection gate G2. It does not assert the other
candidate tangent cuts or any mismatch contraction.

## 1. Inputs already proved without tables

[HAND_EXTERIOR_FRAME_CONCENTRATION](../HAND_EXTERIOR_FRAME_CONCENTRATION.md)
provides physical center gaps \(\delta_i\), real frame lifts
\(\theta_i\), and their strict bounds
\[
 \delta_i>19/25,\qquad \sum_{i=0}^6\delta_i=2\pi,
 \qquad \max_i\theta_i-\min_i\theta_i=D<7/10.               \tag{2}
\]
The frame theorem's central-band and pair-geometry replacements are the
ones on the table-free hand path. In particular the gap in (2) does
**not** import the four Bernstein rows in Section 1 of the historical
`SEVEN_QUARTER_WORDS.md`. The integer argument below starts directly
from (2) and rederives its finite classification.

The fixed-axis boundary cycle has each unsigned state on the complete
core side/corner or the outer circle at \(Q\). Its true original forward
separators are preserved. No restriction on the seven radial kinds is
assumed. The chosen own-frame representation and its label are retained
consistently at both incident edges.

## 2. Quarter increments and the gap constraints

Choose increasing center-argument lifts \(\beta_i\), with
\(\beta_{i+7}=\beta_i+2\pi\), and periodic real frame lifts
\(\theta_{i+7}=\theta_i\). For each vertex choose a nearest square axis,
so that, for an integer \(m_i\) and \(\alpha_i\in[-\pi/4,\pi/4]\),
\[
 \beta_i+\alpha_i=\theta_i+m_i\pi/2.
\]
Resolve a nearest-axis tie once, and extend by
\(m_{i+7}=m_i+4\), \(\alpha_{i+7}=\alpha_i\).
Set
\[
 k_i=m_{i+1}-m_i,\qquad \epsilon_i=\theta_{i+1}-\theta_i,
 \qquad \phi_i=\epsilon_i+k_i\pi/2.
\]
Then
\[
 \delta_i=\phi_i+\alpha_i-\alpha_{i+1},\qquad
                  \sum_{i=0}^6k_i=4.                     \tag{3}
\]
The other six lower gap bounds in (2) give
\[
                 \delta_i<2\pi-114/25.                    \tag{4}
\]
If \(k_i\le-1\), (3) would imply \(\delta_i<D<.7\), contradicting
(2). If \(k_i\ge3\), it would imply
\[
 \delta_i>\pi-.7>2\pi-114/25,
\]
contradicting (4). The second inequality uses only
\(\pi<22/7<193/50\). Hence every \(k_i\) belongs to \(\{0,1,2\}\).

There are no three consecutive zeros. Such a run would give, by
summing (3),
\[
 \delta_i+\delta_{i+1}+\delta_{i+2}
 =\theta_{i+3}-\theta_i+\alpha_i-\alpha_{i+3}
 <7/10+\pi/2<57/25,
\]
while (2) gives the reverse strict inequality. Finally there are at
most one 2: two would use the whole sum 4 and leave five zeros in two
cyclic runs, one of length at least three.

## 3. A direct exhaustive enumeration, not a search

If there is no 2, there are four ones and three zeros. The zero runs
in the four cyclic gaps between ones have lengths at most two and
sum three. Their length multisets are
\[
                        (1,1,1,0),\qquad(2,1,0,0).
\]
The first has one arrangement under rotation and reversal. In the
second, the runs of lengths two and one are adjacent or opposite;
these give its two arrangements. Thus there are exactly the three
binary words
\[
                    0101011,\quad0010111,\quad0011011.
\]
If there is one 2, there are two ones and four zeros. The three zero
runs have multisets \((2,2,0)\) or \((2,1,1)\). For either multiset,
the exceptional run lies between the two ones or touches the unique 2;
reflection identifies the two touching choices. These are exactly
four further words. The complete list is therefore
\[
 0010012,\quad0010102,\quad0010201,\quad0011002,
 \quad0010111,\quad0011011,\quad0101011.                    \tag{5}
\]
Rotation is cyclic relabeling. Reflection of the plane followed by
reversal of center order reverses the edge word and negates local
signed angles while preserving the physical geometry. Thus the
classification acts on actual packings and their original axes.
No replacement of an original separator by a selected owner occurs.

## 4. Every other word has a strict whole-cycle contradiction

### 4.1. All four words containing a 2

Use the common marker functions
\[
 L_O=-9/100+(13/200)a+(203/200)b,
 \qquad
 L_C=(73/10)(7/12-a)+(291/250)b,
\]
and signed vertex label \(\ell_i=\sigma_iL_{K_i}(a_i,b_i)\).
The complete pair theorems
[quarter zero](../QUARTER_ZERO_ALL_BOUNDARY_STATES_HAND_PROOF.md),
[quarter one](../QUARTER_ONE_ALL_BOUNDARY_STATES_HAND_PROOF.md), and
[quarter two](../QUARTER_TWO_ALL_BOUNDARY_STATES_HAND_PROOF.md)
prove respectively
\[
 \phi_i+\ell_i-\ell_{i+1}>
             391/400,\quad157/200,\quad163/200.             \tag{6}
\]
Their domains include all four radial orders, both local signs, all
original forward axes, and the complete relevant angle intervals.
The physical gap and forward-axis inputs are supplied by Section 1.
Their finite lists refer to intrinsic geometric regimes and fixed
Taylor endpoint arithmetic; no numerical state/angle cover is used.
The common coefficients ensure that the same label cancels at a vertex.

There are four zeros, two ones, and one two in each word in this
class. Summing (6), as in
[COMMON_QUARTER_TABLE_AND_FOUR_WORD_EXCLUSIONS](../COMMON_QUARTER_TABLE_AND_FOUR_WORD_EXCLUSIONS.md),
gives
\[
 2\pi>4(391/400)+2(157/200)+163/200=1259/200.
\]
But
\[
                   1259/200-44/7=13/1400>0,
 \qquad 2\pi<44/7.
\]
This excludes the entire class, with every radial assignment.

### 4.2. The two residual binary words

[HAND_SHORT_WORD_COMPLETE_WITHOUT_TABLES](HAND_SHORT_WORD_COMPLETE_WITHOUT_TABLES.md)
proves the complete 0010111 exclusion. It supplies all 304 original-axis
alternatives from the table-free core/core, mixed, and outer components,
with primary-zero branches discharged by the earlier closed-tour theorem.
The edge-2 cost is strictly greater than \(359/400\), and the other six
are strictly greater than \(17953/20000\). Exact cancellation gives
\[
 2\pi>31417/5000=710/113+121/565000>2\pi,
\]
a contradiction.

[HAND_WRONG_0011011_COMPLETE_WITHOUT_TABLES](HAND_WRONG_0011011_COMPLETE_WITHOUT_TABLES.md)
proves the complete 0011011 exclusion with the corresponding complete
core/core, mixed, and outer dependency map. Every edge cost is strictly
greater than \(17953/20000\), yielding
\[
 2\pi>125671/20000=710/113+823/2260000>2\pi.
\]
Both arguments use the elementary Machin-series bound \(2\pi<710/113\).
They do not import candidate cuts or mismatch thresholds, and their
actual-cycle use of the zero-primary theorem depends on G1 alone.
Thus they are noncircular inputs to this word-selection theorem.

The six exclusions leave precisely (1). Their strict reserves also
show that none of the excluded words contributes an equality packing.

## 5. Named candidate roles and the remaining reflection

Name the vertices in the cyclic order
\[
                       (H,G,A,B,T,D,E)=(0,1,2,3,4,5,6).
\]
Subtract the common integer \(m_0\) from the quarter representatives.
The selected word then gives
\[
                       (m_0,\ldots,m_6)=(0,0,1,1,2,2,3).
                                                               \tag{7}
\]
No radial kind or sign except the forthcoming E normalization is
asserted by this naming.

For an unsigned own-frame center \((a,b)\) and local sign \(\sigma\),
put \(u=\sigma b/a\in[-1,1]\). Reflect the plane and assign the new
vertex \(i\) to the reflected old vertex \(5-i\pmod7\). The new
edge increment is \(k'_i=k_{4-i}\). Direct substitution into (1) gives
\(k'=k\). The role order becomes \((D,T,B,A,G,H,E)\), and
\[
                            u'_i=-u_{5-i}.
\]
In particular E is fixed and its signed tangent is negated. Choose
between this representation and the original so that
\[
                                u_E\le0.                  \tag{8}
\]
At \(u_E=0\), either representation is admissible; ties were already
retained. The transformation is an isometry and a relabeling, not a
motion or a new contact hypothesis.

The same word conclusion applies to a boundary cycle at a smaller
ceiling \(5/2\le q<Q\) by the unconditional fixed-ray expansion
in Section 2 of
[the fixed-ceiling transfer theorem](../HAND_FIXED_CEILING_TRANSFER_WITH_AUTOMATIC_TERMINAL.md).
That expansion fixes core centers and preserves every initially feasible
signed axis, center ray, physical frame, and quarter increment.
The sign normalization likewise depends only on the preserved own-frame
center direction.

## 6. Gate boundary

G2 is now closed by the explicit finite classification (5), the four
common-word exclusions, and the two complete table-free binary-word
assemblies. The reflection-only E-sign component of G3 is also proved.
The remaining desired inequalities
\[
 -4/5<u_G<-1/20,\qquad1/20<u_T<4/5,
 \qquad u_H>1/2,\qquad u_D<-1/2
\]
are not inferred from the word or from (8). They remain capture targets,
as do the coarse, middle, and final mismatch contractions. No conditional
sharp terminal theorem is applied before those separate inputs are proved.
