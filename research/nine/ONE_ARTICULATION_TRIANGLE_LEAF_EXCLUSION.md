# A common articulation cannot support only triangle petals and radial leaves

**Status.** Complete uniform hand core exclusion; root and separate independent full hand audits passed. The theorem applies to every component size
allowed by the nine-square packing. All physical circle masks, actual
contact means, additional zero-weight contacts and completion squares
are retained. It makes no degree-two inference at an inner vertex of a
fan or house.

Work in the declared window
\[
                      \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
\tag{1}
\]
Use the common selected necessary physical certificate, including the
compatible pre-extraction conditions of BOWTIE_CELL_CLOSED.md,
Section 1.

## 1. The entire graph family

Let a connected positive component have one distinguished body A and
otherwise consist exactly of

* `k>=1` pairwise distinct pairs `B_j,C_j`, each forming the positive
  triangle `A-B_j-C_j-A`; and
* `l>=0` pairwise distinct leaves `L_i`, each joined positively only
  to A.

There are no other positive edges incident to these bodies. Thus each
triangle tip has exact positive pair degree two, each leaf has degree
one, and A has degree `2k+l`. Extra physical contacts can have zero
multiplier and remain present. The theorem is uniform in k and l;
within a nine-square packing, of course `1+2k+l<=9`.

**Theorem.** No selected positive component in (1) has this graph.

Every leaf is loaded, since a single nonzero pair force cannot balance
without a circle force. Every triangle tip is loaded as well: if its
circle load were zero, its two positive pair forces would be opposite,
placing its two neighbors beyond opposite supporting lines of a unit
square. Those neighbors could not physically touch, contrary to the
third triangle edge.

The articulation A is physically circle-clear. If it touched the circle,
then A,B_1,C_1 would be three pairwise touching boundary units, excluded
by CIRCLE_CONTACT_ANGULAR_ORDER.md. In particular A has no circle load.

## 2. Each entire triangle contributes strictly positive pressure

For each triangle set
\[
 F_{B_j}=2\sum_z\lambda_{B_j,z}z,
 \qquad
 F_{C_j}=2\sum_z\lambda_{C_j,z}z,
 \qquad M_j=F_{B_j}+F_{C_j}.
\tag{2}
\]
All corner weights are nonnegative and each tip's total is positive.
The complete end-triangle pressure theorem in BOWTIE_CELL_CLOSED.md,
Section 2, gives
\[
                              c_A\cdot M_j>0.
\tag{3}
\]
Its hypotheses allow A to have further positive neighbors. They require
only the exact degree-two tips B_j,C_j, which the present graph has.
Its full owner/free/shared interface cover and physical circle-mask
cover therefore apply without splitting a higher-degree body.

The finite normal conditions in that theorem are prelisted for every
physical end-triangle candidate in the whole packing. Hence all k
applications of (3) use the same necessary certificate; they do not
select different normals for different petals.

## 3. Every radial leaf contributes strictly positive pressure

The radial bridge-and-leaf theorem classifies each L_i as radial S or
radial D, with its actual application and mean retained. Write its
positive total circle force as F_i.

If L_i is radial S, it has two physical circle corners. Because it
physically touches A, RADIAL_BOUNDARY_NEIGHBOR_PRESSURE.md gives
\[
                              c_A\cdot F_i>0.
\tag{4}
\]
That theorem permits either individual corner weight to vanish and does
not assume an equal-weight circle resultant.

If L_i is radial D, let e_i be its outward radial direction and let
\[
                          r=R-\sqrt2.
\]
Its inner vertex is `p_i=r e_i`, its circle corner is `R e_i`,
and its only pair force is parallel to e_i. The selected strict
nonradial convention at off-origin point-only vertex pairs makes
p_i a relative-side-interior support point of A. In particular A's
support side has outward normal e_i and
\[
                          c_A\cdot e_i=r-\frac12.
\tag{5}
\]
There is no replacement of a point normal by an axis: (5) is the
already proved radial-D leaf classification in the selected certificate.

The lower endpoint in (1) gives
\[
          r>\frac{11}{20}>\frac12,
\]
using `sqrt(2)<57/40`. Since `F_i=2lambda_i R e_i` with
`lambda_i>0`, equation (5) proves
\[
                    c_A\cdot F_i
                      =2\lambda_i R(r-\tfrac12)>0.
\tag{6}
\]
This covers every radial leaf type and every physical corner-weight
split allowed by the leaf theorem.

## 4. The global force contradiction

Sum the actual force equations of every body in the component. All
internal pair forces cancel. A is clear, and the displayed tips and
leaves are all remaining bodies, so
\[
                   \sum_{j=1}^{k}M_j+\sum_{i=1}^{l}F_i=0.
\tag{7}
\]
Taking its scalar product with c_A contradicts (3), (4) and (6).
There is at least one strictly positive summand because k>=1.
This proves the entire graph-family exclusion.

The proof does not require an exterior-capacity estimate or a secondary
minimizer and moves none of the other physical squares. It includes
the previously treated triangle, triangle-with-leaves and bowtie
examples, and also all larger components whose triangular blocks and
leaf edges share this one articulation.

It does not include a path fan: that graph's inner path bodies have
positive degree three and belong to two triangles. Their circle forces
cannot be split into separate degree-two tip forces without a further
proof. Nor does it include chains of distinct articulations or attached
larger cyclic blocks. Those remain separate whole-component obligations.

No numerical inference, Lean compilation or CI is used.
