# The entire C5 branch of the five-body biconnected cell is closed

**Status: complete hand assembly; root and separate independent full hand
audits passed both metric orbit proofs, the domain theorem and this assembly.**

Work with a hypothetical nine-unit radius minimizer in
\[
                     \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},
\tag{1}
\]
and its selected physical planar certificate. Keep the existing strict
point-normal convention, compatible diagonal avoidance, all actual
shared-side means, every individual circle-corner weight and all physical
zero-weight contacts. The lower endpoint in (1) remains the separate
n=8 import of `LOWER_WINDOW_FROM_EIGHT.md`.

**Theorem.** The unique selected positive component cannot be exactly a
five-cycle. Thus the entire C5 graph branch of C1.5.b0 is closed. No
completion square is moved or discarded by either new metric proof.

## 1. Exhaustive load cover

The earlier global tree/two-load conclusions already exclude a component
with fewer than three loaded bodies in this radius proof. The exact
five-body graph/load reduction in
`FIVE_BODY_BICONNECTED_REDUCTION.md`, Section4.1, therefore leaves only:

| Positive loaded set | Exact cycle form | Complete exit |
| --- | --- | --- |
| Three bodies | T-U-B-C-V-T, precisely T,B,C loaded | `FIVE_CYCLE_THREE_LOAD_EXCLUSION.md` |
| Four bodies | A-B-C-D-U-A, precisely A,B,C,D loaded | `FIVE_CYCLE_FOUR_LOAD_EXCLUSION.md` |
| All five bodies | Every cycle vertex physically touches the circle | The physical boundary-cycle theorem excludes C5. |

The three-load row is one dihedral orbit: connectedness of the loaded
physical noncontact graph forces exactly one positive edge among its
three loaded vertices. The two unloaded vertices are nonadjacent. The
four-load row likewise has a single orbit. Physical circle contacts with
zero multiplier are retained independently of these positive-load labels.

## 2. The complete three-load exit

The isolated load T could a priori have parallel pair forces, because
both of its cycle neighbors are unloaded.
`FIVE_CYCLE_THREE_LOAD_PARALLEL_EXCLUSION.md` excludes that entire
alternative first, with both radial masks and every genuine mean.

The nonparallel proper-concurrence lemma in
`FIVE_CYCLE_FORCE_POLYGON_DOMAIN.md`, Section1, then applies to T
without a boundary-neighbor hypothesis. B and C do have a boundary
neighbor. Their proper concurrences form a strictly convex radial
triangle containing zero, with two exact transmitter reserves.

`FIVE_CYCLE_THREE_LOAD_EXCLUSION.md` treats each reserve1 orsqrt(2)
in full. If theta=acos(9/25), every transmitter's outward consecutive
center angle is less than pi-theta/2, while the direct BC angle is
less than theta. The three consecutive angles therefore sum to less
than2pi, contradicting their complete circular order. The diagonal
case uses the proved strict concavity of the actual axis-aligned
boundary-center curve, not a sampled orientation table.

This exit covers both remaining side/side and side/diagonal families
and also independently covers double-diagonal transmission after the
parallel-T reduction. No common frame is assigned to a side-normal
transmitter's loaded neighbors. Radial two-corner concurrences may lie
outside their squares throughout the argument.

## 3. The complete four-load exit

Every loaded vertex in this orbit has a boundary neighbor and hence
a proper nonparallel concurrence. The four concurrences form a strictly
convex quadrilateral containing zero.

`FIVE_CYCLE_FOUR_LOAD_EXCLUSION.md` proves that both endpoint centers
have nonnegative signed height relative to the horizontal axis through
the circle origin, with the transmitter line at strictly positive height. It retains the aligned zero-height,
two-circle-corner endpoint. The three direct boundary contacts force
these two centers to have an almost-antipodal upper angle. A side-normal
transmitter contradicts their actual center-distance bound; a diagonal
transmitter contradicts their exact horizontal center displacement and
actual circle equations. Both reserve widths and all shared means are
therefore excluded.

## 4. Exact scope

The new three- and four-load arguments are direct selected-core
exclusions, strict at both endpoints of (1). They use no secondary
minimizer, no dilation or sliding of the four extras, no deletion of a
positive chord and no normal choice made after obtaining multipliers.
All selections used by their prerequisites precede the common physical
certificate. Aggregation retains actual contact means.

This theorem applies to the entire positive component C5. A five-cycle
appearing as a subgraph of a house, fan, larger block or attached graph
can have additional positive forces at its vertices; those cases do
not inherit the degree-two concurrence equations used here. The house
and four-load fan branches of C1.5.b0 remain separate obligations.
The coarse C1.5.b0 cell is not declared closed by this C5 theorem.

The sharp radius theorem, its remaining larger components and equality
classification remain broader goals. No Lean compilation or CI is a
premise or a reported validation of this hand assembly.
