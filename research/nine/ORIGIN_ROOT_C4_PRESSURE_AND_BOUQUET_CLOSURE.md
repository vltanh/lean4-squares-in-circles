# An origin-containing root has nonnegative C4 pressure: seven complete attachment families

Date: October 25, 2026.

**Status: accepted after independent complete source/scope review. See
REVIEW_ORIGIN_ROOT_C4_BOUQUET_CLOSURE_2026_10_25.md.**
The new scalar R0 theorem is independently reviewed in
REVIEW_ABC_R0_AND_COMPLETE_ASSEMBLY_2026_10_25.md. This manuscript does
not generate another scalar certificate. It supplies the missing
arbitrary-root join, and explicitly replaces the physical end-petal
input where the earlier ABC proof needed it.

Keep the original nine physical squares, the common compatible selected
certificate, and the closed window

    79/40 <= R <= sqrt(1105)/16.

No physical body, original force, actual mean, individual circle weight,
zero-stress physical contact or completion square is removed. Every
degree below means the true degree in the selected positive graph.

## 1. The local three-load pressure theorem

Suppose H--A--B--C--H is an actual positive cycle. A,B,C have true
positive degree two and positive total circle loads. H may have
arbitrary additional positive neighbors. Assume the actual closed
square H contains the circle origin O. Put

    S = F_A + F_B + F_C,
    F_T = 2 sum_(circle corners z of T) lambda_z z.

The individual lambda_z are their original nonnegative weights, and
the total on each of A,B,C is positive. Then

    c_H dot S >= 0.                                      (1)

This is a nonnegative block pressure, not a claim that each endpoint
circle force has nonnegative pressure. The circle origin may lie on
H's side or vertex. The theorem does not need a secondary minimizer.
It does need the same simultaneous local normal selections as the
complete ABC proof, discussed in Section 5.

### 1.1. Contradiction assumption and unchanged block equations

Assume c_H dot S<0. Sum only the actual A2/B2/C2 equations. Let n,m
be the original H-to-A and H-to-C normals, let mu,nu>0 be their
actual magnitudes, and let P,Q be their unchanged applications. Then

    S = mu*n + nu*m,
    mu*det(P,n) + nu*det(Q,m) = 0.                      (2)

These are force and origin-moment identities for the actual block.
No equation at H has been replaced by a degree-two equation.

The physical boundary path A--B--C has the complete cone identity

    F_B = a*F_A + b*F_C,       a,b>0.                  (3)

This is BOUNDARY_THREE_PATH_RESULTANT_CONE.md; its proof uses the
physical boundary order and original radial resultants. Combining
(3) with c_H dot S<0 gives a negative endpoint. A physically
two-circle-corner neighbor of H has strictly positive pressure by
RADIAL_BOUNDARY_NEIGHBOR_PRESSURE.md, including every individual
zero-weight limit. Therefore the negative endpoint is physically
unique. Exchange A,C if necessary to call its actual circle corner
z_A, so

    c_H dot z_A < 0.                                  (4)

This is a renaming of the actual cycle, not a new stress or motion.
Since O belongs to the actual unit H, every H point has norm at most
its diameter sqrt(2)<79/40<=R. Thus H is physically circle-clear
and its actual circle load is zero, including when O is a vertex.

Let M be the sum of all actual circle resultants in the same positive
component outside A,B,C. Whole-component balance gives

    M+S=0,             c_H dot M>0.                   (5)

M is an unchanged sum of original circle forces. It is used only as
that sum, never as a physical square, triangle or new force atom.

### 1.2. The parallel-root replacement is already proved at this scope

Apply ORIGIN_ROOT_POSITIVE_PRESSURE_THREE_LOAD_C4_NONPARALLEL.md with
the actual O in H, equations (2),(5), genuine A2/B2/C2 and arbitrary
additional forces at H. Its complete proof excludes both opposite
and equal root normals, every original mean and every circle mask.
Consequently n,m are nonparallel.

This substitution is essential. The older exact H4/petal parallel
proof used the physical petal's opposite-face bound to prove a
positive wall coordinate. That bound is not imported here. The
already accepted arbitrary-root version uses O in H to obtain
s>=0, then the actual two endpoint distances and y+w<=1 give

    1/4 < s < 1/2.

Its remaining wall calculations are local to H,A,B,C. This handles
the entire original H4 dependence in the parallel-root branch,
including O on the boundary of H. It is not sufficient merely to
delete the old petal from the statement of that branch.

## 2. The nonparallel negative-endpoint proof has a local scope

The following is a source-dependency lift of the completed ABC proof.
Its standing domain is precisely (2)--(4), the nonparallel n,m just
proved, the four physical squares and their actual equations.
The original total negative block pressure c_H dot S<0 is retained.

In this domain the only uses of the old HXY petal in the ensuing
negative-endpoint sources are:

1. to obtain (4) from a negative whole-block pressure;
2. to invoke the complete parallel-root exclusion;
3. to contradict a derived c_H dot S>=0 using the original total
   force balance and strictly positive outside pressure.

Here (4) is proved directly by (3), item 2 is replaced by Section 1.2,
and item 3 contradicts the standing c_H dot S<0 directly. None
asserts a fictitious smaller-component force equation. Physical
circle containment, H/B nonoverlap, all return-owner conditions and
the original middle B2 equation remain in every source.

### 2.1. Radial middle: every HA owner and both C masks

Use the complete owner/mask cover of
TRIANGLE_C4_RADIAL_MIDDLE_LOAD_EXCLUSION.md, with its Section 1
replaced by (3)--(4) and its Section 2 by Section 1.2 above.
Its actual nonparallel proofs have the following unchanged scope.

| Actual HA feature | Source calculations used | Local force/geometry input |
| --- | --- | --- |
| A-owned singleton or shared HA | NEGATIVE_UNIQUE_ENDPOINT_OWNED_CONTACT_DOMAIN.md; NEGATIVE_UNIQUE_ENDPOINT_OWNED_RADIAL_MIDDLE_EXCLUSION.md | A2, negative z_A, actual radial B, full HA mean and AB support; no H or outside equation |
| Genuinely free HA | NEGATIVE_ENDPOINT_FREE_SHARED_RADIAL_MODULE.md and the four FREE_NEGATIVE_C4_* return exclusions | True A2/B2 pin the full shared AB module; genuine C2 is used only for the applicable unique return; arbitrary H forces are retained |
| H-owned singleton HA | NEGATIVE_H_OWNED_ENDPOINT_RADIAL_MIDDLE_DOMAIN.md and its RADIAL_MIDDLE_RADIAL_RETURN, UNIQUE_RETURN_DOMAIN, UNIQUE_RETURN_OWNER and H_OWNED_RETURN continuations | A2/B2 and the full original two-corner weight interval; actual C2 where needed; the H-owned return uses only nonparallel root axes after Section 1.2 |

In particular FREE_NEGATIVE_C4_H_OWNED_RETURN_EXCLUSION.md explicitly
states arbitrary additional H forces, and the radial return source
uses no H force equation. The H-owned radial-middle return's old
exact-petal invocation supplied only its complementary parallel
case; the nonparallel contradiction is q/p>8 and q/p<54/7 from the
unchanged B2/C2 equations.

The high-radius radial-middle pressure comparison uses the full
original HA mean and endpoint geometry; it is not a theorem about
a fictitious B with one pair force. Both q intervals join at 17/4
and both individual radial weights retain their zero endpoints.
Thus radial B is impossible throughout this contrary domain.

### 2.2. Unique middle: every non-H-owned HA is excluded locally

The free-HA module forces B physically radial, already excluded.
If HA is A-owned, including a shared HA, the complete local owner
theorem forces a singleton outgoing AB in its strict northwest
corner cone. The remaining cover is:

| Actual feature | Complete source | Scope retained |
| --- | --- | --- |
| A-owned singleton HA | NEGATIVE_A_OWNED_UNIQUE_MIDDLE_RETURN_DOMAIN.md and NEGATIVE_A_OWNED_UNIQUE_MIDDLE_EXCLUSION.md | True A2/B2, negative z_A, actual H/C return and all C masks |
| Shared HA with B-owned AB | Section 5 shared-root extension of NEGATIVE_A_OWNED_UNIQUE_MIDDLE_EXCLUSION.md | Every actual HA mean; only H's original supporting half-plane is used |
| Shared HA with free AB | NEGATIVE_A_OWNED_SHARED_FREE_UNIQUE_MIDDLE_EXCLUSION.md | Local A/B or B/C virtual-work identities, genuine B2/C2 and every original shared mean; H and outside bodies have zero test velocity |

The return-domain source expressly imposes no assumption on H's
other forces or petal after recording its actual support. The
selection in the last row is local to the physical pair, its fixed
external applications and actual middle/end equations. Additional
forces at H contribute zero to those virtual-work tests.

Consequently HA is its actual H-owned singleton. The ordered
negative-corner frame and complete outgoing support fan follow
from Section 1 of
NEGATIVE_H_OWNED_ENDPOINT_RADIAL_MIDDLE_DOMAIN.md before its
radial-middle specialization. This argument uses only A2.

### 2.3. Every A-owned or shared outgoing side is excluded locally

The two possible A-axis outgoing features are the left inner side
and the upper side. Their full singleton and shared alternatives
are excluded by:

* NEGATIVE_H_OWNED_LEFT_SINGLETON_MIDDLE_EXCLUSION.md;
* NEGATIVE_H_OWNED_UPPER_AXIS_SINGLETON_MIDDLE_EXCLUSION.md;
* NEGATIVE_H_OWNED_SHARED_LEFT_MIDDLE_EXCLUSION.md;
* NEGATIVE_H_OWNED_SHARED_UPPER_MIDDLE_EXCLUSION.md.

The left family retains its full small/large-coordinate, low/high
radius and tilted/shared feature cover. Its H-owned return only
needs the two root axes to be nonparallel, supplied by Section 1.2.
The shared-left preselection tests the original A/B equations,
keeps every original shared mean and leaves H fixed.

The two upper families may first prove that the actual other
endpoint C also has negative H-pressure. Their reflected owner
exits use exactly Section 2.2, with A and C renamed; this lift is
therefore ordered and noncircular. Their final root moment is the
sum of the true A/B/C origin torques in (2), not H2 or H4 torque
with outside forces omitted. The only old parallel-root calls are
again replaced by Section 1.2.

Thus the entire contrary domain is reduced to the true B-owned
upper-left singleton AB, with unique B, negative unique A and
either physical C mask. No corner coordinate has been selected
artificially.

## 3. The whole upper-left return cover uses only this local domain

The full support fan has the near vertex, the strict far vertex,
and the minimum-f side, with the original physical B corners and
the actual shared/singleton distinction retained.

| Complete return family | Source or complete assembly | What is needed beyond the unchanged local equations |
| --- | --- | --- |
| Near BC vertex, either C mask | NEGATIVE_H_OWNED_UPPER_LEFT_NEAR_VERTEX_EXCLUSION.md | None; contradiction uses A/B geometry and actual B2 |
| Far BC, nonnegative ordinary vertical normal component | NEGATIVE_H_OWNED_UPPER_LEFT_NONNEGATIVE_VERTICAL_RETURN_EXCLUSION.md | Nonparallel root axes from Section 1.2 in the H-owned HC branch |
| Far BC, physical radial C, both B corners | REVIEW_ABC_FAR_RADIAL_AND_UUS_JOIN_2026_10_25.md and ABC_UPPER_LEFT_FAR_RADIAL_BLOCK_PRESSURE_EXCLUSION.md | Derived A/B pressure plus actual radial-C pressure gives c_H dot S>0; this directly contradicts the standing pressure assumption |
| Far BC, unique C, every B corner and HC owner/mean | REVIEW_ABC_COMPLETE_FAR_RETURN_2026_10_25.md and ABC_FAR_UNIQUE_NONPOSITIVE_TANGENT_RETURN_EXCLUSION.md | Nonparallel root axes; where the proof derives nonnegative total block pressure, use c_H dot S<0 instead of H4/petal balance |
| Minimum-f BC with physical radial C | NEGATIVE_H_OWNED_UPPER_LEFT_SIDE_RADIAL_SHARED_EXCLUSION.md and NEGATIVE_H_OWNED_UPPER_LEFT_SIDE_RADIAL_SINGLETON_EXCLUSION.md | The actual radial square, B2 force/moment and H support; no outside-body position |
| Genuinely shared minimum-f BC, unique C | ABC_UNIQUE_SHARED_SIDE_COMPLETE_EXCLUSION.md | Nonparallel root axes and the local negative-endpoint owner statements already lifted above |
| Strict B-owned minimum-f BC with opposite C circle corner | ABC_UNIQUE_SINGLETON_SIDE_OPPOSITE_CORNER_EXCLUSION.md | Original C2 sign, circle equations and actual H support |
| Strict B-owned minimum-f BC with adjacent C circle corner, C-owned/shared HC side or R1 | ABC_UNIQUE_SINGLETON_SIDE_ADJACENT_RETURN_FAN.md; ABC_UNIQUE_SINGLETON_SIDE_FRONT_RETURN_REDUCTION.md; ABC_UNIQUE_SINGLETON_ADJACENT_SIDE_EXCLUSION.md | Nonparallel root axes and actual negative A offset; every side mean remains |
| The remaining adjacent R0/j endpoint | ABC_R0_FULL_ANGLE_BLOCK_PRESSURE.md | Its proof explicitly allows arbitrary H degree and proves c_H dot S>sqrt(gamma^2+nu^2)/640>0 |

The middle-owned minimum-f singleton is not given the C-pressure
sign of a different far-return owner. Its R0 exit instead uses
the actual full A2/B2/C2 force ratios and the actual B2 torque.

For explicit scope at the pressure-dependent far returns,
ABC_RETURN_OWNER_NONNEGATIVE_ENDPOINT_PRESSURE.md uses reflection
and the local negative-endpoint owner cover from Section 2 above.
It therefore gives c_H dot F_C>=0 in exactly its original C-owned
or genuinely shared BC domain. It never requires a position or
equation for X,Y. Where
ABC_FAR_UNIQUE_NONNEGATIVE_ROOT_PROJECTION_EXCLUSION.md or
ABC_SHARED_UNIQUE_NONNEGATIVE_ROOT_PROJECTION_EXCLUSION.md then
uses the H4 equation, its preceding calculation has established
nonnegative or positive pressure of the *actual entire block S*.
That calculation contradicts c_H dot S<0 without inventing an
outside force or using a root degree.

The support fan is exhaustive, including k_y=0, k_j=0, both B
circle corners, both C physical masks, shared-mean endpoints,
both individual radial-weight endpoints and both q endpoints.
Its final R0 family is excluded by strictly positive block
pressure, independently of any other root force. The contrary
assumption c_H dot S<0 is therefore impossible. This proves (1).

## 4. Opposite-load C4 pressure at the canonical packing

For the following attachment theorem use the already chosen radius
minimizer minimizing the sum of squared center norms. This is the
same canonical lower-bound scope as the earlier opposite-load exit.

Suppose H--A--U--C--H is an actual positive cycle, A,U,C have true
degree two, A,C have positive circle loads, U has zero load and H
is physically circle-clear. H may have arbitrary other neighbors.
Then, in this common selected certificate,

    c_H dot (F_A+F_C) >= 0.                           (6)

Indeed if it were negative, the sum M of all other original
component circle forces would satisfy M+F_A+F_C=0 and
c_H dot M>0. These are exactly the premises of
POSITIVE_ROOT_PRESSURE_OPPOSITE_C4_EXCLUSION.md. Its complete
canonical proof permits arbitrary other H forces and retains every
one of the five outside physical squares, including any other
cycle or leaf under discussion. It gives a contradiction.

This is a contrapositive use of that proved theorem, not a new
assumption that arbitrary outside loads have positive pressure.
The latter sign follows here from the contrary block pressure.
No origin-containment premise is needed for (6); it will be
available at the roots of Section 6 anyway.

## 5. One selection for all actual local cycles

Before extraction, prelist all ordered physical H,A,B,C cycles
among the nine actual bodies and all root degrees; include both
endpoint orderings and every original fixed/shared contact and
physical circle mask. The local determinant conditions used in
Sections 2--3 concern only a true degree-two endpoint, an actual
two-body shared block, or the original A/B/C chain. Their
coefficients contain no X/Y position, force, load or positive
degree. H is kept fixed in each local virtual-work test.

The existing proofs verify nontriviality on their admissible
normal-parameter domains, and remove coincident or variable-mean
exceptions geometrically before fixed-application selection.
Their same finite conditions can therefore be imposed for this
larger list simultaneously with the original strict, nonradial,
matched-junction and canonical opposite-load conditions. Shared
physical normals use the same parameter wherever they occur;
no separate selection is made for separate cycles. Uncrossing
preserves surviving point normals and adds only actual shared
forces already covered; thinning deletes atoms. All original
means and physical zero-stress contacts remain.

This is the same enlargement mechanism stated in
POSITIVE_ROOT_PRESSURE_OPPOSITE_C4_EXCLUSION.md, Section 5,
and the arbitrary-root parallel theorem. The newly used R0
scalar inequality needs no further normal selection at all.

## 6. Whole common-root bouquets with at least two genuine leaves

At the common canonical packing, let a selected positive component
consist of:

* s>=1 actual four-cycles sharing only a root H, each with three
  other bodies of true positive degree two;
* k>=2 genuine degree-one leaves at H;
* t>=0 intact end triangles at H, each with two actual true
  degree-two tips.

There are no other positive edges in this component. Extra physical
contacts may have zero stress and remain. The total body count is

    n = 1+3s+k+2t <= 9,

and H keeps its true degree 2s+k+2t. Every one of the 9-n other
physical squares remains arbitrary and present.

**Theorem.** This entire family is impossible, for every S/D leaf
assignment and every physical load mask of every four-cycle.

The actual two-leaf central-disk lemma, recorded in
TWO_LEAF_ROOT_NO_UNLOADED_TRANSMITTER.md, Section 1, gives O in H
with arbitrary other H forces. At d=1 it retains the exceptional
origin-at-vertex SS root. The same source's complete no-unloaded-
transmitter theorem forces each of the two H-neighbors on each
four-cycle to be loaded; it applies separately to their actual
true degree-two stars. It retains the whole nine-square packing,
including its critical-radius P/Y capacity argument.

The middle of each four-cycle is either unloaded or loaded. In
the former case its original block pressure is nonnegative by
(6), and in the latter by (1). These are the entire two possible
load masks, not an assumed physical one-/two-circle mask.

Every genuine leaf contributes strictly positive H-pressure:
RADIAL_BOUNDARY_NEIGHBOR_PRESSURE.md covers S with either individual
corner weight zero, and the original selected D-leaf classification
gives c_H dot e=R-sqrt(2)-1/2>0. Every intact end triangle contributes
strictly positive H-pressure by BOWTIE_CELL_CLOSED.md, Section 2,
which permits arbitrary additional H forces. H is physically clear
by the genuine leaf/root theorem and has zero circle load.

Sum all actual component circle forces and take the scalar product
with c_H. Every C4 block contributes a nonnegative number, every
leaf a strictly positive number, and every petal a strictly positive
number. The result is strictly positive since k>=2. Genuine whole-
component balance says it is zero. This contradiction proves the
complete bouquet theorem. All original middle forces have been
kept; no cycle or triangle is replaced by an artificial leaf.

### 6.1. The complete finite size list and coarse-cell mapping

The inequality 3s+k+2t<=8 with s>=1,k>=2 has exactly seven
solutions. No graph search is needed: s=1 leaves k+2t<=5, while
s=2 forces k=2,t=0; s>=3 is impossible.

| s | k | t | Actual bodies | Actual H degree | Arbitrary extras | Original coarse cell, specified common-root layout |
| ---: | ---: | ---: | ---: | ---: | ---: | --- |
| 1 | 2 | 0 | 6 | 4 | 3 | C1.4.b2 |
| 1 | 3 | 0 | 7 | 5 | 2 | C1.4.b3 |
| 1 | 4 | 0 | 8 | 6 | 1 | C1.4.b4 |
| 1 | 5 | 0 | 9 | 7 | 0 | C1.4.b5 |
| 1 | 2 | 1 | 8 | 6 | 1 | C2.34.b2 |
| 1 | 3 | 1 | 9 | 7 | 0 | C2.34.b3 |
| 2 | 2 | 0 | 9 | 6 | 0 | C2.44.b2 |

Each row includes every genuine S/D leaf assignment, every
relative attachment orientation, all original circle masks and
weight endpoints, all original shared means, both middle-load
alternatives and the listed arbitrary extras. They are seven
whole attachment families inside larger coarse cells. Other
block adjacencies and other attachment roots remain in those
coarse cells, so the table does not close seven coarse cells.

## 7. Accepted existing-gate consequences

For the six-body common-root C4/two-leaf layout, the accepted
load cover leaves only the opposite-load BD and three-load BCD
orbits, in the old labels A--B--C--D--A. The full BD orbit is
already closed at the same canonical scope by
TWO_LEAF_ROOT_OPPOSITE_C4_EXCLUSION.md. Section 1 closes the
remaining complete BCD orbit for each SS,SD,DD leaf type; its
parallel part was already closed. No new ID is needed.

The separate full source/scope review passed. The following seven
existing IDs are now checked:

* M6.B4L2.C4.SAME.LBCD.SS.NONPARALLEL;
* M6.B4L2.C4.SAME.LBCD.SD.NONPARALLEL;
* M6.B4L2.C4.SAME.LBCD.DD.NONPARALLEL;
* M6.B4L2.C4.SAME.LBCD.SS;
* M6.B4L2.C4.SAME.LBCD.SD;
* M6.B4L2.C4.SAME.LBCD.DD;
* M6.B4L2.C4.SAME.

This reduces the unresolved four-body-block/two-bridge attachment
layouts by one, while retaining the other chain/distinct-root/
diamond layouts and every genuine force at their higher-degree
vertices. No existing larger-size parent gate is automatically
closed merely because one of its common-root layouts appears
in Section 6.1.

## 8. Verification boundary and retained obligations

This manuscript adds no scalar polynomial, exact coefficient packet,
angle cover or numerical sign claim. It reuses the proved whole-
domain ABC sources once, with an explicit replacement of their
petal-dependent parallel premise and final pressure contradiction.
Its chief verification obligation is the complete scope lift in
Sections 2--5, not a new computation. The original source scalar
certificates remain inherited dependencies until separately removed.

The three-load pressure theorem is independent of a secondary
minimizer. The whole bouquet theorem and its two-load alternatives
have the declared canonical lower-bound scope. They do not classify
all original equality packings. A fourth positive force at any
designated cycle tip or middle body invalidates its use of A2/B2/C2.
Different-root attachments and arbitrary outside resultants do not
automatically satisfy the hypotheses. The origin premise cannot be
omitted from the present arbitrary-root parallel replacement.

The unrestricted nine-square theorem, all other coarse cells, the
older full prerequisite-chain audit and Lean/kernel verification
remain separate obligations. No Lean compilation, CI or workflow
dispatch is used in this continuation.
