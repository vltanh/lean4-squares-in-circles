# The entire five-body bowtie cell is excluded

**Status: complete hand assembly; root and separate independent full hand audits passed.**
In the declared radius window
\[
                      79/40\le R\le\sqrt{1105}/16,
\tag{1}
\]
the necessary physical certificate can be selected so that its
positive body graph has no five-body bowtie component. In the
coarse inventory this is the entire cell C2.33.b0: two triangle
blocks sharing one articulation and having no bridges.

The theorem retains all four arbitrary completion squares, every
additional zero-weight physical contact, all square orientations,
all one-/two-physical-circle-corner masks and every shared-side
application mean. It needs no secondary minimizer.

## 1. One common selection for every end triangle

Use the strict, nonradial point-normal convention and the matched
four-junction choices of PHYSICAL_BODY_GRAPH_UNCROSSING.md.
Before extracting multipliers, impose the finite generic conditions
from GENERAL_FIXED_TIP_NORMAL_SELECTION.md and the two-tip
shared-side determinant of BOWTIE_SHARED_SIDE_FREE_INTERFACE.md,
Section3. These are compatible with the previously selected finite
conditions used in the side-owner pressure proofs.

The shared-side determinant's nontriviality is proved with actual
fixed exterior applications and arbitrary internal means. Its
collinear and coincident exceptions are excluded geometrically
before generic selection. Distinct exterior points have distinct
junction parameters; the matched opposite-pair convention does
not identify them. Every remaining forbidden set is the zero set
of a nonzero real-analytic function on the allowed parameter
product. A finite union cannot fill its open domain.

Prelist physical candidates in the whole packing, including pairs
whose eventual multipliers may be zero. Uncrossing preserves
surviving point normals and adds only actual shared-side forces;
thinning deletes atoms. Thus the same initial selection covers
every final end triangle and every final application mean. No
normal is changed after the certificate is obtained.

## 2. The complete end-triangle pressure theorem

Let A--B--C--A be an actual unit-square triangle in that selected
certificate, with B,C positive degree-two circle-loaded tips.
A may have further positive neighbors. Put
\[
 F_B=2\sum_{z\text{ on }B}\lambda_z z,
 \qquad F_C=2\sum_{z\text{ on }C}\lambda_z z,
                         \qquad M=F_B+F_C.
\tag{2}
\]
Then
\[
                              c_A\cdot M>0.
\tag{3}
\]

Here is the exhaustive interface cover establishing (3).

### 2.1. Both articulation normals have side owners

If A owns both normals, they are axes of the same square.
The opposite case is excluded by
UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md. The perpendicular case
is excluded by BOWTIE_PERPENDICULAR_CONTACT_EXCLUSION.md.
The remaining parallel direction has (3) by
BOWTIE_PARALLEL_PRESSURE.md, including every shared-side mean
and coincident mean endpoint.

If exactly one normal has an A-side owner, the other is owned
by its tip. Unless it has an A owner too, that other contact
is a singleton in the relative interior of the tip side:
a point-only vertex/vertex contact cannot carry a side-axis
endpoint under the strict convention. The full theorem of
BOWTIE_MIXED_OWNER_PRESSURE.md therefore applies. Its aligned
AB case includes shared means; its oblique case retains every
BC owner, the shared-frame transition and every physical
circle mask.

If neither normal has an A owner, both are tip-owned singleton
relative-side-interior contacts. Equation(3) follows from
BOWTIE_TIP_OWNED_PRESSURE.md. These cases exhaust the side-owned
interfaces.

### 2.2. At least one articulation normal is free

Name one such contact AC.

If C has two physical circle corners, equation(3) is exactly
BOWTIE_RADIAL_FREE_INTERFACE_PRESSURE.md. Its whole singleton
AB domain is excluded, and its shared AB domain has positive
pressure. The two-radial mask is independently positive by
RADIAL_BOUNDARY_NEIGHBOR_PRESSURE.md. All zero individual
circle weights remain included.

If C has one physical circle corner and BC is a singleton,
GENERAL_FIXED_TIP_NORMAL_SELECTION.md removes free AC. A
coincident-application exception would have to be C's radial-D
inner vertex, whose norm is R-sqrt(2). Such a point cannot
also belong to the boundary neighbor B, so it cannot provide
a positive end triangle.

The only remaining possibility has C unique and BC a
positive-length shared side. The complete theorem of
BOWTIE_SHARED_SIDE_FREE_INTERFACE.md gives (3): its two-unique
mask is excluded by the compatible block selection, while its
radial-B mask has a direct pressure proof throughout the full
radius and shared-mean domain.

This exhausts all free interfaces. Combining Sections2.1--2.2
proves (3) for every end triangle, without imposing a common
frame, symmetric pose, equal radial-corner weights or fixed
shared-side application.

## 3. Apply the theorem to both complete bowtie blocks

Write the bowtie as
\[
              A--B--C--A,\qquad A--D--E--A.
\tag{4}
\]
All six displayed edges have positive multipliers, and there
are no further positive edges in this component. Each of
B,C,D,E is loaded. Indeed, if a degree-two triangle tip had
zero circle load, its two positive force vectors would be
opposite. Its two neighbors would then lie beyond opposite
support lines of the unit square, separated by its strictly
positive width. They could not physically touch, contrary
to the remaining edge of that triangle.

Thus B,C,D,E all physically touch the circle. A cannot do so:
it physically touches four distinct boundary bodies, whereas
CIRCLE_CONTACT_ANGULAR_ORDER.md bounds a boundary square's
physical boundary neighbors by two. A is physically circle-clear
and has zero circle force.

Define the two whole-block resultants
\[
                         M_1=F_B+F_C,
                         \qquad M_2=F_D+F_E.
\tag{5}
\]
Within each block, the mutual tip force cancels. The remaining
resultant is exactly the sum of that block's two outward pair
forces at A. The force equation of the unloaded A therefore is
\[
                                  M_1+M_2=0.
\tag{6}
\]
The complete theorem (3) applied separately to the two blocks
gives c_A dot M_1>0 and c_A dot M_2>0. Taking the scalar
product of (6) with c_A contradicts their strict sum.

This excludes the entire positive bowtie component. No
completion-capacity estimate is needed: the core itself cannot
carry a selected physical certificate in the window. All four
other unit squares remain part of the physical packing in every
selection and geometric input above.

## 4. Scope

The result closes C2.33.b0. The cited whole-interface
manuscripts and this assembly have passed root and separate
independent full hand audits. It does
not claim that every other cyclic coarse cell is closed, or that
the global nine-square lower bound has already been completed.
The shared articulation theorem requires its tips to have exact
positive degree two; it does not split a degree-three loaded hub
into fictitious end triangles.

No sampled configuration, numerical certificate, Lean compilation,
CI, graph omission or post-extraction normal adjustment is used.
