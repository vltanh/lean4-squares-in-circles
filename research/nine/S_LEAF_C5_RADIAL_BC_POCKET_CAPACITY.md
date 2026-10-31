# The actual B-V-C pocket of every S-leaf C5 load13 core has capacity at most one

Date: October 26, 2026.

**Status: complete hand local-pocket reduction, accepted after independent
topological and original-domain review in
REVIEW_S_C5_TILTED_AND_RADIAL_POCKET_ROOT_2026_10_26.md.** It uses the accepted aligned
far-endpoint theorem and the separately reviewed tilted far-endpoint
theorem. No original S-leaf completion gate is closed.

Keep the entire original positive component

    A--B--V--C--U--A, with a genuine S leaf L at A,

in 79/40<=R<=sqrt(1105)/16, with original block loads B,C and
the three additional physical unit squares. A has true degree
three; B,C have true degree two; U,V are true unloaded
degree-two transmitters. Every actual normal, physical circle
mask, radial corner weight and application mean remains.

The sources

- S_LEAF_C5_ALIGNED_FAR_ENDPOINT_RADIAL.md;
- S_LEAF_C5_TILTED_FAR_ENDPOINT_RADIAL.md

together cover the entire original aligned and tilted root
domain. They prove

\[
 d=\sqrt{R^2-1/4}-1>1,\qquad d<61/60,
\]
\[
 C\text{ is physically radial},\qquad w_U=w_V=1.
\tag{1}
\]

They also retain positive proper loaded concurrences q_B,q_C,
the actual root concurrence q_A on the positive genuine-leaf
ray, and positive coefficients for the three real connections
AB,BC,CA. In the tilted proof one root proper coefficient
was initially allowed to be signed; its full edge coefficient
was subsequently proved positive. No properness at a
fictitious circle load on A is assumed here.

**Theorem.** The entire actual B--V--C exterior pocket contains
at most one additional physical unit square. If B is also
physically radial, that whole pocket is empty.

The presence of the genuine leaf is accounted for below.
The simple-cycle premise of the existing radial-pocket
capacity theorem is not imported unchanged.

## 1. The local channel has positive height greater than one half

At the physical radial C, the complete local support cover in
Section 1 of RADIAL_LOAD_SIDE_CHANNEL_POCKET_CAPACITY.md
applies to the actual reserve-one channel toward the physical
boundary endpoint B. It needs no simple-cycle premise.
The return is a strict inner vertex with strict components.
After orienting its radial frame and the horizontal channel,
write

\[
 p_{CV}=d e+f/2,\qquad
 g=-\alpha e+\beta f,\qquad
 \alpha,\beta>0,\quad\alpha^2+\beta^2=1.
\]

The channel line is at distance

\[
                  H=d\beta+\alpha/2>1/2
\tag{2}
\]

from the origin. The strict inequality follows from
d>1/2 and alpha+beta>=1. Orient its perpendicular axis N
so that the applications have height H>0, and label the
left and right endpoints X,Y, a relabeling of B,C, so that

\[
 P_X=(l,H),\qquad P_Y=(l+1,H),\qquad
 X\subseteq\{x\le l\},\quad Y\subseteq\{x\ge l+1\}.
\tag{3}
\]

The real segment P_X P_Y lies in V. Properness at B,C puts
q_B,q_C on this same horizontal line. Since each is a
positive multiple of its own circle resultant, both original
resultants have positive N-components.

## 2. The genuine leaf and the other side of the actual cycle are below the channel

Let F_A be the genuine leaf resultant at the root, pointing
along its original outward leaf direction e_L; F_B,F_C
are the unchanged circle resultants. Whole-component force
balance says

\[
                         F_A+F_B+F_C=0.
\tag{4}
\]

By Section 1, F_B dot N and F_C dot N are strictly positive.
Thus e_L dot N<0. The actual genuine S leaf is

\[
 L=[d,d+1]e_L+[-1/2,1/2]J e_L.
\]

Every one of its points has height less than 1/2:

\[
             N\cdot z\le d(N\cdot e_L)
                         +\tfrac12|N\cdot J e_L|
                       <1/2<H\qquad(z\in L).
\tag{5}
\]

This includes both actual circle corners, independently of
which is used as the exterior spoke. The leaf application
at A has negative N-coordinate.

Also q_A is a positive multiple of F_A, so its height is
negative. The positive AB and AC connection coefficients
give q_B-q_A along the actual A-to-B force and q_C-q_A
along the actual A-to-C channel force. Both those directions
have positive N-components.

The proper B port lies at or before q_B along A-to-B,
and the proper C port p_CU lies at or before q_C along
A-to-C. Therefore

\[
     N\cdot p_{AB}\le H,\qquad N\cdot p_{CU}\le H.
\tag{6}
\]

The exact U reserve gives p_CU-p_AU equal to the
A-to-C unit direction, whose N-component is positive.
Consequently

\[
                         N\cdot p_{AU}<H.
\tag{7}
\]

These deductions do not require q_A to lie inside A.
They do not require the root's original channel proper
coefficient to be nonnegative.

The five actual C5 contact points are now all in
{N dot z<=H}: p_AB,p_BV,p_CV,p_CU,p_AU, with
p_BV,p_CV on the line. The contact polygon joining
successive applications inside their own actual convex
bodies is therefore wholly below or on that line.
The actual leaf segment and its attachment at A can
likewise be joined to the root cycle applications inside
the root using chords whose endpoints are all below H.

## 3. Exact physical identification of the outward B-V-C pocket

The physical center/contact embedding gives the actual
Jordan C5 cycle, with its genuine leaf branch and exterior
spokes at the three physical loaded bodies L,B,C.
The center/contact loop is homotopic, inside the closed
occupied cycle bodies, to the contact polygon of Section 2.
As in CONTACT_RING_HOLE_AREA.md, winding about every
point in a completion square's open interior is unchanged
by this homotopy. Thus the free central C5 region has no
point above H.

For the B--V--C side, the endpoint-center proof in
FIVE_CYCLE_FOUR_LOAD_EXCLUSION.md, Sections 1--2, is local:
it uses the actual supports (3), endpoint center radii
below 91/60, and the positive N-component of each
endpoint circle resultant. Those premises have all
been verified here. It gives nonnegative endpoint-center
heights, with the left center strictly left of -29/60
and the right center strictly right of 29/60.

The full local argument in Section 1 of
SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md then supplies facing
physical circle corners z_X,z_Y with

\[
 (z_X)_x<0<(z_Y)_x,\qquad
                   (z_X)_N,(z_Y)_N\ge H.
\tag{8}
\]

For a physical radial endpoint the higher actual circle
corner is used, even if its individual weight is zero.
For a unique endpoint its proper positive concurrence
places its unique circle corner above the line.

The occupied broken line

\[
                         z_X-P_X-P_Y-z_Y
\tag{9}
\]

is a simple disk crosscut: the endpoint strips in (3)
separate the three segments, which lie respectively in
X,V,Y. Join it to the upper outer-circle arc. Its
bounded region is wholly in {N dot z>=H}.

This is the actual exterior side of B--V--C. The free
central cycle region is on the other side by the winding
argument above. The only other positive boundary spoke,
the one at L, has both its circle endpoints below H by
(5), and its root attachment can be homotoped below H
as in Section 2. It therefore cannot be inserted in
the upper arc or change which exterior side corresponds
to the B--V--C path. The other two exterior paths are
the actual L--A--B and L--A--U--C paths.

All replacements are inside the original closed occupied
bodies. At shared-side endpoints or other junction
degeneracies, take a compact path in an extra square's
open interior. It has positive distance from the closed
core union; sufficiently small center/contact perturbations
and the occupied homotopies preserve its side. This is
the same compact-interior argument used in Section 2
of SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md. Extra physical
contacts with zero selected weight can only subdivide
these regions and do not enlarge them.

Hence every whole extra in the actual B--V--C pocket
satisfies

\[
                   E\subseteq D_R\cap\{N\cdot z\ge H\},
                   \qquad |c_E|\ge H+1/2>1.
\tag{10}
\]

Connectedness of its open interior and the occupied
crosscut justify the whole-square conclusion; it is
not a statement merely about the center.

## 4. The unchanged radial pocket estimates give capacity one

With the physical cap join established, Sections 3--6 of
RADIAL_LOAD_SIDE_CHANNEL_POCKET_CAPACITY.md apply
without any remaining reference to the larger graph.
Their inputs and estimates are:

- The radial endpoint has center radius d+1/2>7/5;
  the other physical boundary endpoint has center radius
  greater than 5/4.
- The actual reserve-one endpoint applications give center
  distance at most 1+sqrt(2). Together with their opposite
  horizontal center signs and nonnegative heights, the
  whole outward center-angle gap is less than
  arccos(-2/3)<53pi/72.
- On the inner circle of radius 5/4, the radial endpoint
  blocks its complete closed centered arc of half-width
  beta_0=arcsin(2/5)>pi/8. The other physical boundary
  endpoint blocks its complete centered arc of half-width
  pi/9.
- The actual crosscut (9) routes every extra's open inner
  circle arc into the same free consecutive interval.
  Its length is strictly less than

\[
                 53\pi/72-\pi/8-\pi/9=\pi/2.
\tag{11}
\]

By (10) and ANNULAR_CENTER_ARC_BUDGET.md, every such
whole extra contributes an open inner-circle arc of
length strictly greater than pi/4. Two extras would
need disjoint open arcs of total length greater than
pi/2, contradicting (11). Thus the entire pocket has
capacity at most one.

This retains arbitrary extra-square frames and positions.
No extra is moved to the boundary and no circle weight
is assigned to it.

## 5. If B is radial, this entire pocket is empty

When both endpoints are physical radial, their actual
applications in (3) are inner vertices of common norm

    r_0=sqrt(d^2+1/4).

The two points are at distance one on their positive-height
line. Their coordinates on that line are therefore

\[
                         P_X=(-1/2,d),\qquad
                         P_Y=(1/2,d).
\tag{12}
\]

In particular the actual cap height is H=d.
Any unit wholly beyond this line has center height at
least d+1/2, while the sharp universal center bound is
at most d+1/2. Equality forces the unique radial square

\[
                    [-1/2,1/2]\times[d,d+1].
\tag{13}
\]

As proved geometrically in Section 7 of
RADIAL_LOAD_SIDE_CHANNEL_POCKET_CAPACITY.md, the strict
inner-vertex support at each actual endpoint makes the
candidate (13) overlap an endpoint's open interior near
P_X or P_Y. That proof uses only (12), the strict
endpoint normals and actual radial frames. It applies
unchanged here. Thus no unit fits in this cap.

## 6. Complete retained allocation statement

The actual C5 central hole has capacity at most one by
CONTACT_RING_HOLE_AREA.md. Together with the genuine
leaf branch and the three physical loaded-body spokes,
the remaining outside regions follow the paths

    B--V--C,   C--U--A--L,   L--A--B.

The physical embedding and the compact-interior rule
assign every extra square to the central region or one
of these three exterior regions. Additional zero-weight
physical contacts may split one region; counting all
pieces together only makes these capacity bounds weaker.

Writing the four numbers as n_c,n_BC,n_CL,n_LB gives the
following whole original necessary allocation:

\[
 \begin{gathered}
 n_c+n_{BC}+n_{CL}+n_{LB}=3,\qquad
 n_c\le1,\qquad n_{BC}\le1,\\
 B\text{ radial}\ \Longrightarrow\ n_{BC}=0.
 \end{gathered}
\tag{14}
\]

Thus at least one original extra lies in a leaf-side
region, and at least two do when B is radial. No bound
on the coupled capacities of the two leaf-side regions
is claimed in this manuscript.

The original gate M6.B5L.C5.L13.S therefore remains open.
The theorem supplies a verified local completion
reduction while retaining all three actual extras,
both full root shapes and all original force/mean
endpoints.
