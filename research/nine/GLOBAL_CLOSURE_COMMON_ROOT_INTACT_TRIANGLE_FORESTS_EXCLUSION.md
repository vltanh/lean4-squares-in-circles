# Intact triangles sharing one root exclude every attached bridge forest

Date: October 26, 2026.

**Status: accepted after full root and independent C6 review.** See
`REVIEW_COMMON_ROOT_INTACT_TRIANGLE_FORESTS_ROOT_2026_10_26.md` and
`REVIEW_COMMON_ROOT_INTACT_TRIANGLE_FORESTS_C6_2026_10_26.md`, both of which
pin the unchanged mathematical source before this acceptance-only status
edit. No ledger is changed. This does not yet close a whole bridged
C2.33 coarse cell.

Keep the common compatible selected physical certificate and

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,
    epsilon=max(d-1,0)<1/60,
    r=R-sqrt(2)>67/120.                                 (1)

An intact end petal means an actual positive triangle H,T1,T2 whose
tips T1,T2 have their true positive degree two and positive circle load.
H keeps all its other original forces and its true degree. Distinct
intact petals at H have distinct tips: otherwise a shared tip would
have more than its required two positive neighbors.

## 1. Complete common-face consequences of the origin theorem

For every intact petal, the accepted
`ROOTED_END_TRIANGLE_ORIGIN_INTERIOR.md` gives O in the open interior
of H. The original common-face theorem supplies an actual root side
with unit outward axis N and height P<39/40. In the frame of that
side, the two original applications have the form

    H=[P-1,P] times [Y-1/2,Y+1/2],
    p_-=(P,y_-), p_+=(P,y_+),       y_-<0<y_+.           (2)

The strict port straddling is proved in both the nonparallel and
parallel branches of the origin theorem. The parallel branch has
both actual normals N; its strict-vertex alternative is excluded.
In the nonparallel branch the actual normals have strictly positive
N-components. At either port, their transverse component has the same
weak sign as that port's transverse coordinate. These statements
include owned-side means, their endpoints, and zero proper lengths.

Every point belonging to an actual boundary unit has norm at least
r>67/120. Since the two straddling port heights in (2) differ by at
most one, one has magnitude at most 1/2. Therefore

    P^2>(67/120)^2-1/4=889/14400>1/25.

Origin containment makes P positive. Hence

    1/5<P<39/40.                                        (3)

Each vertex of H has N-coordinate P or P-1. Thus the existence of
even one intact petal implies the useful orientation-free statement

    every actual H vertex has norm >1/40.               (4)

This does not assert that H contains the disk D_(1/40): its transverse
side margins may still be small.

## 2. At most one intact petal can use a given root side

Write F_-,F_+ for the actual nonzero circle resultants of the two tips.
The complete loaded-tip proper concurrence theorem gives

    q_i=tau_i F_i=p_i+ell_i n_i,
    tau_i>0, ell_i>=0,       i in {-,+}.                 (5)

Every physical circle mask and individual zero corner weight is retained.
Using (2) and its full normal signs in (5), we obtain

    (F_-).N>0, (F_+).N>0,
    (F_-).JN<0<(F_+).JN,                                (6)

after choosing JN as the transverse orientation. The two actual tip
resultant directions therefore lie strictly on opposite sides of N
inside its open angular semicircle. Their minor angular interval
contains N strictly.

We record why this interval contains no resultant direction of any
other physical loaded unit. The tips actually touch. By
`CIRCLE_CONTACT_ANGULAR_ORDER.md`, Sections 2--3, their center directions
are consecutive along a minor gap of length less than 2pi/5, and every
two boundary-center directions differ by more than pi/5. Each full
circle resultant is within pi/12 of its own center direction, by the
local estimate in `FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md`, Section 1.
That estimate applies independently of a four-body path and retains all
nonnegative individual weights.

The center intervals of angular radius pi/12 are disjoint, because
pi/5>pi/6. Thus circle-resultant order agrees with center order. For
the touching pair, the corresponding resultant gap has positive
length and is less than

    2pi/5+pi/6=17pi/30<pi.

It is consequently the same minor gap as the one in (6), and has no
other loaded resultant direction in its interior.

If two distinct intact petals used the same H side, each of their
two open minor resultant intervals would contain that side's direction
N. All four endpoints are distinct, by the same disjoint angular
intervals. Two such intervals overlapping at an interior point must
contain an endpoint of one strictly inside the other. That endpoint
would be another loaded body's resultant direction inside a touching
pair's empty minor gap, a contradiction.

**Lemma 2.** At most one intact end petal at H can have its two actual
root ports on any given actual side of H.

No arbitrary face is assigned to a petal. Its face is the one supplied
by the actual common-side theorem. The straddling in (2) also makes the
two ports distinct, so the common side cannot be ambiguously another
side meeting it at a single vertex.

## 3. Two intact petals exclude every small radial bridge application

Suppose H has at least two intact petals and also an actual radial
bridge application p satisfying

    |p|<=epsilon.                                        (7)

Let e be its actual outward unit normal from H. Since O is in the open
interior of H, radiality gives

    p=sigma e,       0<sigma<=epsilon.

In particular epsilon>0. Equation (4) and epsilon<1/60<1/40 imply that
p cannot be a vertex of H, including an axis endpoint. It is in a
relative side interior. Consequently e is an actual H side axis and

    h_H(e)=sigma,       h_H(-e)=1-sigma.                 (8)

An intact petal cannot use either of these two sides: the first height
is below 1/5, and the other is greater than 59/60>39/40, contradicting
(3). Every intact petal must therefore use one of the two actual sides
perpendicular to e.

For such a face of outward normal N, choose the transverse coordinate
e. The root's transverse interval is [sigma-1,sigma]. By the complete
straddling (2), one actual petal port has the form

    z=P N+w e,       0<w<=sigma<=epsilon.

It belongs to a true boundary tip, so

    P^2=|z|^2-w^2
       >(67/120)^2-(1/60)^2
       =299/960>1/4.                                   (9)

Thus each perpendicular side used by a petal has height P>1/2.
Lemma 2 prevents two petals from using the same side. With at least
two petals, both opposite perpendicular sides would therefore have
height greater than 1/2. Their two heights sum to the actual unit
width one, a contradiction.

**Theorem 3.** A root of two distinct intact end triangles has no
positive radial bridge application of norm at most epsilon.

The proof uses all actual petal ports and their proper normal signs.
It does not require a force equation involving only the two petals,
or place any restriction on H's other positive forces.

## 4. Whole common-root triangle-and-forest family

Now use the common minimum-support selection of
`GLOBAL_CLOSURE_ARTICULATION_STRESS_SPLITTING.md`, with its named
canonical small-core joins. Suppose the entire positive component has
at least two cyclic blocks, all triangles sharing one root H, all their
non-H vertices true degree-two tips, and arbitrary bridge forests
attached at H. All physical units remain, and the component has at
most nine bodies.

Every tip is loaded by the touching-neighbor degree-two obstruction,
so every cyclic block is an intact petal. The origin theorem gives
O in the open interior of H. Every other actual square avoids O even
on its boundary.

The exact articulation splitting theorem makes every loaded bridge-only
body a genuine leaf. Every other positive bridge-only body is genuinely
unloaded and off-origin. The complete off-origin transmitter theorem
then gives it exactly two positive neighbors, with its unique inward
neighbor containing O and therefore equal to H. Its inward application
has norm in (0,epsilon].

If any such internal bridge body exists, its actual edge to H violates
Theorem 3. Hence no internal bridge body exists. Every bridge forest
branch is a genuine direct leaf at H. This conclusion includes empty
forests, all possible forks before their degree reduction, and all
original branch lengths; no graph shape was assumed in advance.

Let M_j be the actual resultant of each intact petal, and alpha_i v_i
the actual force from each direct leaf. H is physically circle-clear.
Its complete actual force equation is

    sum_j M_j + sum_i alpha_i v_i =0.                   (10)

Each petal has c_H.M_j>0 by the complete end-triangle pressure theorem.
Every genuine direct leaf also has positive center pressure, with no
degree restriction at H:

- An S leaf gives c_H.v_i=d-H_H(v_i)>=d-1/sqrt(2)>0.
- A D leaf is side-interior at H and gives
  c_H.v_i=R-sqrt(2)-1/2>0.

These are the actual S/D radial support identities, retaining all
other root forces. Taking scalar product of (10) with c_H gives a
strictly positive left-hand side, impossible.

**Whole-family conclusion.** No such original common-root collection
of intact triangles, with any attached bridge forests, occurs in the
selected nine-square certificate.

In particular this removes the complete shared-hub two-triangle
family in which all four cyclic tips remain untouched and every bridge
forest is attached at their common root. For b=2 it includes the
remaining root--unloaded--leaf path, with all genuine leaf types and
widths reduced by the existing actual off-origin theorem.

Tip attachments change their true degrees and are outside this intact
family. Shared-hub graphs with such attachments, direct intertriangle
connectors with the remaining endpoint decorations, and graphs without
an intact petal retain their full original obligations. No complete
bridged C2.33 cell or new fine label is declared closed here.

No force, original mean, circle mask, physical square, or contact normal
is changed. No numerical pose, sampled angular cover, Lean compilation,
CI, remote write, or shared-ledger edit is performed.
