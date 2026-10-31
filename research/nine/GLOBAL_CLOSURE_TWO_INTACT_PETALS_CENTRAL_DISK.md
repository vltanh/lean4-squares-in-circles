# Two intact triangle petals force a central disk and exclude all triangle block trees

Date: October 26, 2026.

**Status: accepted complete hand argument after the full-source reviews
REVIEW_TWO_INTACT_PETALS_CENTRAL_DISK_ROOT_2026_10_26.md and
REVIEW_TWO_INTACT_PETALS_CENTRAL_DISK_ROOTED_BLOCKS_2026_10_26.md.**
This source extends the accepted small-port theorem to an actual
closed-disk statement, and then uses the entire original block-cut
tree. It does not assume that every cyclic block initially shares
the two petals' root.

## 1. Scope and inherited local geometry

Keep the original nine physical unit squares, the common compatible
selected physical certificate, and the same radius/Phi-minimizer pose.
Use the minimum-positive-scalar-support selection and its small-core
prerequisites from GLOBAL_CLOSURE_ARTICULATION_STRESS_SPLITTING.md.
Work in

    79/40 <= R <= sqrt(1105)/16,
    d = sqrt(R^2-1/4)-1,
    epsilon = max(d-1,0) < 1/60,
    r = R-sqrt(2) > 67/120.

An intact petal is an actual positive triangle H,U,V whose two
nonroot bodies U,V have their true positive degree two. Their
touching neighbors force their positive circle loads. H retains
every additional actual force.

Suppose H has two distinct intact petals. The accepted
ROOTED_END_TRIANGLE_ORIGIN_INTERIOR.md puts O in int H. Each
petal's original common side has outward own axis N, height P, and
ports of strictly opposite transverse signs:

    p_- = P N + y_- JN,  p_+ = P N + y_+ JN,
    y_- < 0 < y_+,      1/5 < P < 39/40.                 (1)

These are the complete parallel/nonparallel, physical-mask and
original-mean statements used in Sections 1--3 of
GLOBAL_CLOSURE_COMMON_ROOT_INTACT_TRIANGLE_FORESTS_EXCLUSION.md.
That source also proves that at most one intact petal can use any
one actual side of H. Its proof uses the empty angular gap between
the two touching loaded tips, not the root's complete force equation.

## 2. The whole small disk lies strictly inside the actual root

**Central-disk theorem.**

    D_epsilon is contained in int H.                    (2)

For epsilon=0 this is exactly the origin-interior theorem. Suppose
epsilon>0 and (2) fails. Since O is interior to the unit square H,
some actual side has a positive height sigma<=epsilon. Call its
outward own axis e. The opposite side has height 1-sigma.

Neither of these two sides can be the common side of an intact
petal: their heights respectively satisfy

    sigma <= epsilon < 1/5,
    1-sigma >= 1-epsilon > 59/60 > 39/40,

contrary to (1). Therefore the two intact petals both use sides
perpendicular to e. They cannot use the same side by the already
proved one-petal-per-side theorem, so they use the two opposite
perpendicular sides.

Consider either such petal and write P for its actual side height.
Take e as its transverse coordinate, with either consistent
orientation of the ordered ports. The transverse H interval is
[sigma-1,sigma]. The strict straddling in (1) gives one actual
port

    z = P N + w e,     0<w<=sigma<=epsilon.

This actual point belongs to a physical boundary tip, so |z|>=r.
Consequently

    P^2 = |z|^2-w^2
        > (67/120)^2 - (1/60)^2
        = 299/960 > 1/4.

Thus P>1/2. The same argument applies to the other petal's
opposite perpendicular side. Their two actual side heights sum
to the unit width one, so they cannot both exceed 1/2. This
contradiction proves (2).

The proof did not require a bridge on the small side. This is the
extra conclusion beyond the older small-radial-application theorem.
It concerns every side of the original H, and includes equality
sigma=epsilon without losing strictness.

## 3. Every genuine leaf root is H; no bridge-only internal body exists

A genuine S-leaf root K contains the inward radial unit segment
ending at its true application d v. It therefore meets D_epsilon:
if d>1 it contains epsilon v; if d<=1 it contains O.
A genuine D-leaf root contains O openly. By (2), no actual
unit distinct from H can meet D_epsilon. A boundary point of
such a unit inside int H already forces interior overlap, because
its own interior points approach that point. Hence every genuine
leaf root in the entire original component is H.

Now let U be any positive bridge-only internal body. The exact
articulation split makes a loaded bridge-only body a genuine
leaf, so U is truly unloaded. Since O is in int H, U avoids O.
GLOBAL_CLOSURE_OFF_ORIGIN_BRIDGE_TRANSMITTERS.md then gives an
actual incoming application of norm in (0,epsilon], belonging
to U. This again contradicts (2). Therefore no such U exists.

This uses minimum support only where that prior theorem requires
it. No force is removed to create a leaf or a degree-two body.

## 4. Entire all-triangle components with two intact petals are impossible

**Whole graph theorem.** A selected positive component with only
triangle cyclic blocks and arbitrary bridge blocks cannot contain
two intact petals at the same root H.

Use its actual finite block-cut incidence tree, with each bridge
a two-vertex block, and root the tree at H. Every terminal triangle
has two private degree-two tips; it is an intact petal, so its root
also contains O openly. Its actual root must therefore be H.
Every terminal bridge has a genuine leaf endpoint. By Section 3
its root is H as well.

If any block had an articulation other than H or occurred farther
from H, choose a terminal block descendant on that branch. Its
root would differ from H, contradicting the preceding paragraph.
Equivalently all leaf block nodes are adjacent to H, which in a
finite incidence tree with articulation degrees at least two
forces every block node to be adjacent to H.

Thus every triangle block is an intact petal at H and every bridge
is a genuine direct leaf edge at H. In particular no initially
decorated triangle or indirect bridge attachment was silently
discarded: the complete tree argument has ruled it out.

H is physically circle-clear, since it contains O and R>sqrt(2).
Write M_j for each petal's actual resultant and alpha_i v_i for
each genuine direct leaf force. The full original H equation is

    sum_j M_j + sum_i alpha_i v_i = 0.                    (3)

The complete arbitrary-root-degree petal pressure theorem gives
c_H.M_j>0. Every direct leaf has the same strict center pressure:

    S: c_H.v_i = d-H_H(v_i) >= d-1/sqrt(2) > 0;
    D: c_H.v_i = r-1/2 > 0.

For D the last identity is the actual side-interior support law.
Taking the scalar product of (3) with c_H contradicts its strictly
positive left side. This proves the entire graph theorem.

## 5. Exact scope and consequences

The geometry (2) applies at arbitrary full root degree, without
assuming that the rest of the component is a triangle block tree.
The graph conclusion applies to any number of triangle blocks and
any bridge forest allowed by the original nine-body budget, at the
same inherited canonical/minimum-support scope.

In particular every original C2.33.b2/b3/b4 or C3.333.b1/b2 layout
with two intact petals is excluded, including non-bouquet layouts
which one might initially decorate elsewhere. Distinct intact
roots are already impossible by origin-interior overlap. Therefore
any still surviving all-triangle component can have at most one
intact petal in its entire actual block tree.

This is a uniform whole-family exit. It does not by itself close
any entire coarse cell whose original graph cover also contains
exactly-one-intact or no-intact layouts. The unchanged fine labels,
coarse parent cells, unrestricted sharp theorem and equality
classification require their respective complete joins.

All nine physical squares, circle masks, zero individual weights,
actual contact normals, positive force degrees and original side
means remain. No numerical pose, scalar certificate, Lean
compilation or CI is used.

