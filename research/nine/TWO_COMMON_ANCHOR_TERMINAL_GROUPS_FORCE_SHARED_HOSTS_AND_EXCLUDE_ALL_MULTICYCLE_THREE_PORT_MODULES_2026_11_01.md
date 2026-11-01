# Two short common-anchor terminal groups force a shared host; every multicycle three-port module is excluded

Date: November 1, 2026 UTC. Complete new hand proof, frozen for independent review.

Construction credit: articulation derived the original full-region work
and inside-neighbor-set argument with a unique third-terminal cut.
Module_universal supplied the decisive observation that the two existing
terminal contacts lie in one actual unit square and hence are less than
two apart. Root extended the work argument to arbitrary cut multiplicities
and two groups of terminals with common actual anchor points. The complete
general argument and its original module caller are printed here. None
of these contributors supplies the clean noncontributor acceptance.

## 1. A radius-free theorem for arbitrary full cuts

Let L be a finite nonempty set of actual closed unit squares with
pairwise disjoint open interiors. Retain their COMPLETE original
positive force-and-torque equations, every original support normal,
positive pair magnitude and actual application or full shared-side mean.
Every member of L is unloaded: its total selected circle coefficient is
zero. A physical circle contact with zero coefficient is allowed.

The FULL original positive cut of L is nonempty. Partition ALL its cut
edges into two nonempty groups E_0 and E_1. Assume that there are actual
points p and q such that

* the outside terminal square of every edge in E_0 contains p;
* the outside terminal square of every edge in E_1 contains q.

These are points of the actual terminal squares, not arbitrary reference
points asserted to satisfy support inequalities. Different edges may
have the same outside terminal. A terminal can appear in both groups
only if it actually contains both designated points. Its original forces
and every other actual square remain unchanged.

Let H_0,H_1 be the sets of actual inside hosts of the two cut groups:
an inside body belongs to H_j precisely when it carries at least one
original edge of E_j. Their sizes and true degrees are unrestricted.

**Theorem A.** If H_0 and H_1 are disjoint, then

    |q-p| >= 2.                                     (1)

Consequently, when |q-p|<2, some actual member of L carries an original
positive cut edge to each terminal group. This conclusion permits
arbitrary original cut multiplicities, arbitrary internal graph, and
arbitrary degrees and loads at all terminal squares.

No radius bound, body-count bound, planar graph, generic-normal selection,
or equilibrium equation at an outside terminal is required. No original
edge is removed to form the two groups. Only complete original
translations are needed; the original torque equations remain intact.

## 2. Full force resultants and complete support work

For an actual unit square i, write c_i for its center and h_i(v) for its
centered support halfwidth in a unit direction v. Always h_i(v)>=1/2.
For every original positive internal pair i--j, orient its original
unit normal v from i to j. Its unchanged actual support relation is

    v dot(c_j-c_i)=h_i(v)+h_j(v) >= 1.               (2)

Let R_0 and R_1 be the vector sums of the original cut forces in E_0
and E_1, oriented outward from L. Sum the COMPLETE unloaded translations
over L. Every internal original pair cancels, giving

    R_0+R_1=0.                                     (3)

Let C_0,C_1 be the sums of their positive magnitudes, and C=C_0+C_1>0.
The ordinary triangle inequality and (3) give

    C >= |R_0|+|R_1| = 2|R_1|.                     (4)

Let I be the COMPLETE internal support work,

    I=sum_(ij internal) mu_ij (h_i(v_ij)+h_j(v_ij)) >= 0.

Dot every complete translation at i in L with c_i-p and sum. Internal
pairs contribute -I. At a cut edge in E_0 with original normal v,
its actual outside terminal contains p. Therefore

    v dot(c_i-p) <= -h_i(v).                        (5)

At a cut edge in E_1, its actual terminal contains q, so the same
original supporting half-plane gives

    v dot(c_i-p) <= v dot(q-p)-h_i(v).              (6)

These inequalities require only membership of the designated anchor
in the actual terminal. They do not make it that edge's application
or replace any original shared-side mean.

Using (5)--(6) in the complete summed equation gives

    I+sum_(FULL cut) mu h_inside
       <= R_1 dot(q-p).

In particular

    I+C/2 <= R_1 dot(q-p).                          (7)

If R_1=0, (7) contradicts C>0 immediately. Hence R_1 is nonzero.
This explicitly covers arbitrary cancellations within either cut group.
No lower bound on any individual positive magnitude has been assumed.

## 3. Disjoint inside hosts supply one full layer of internal work

Assume H_0 and H_1 are disjoint. Sum the COMPLETE original translations
over exactly the set F=H_0. Every E_0 edge is incident to F, and no
E_1 edge is incident to F. All internal pairs within F cancel. Thus
the vector sum of original forces from F to L minus F is

    -R_0=R_1.                                      (8)

Their positive magnitude sum is at least |R_1|. Every one of these
is an actual internal pair of L and contributes at least its magnitude
to I by (2). Consequently

    I >= |R_1|.                                    (9)

Combining (4), (7), (9), and Cauchy's inequality yields

    2|R_1| <= I+C/2
              <= R_1 dot(q-p)
              <= |R_1| |q-p|.

Because R_1 is nonzero, division proves |q-p|>=2. This proves Theorem A
for the whole original domain, with every internal pair, external cut,
application endpoint and true degree retained. QED.

### Optional complete graph-distance strengthening

The same argument gives a more general bound without the disjointness
premise. Let ell be the shortest number of ORIGINAL internal positive
edges joining H_0 to H_1, with ell=0 when the host sets intersect.
Then

    |q-p| >= ell+1.                                (10)

The distance is finite: if no path joined the two host sets, sum the
full translations over every vertex reachable internally from H_0.
This set has no internal outgoing edge and no E_1 edge; its entire
external resultant is R_0. It would give R_0=R_1=0, contrary to (7).

For ell>0 and each integer j=0,...,ell-1, let F_j be all vertices at
internal graph distance at most j from H_0. It includes every E_0 host
and no E_1 host. Its complete internal outgoing force sum is again
R_1. Each layer cut therefore has magnitude sum at least |R_1|.
Adjacent original internal vertices have distance labels differing
by at most one, so no original internal edge crosses two of these
different layer cuts. They are edge-disjoint. Equation (2) now gives
I>=ell |R_1|. Equation (7), together with (4), proves (10). At ell=0
the same conclusion follows directly from I>=0 and (4), (7).

This strengthening is also a hand summation on the unchanged original
graph. It does not count a suppressed channel as a direct edge.

## 4. A physical terminal path forces an actual common host

Let A,B,C be three distinct actual outside terminal squares. Suppose
every original cut edge of an unloaded region L has its outside endpoint
in {A,B,C}; there is at least one cut to {A,B} and at least one cut to C.
Assume the actual physical contacts

    A intersect B is nonempty,
    C intersects A or B.                            (11)

The contacts in (11) may have zero selected force. All cuts still use
their original positive forces and fixed applications.

**Corollary B.** Some actual member of L has both a positive cut edge
to C and a positive cut edge to A or B.

Choose p in the actual A/B intersection. Choose q in C and in whichever
of A,B physically touches it. Then p and q lie in one SAME actual unit
square, so

    |q-p| <= sqrt(2) < 2.                           (12)

Partition the FULL original cut into its A/B edges and its C edges.
Every terminal of the first group contains p; the second group's
terminal C contains q. Theorem A and (12) force an inside host belonging
to both groups. This proves the corollary at arbitrary cut multiplicities
and all original degrees. In particular a unique C-cut host cannot
lack all positive A/B cuts. QED.

No claim that an arbitrary reference point supports a square has entered:
p and q are actual physical contact points used only as anchors for
the valid original support inequalities (5)--(6).

## 5. The whole final six-body graph is impossible

Consider six entirely unloaded actual bodies A,B,C,X,Y,T whose induced
original positive graph has precisely

    AB, BC, AX, BX, XY, CY, AT, TY.                  (13)

Their full original outside cut has three edges, one each at A,B,C.
There are no other outside forces at X,Y,T. All outside degrees, loads,
terminal identities and physical contact masks are arbitrary here.

Take the original region

    L={X,Y,T}.

Its complete internal pairs are XY and YT. Its FULL original positive
cut is exactly

    AX, BX, AT, CY.                                 (14)

For the A/B cut group the inside hosts are exactly {X,T}. For the C
cut group the inside host is exactly {Y}. These sets are disjoint.
The actual positive AB and BC edges supply the physical contacts
A--B--C. Corollary B contradicts these disjoint host sets.

Equivalently, take the SAME original applications p_AB in A intersect B
and q_BC in B intersect C. Theorem A applied to the FULL region (14)
gives |q_BC-p_AB|>=2, while those two actual points of B have distance
at most sqrt(2). This is a direct contradiction, including all original
shared-side means and their endpoints.

The original AB and BC forces are between outside terminal bodies of
L. They remain present in the full certificate and are not discarded
from any equation. We do not use a shortened equilibrium at A,B or C.
The exact full region is L, not the larger region K minus {A,B}; this
is why every needed inside-host separation is supplied literally by
(13)--(14). No dominance, small force, leaf-type, circle-load, or
central-contact assumption is needed to exclude this entire graph.

## 6. Complete exclusion of every multicycle unloaded three-port module

Return to the unchanged original nine-square research domain

    79/40 <= R <= sqrt(1105)/16,

with the complete compatible physical certificate and all original
strict/planar selection premises of the already accepted module results.
Keep every actual square, all original normals, full applications and
means, positive magnitudes and individual circle coefficients.

Let K be any connected entirely unloaded original region whose FULL
positive cut has exactly three edges. Suppose its induced original
positive graph has cycle rank at least two.

The complete independently reviewed census

`ALL_MULTICYCLE_THREE_PORT_MODULES_REDUCE_TO_ONE_SIX_BODY_RANK_THREE_GRAPH_2026_11_01.md`

applies at exactly this whole original scope. Its Theorem in Section 1
forces K to have six actual bodies, precisely the eight original edges
(13), and three direct original outside edges, one each at A,B,C.
It accounts for every other positive incidence. In particular X,Y,T
have no outside cut force. Section 5 of the present source excludes
exactly that entire final graph. This is a literal whole-source join;
no reduced edge, hidden chord, smaller packing, or selected load mask
is substituted.

**Theorem C. No connected entirely unloaded full-three-cut original
region can have cycle rank at least two in the stated nine-square
domain.** Every such region is a tree or unicyclic.

This closes the entire multicycle family, simultaneously at every
original degree, every cycle rank, every number of actual module bodies,
every external terminal multiplicity, and every original physical mask.
The two S-leaf placements and the D-leaf placements of the final graph
are all excluded because the whole graph is excluded.

The census's optional C1.8.b1 caller is not needed for this final proof.
In particular the local contradiction uses neither its outside loaded
ear nor a genuine leaf, and this new join does not add the C1.6.b3
coarse closure as an extra prerequisite. The operative initial scope
is exactly the complete physical scope of the accepted census.

## 7. Exact accepted source and clean-review boundary

The broad local theorem and Corollary B are self-contained in Sections
1--4. Their only geometric inputs are a unit square's halfwidth at least
1/2 and diameter sqrt(2), with their full uses printed explicitly.

The final original family composition imports these exact whole bodies:

| Body | SHA256 | Exact use |
| --- | --- | --- |
| `ALL_MULTICYCLE_THREE_PORT_MODULES_REDUCE_TO_ONE_SIX_BODY_RANK_THREE_GRAPH_2026_11_01.md` | `d77b06360ee17ac22fccec0b9274305a655ffafa0b6c6df8ce451d62f469653b` | Entire original multicycle full-three-cut domain reduces to precisely (13), with all full incidences retained |
| `reviews/2026-11-01/REVIEW_ALL_MULTICYCLE_THREE_PORT_MODULES_TO_ONE_SIX_BODY_RANK_THREE_GRAPH_2026_11_01.md` | `0814d65ec45dc970722ff188a9272dd1e3559b73a971406bf375fe4fa8ca91d9` | Complete independent acceptance of that entire census and every original full-cut caller |

The entire source and clean review were read. Their accepted historical
geometric kernels and compatible-certificate premises remain unchanged;
this file does not claim a fresh recursive re-audit of those kernels.
The census's explicitly optional embedding and original coarse-parent
consequences are not needed for Theorem C.

The new complete proof requires its own full noncontributor review.
The constructor credits at the beginning disclose the contributions
to the local work mechanism, the physical diameter contradiction and
the arbitrary-multiplicity generalization.

The full multicycle three-port family is closed by the proved composition,
but unicyclic and tree regions have their separate obligations. This
manuscript alone does not close an original coarse parent without a
complete literal caller, the unrestricted nine-square radius problem,
or the equality classification. No original ledger or status file is
changed here.

All mathematics is hand force summation, exact support work and finite
graph-layer bookkeeping. No mathematical program, graph enumeration,
pose search, sampled angle or coefficient, interval proof, Lean, build,
or CI was used. No original force, normal, mean, circle coefficient or
physical square was removed or changed.
