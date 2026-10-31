# Independent review: inward-corrected rotation at a fully screened unique-corner body

Date: October 30, 2026. Reviewer: branch-budget continuation.

**Decision: ACCEPT at the complete stated canonical and physical-contact scope.**
I did not author the motion theorem or its preceding one-body rotation
source. I read the complete final theorem and all four direct inputs,
reconstructed the physical motion and its exact inequalities, and checked
the ownership caller. This review is not a closure of a whole original
seven-cycle parent or an audit of every historical transitive input.

## 1. Exact reviewed source and prerequisites

| Source | SHA256 | Reviewed use |
| --- | --- | --- |
| INWARD_CORRECTED_CANONICAL_ROTATION_EXCLUDES_THE_FULL_UNIQUE_CORNER_VERTEX_SCREEN_2026_10_30.md | 532af1f5caab560afea6a9c7b20e7503c85417a6692322d55f9adf45917b6742 | Complete new theorem, all supplemental physical contacts, and complete singleton ownership count |
| CANONICAL_ROTATION_OF_UNBLOCKED_UNIQUE_CIRCLE_TWO_FORCE_BODIES_2026_10_30.md | 94f4d2ed11af153196d7e68644c5a21b0f3e4619abcb2b042d54a00d1450bda3 | Entire preceding feasible rotation and the exact surviving radial-diagonal geometry |
| ORIGINAL_PACKING_COMPACT_CANONICAL_MINIMUM_AND_RADIUS_TRANSFER.md | be6636a018df64f52a48f382dc21b453a208d0a929fdeaa7cb5bef9c30822c06 | Full original `(R,Phi)` minimum and physical competitor domain |
| FIVE_CYCLE_FORCE_POLYGON_DOMAIN.md | 7d0c4092ba133a832cf963f329b1c3a6442a3260576f16319293835b39e6d282 | Only the project-window nonparallel true-two proper-concurrence caller |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Full original force, moment, actual-support and transmitter conventions |

The new theorem itself assumes proper concurrence and only needs
`R>sqrt(2)`. Its wider radius statement does not silently extend the
local proper-concurrence input beyond that input's project window.
The final source expressly repeats the original radius/Phi-minimizing
premise in its Section 5 ownership corollary. This was the sole review
clarification; it changed no equation or geometric hypothesis.

## 2. Complete necessary geometry

The original rotation about `q=tau*z` is feasible for both signs under
the full screen, including every zero-weight actual contact: strict
vertex exposure persists, and its support changes by
`alpha*(cos(theta)-1)`. The unique active circle corner remains contained,
and all other corner and noncontact inequalities have positive slack.

Canonical minimality forces `det(q,c)=0` and `q.(c-q)<=0`. With
`sigma=1/sqrt(2)`, the original radial square consequently has
`c=r*e`, `r=R-sigma`, and `q=(r+delta)*e`, `0<=delta<=sigma`.
No containing-circle vertex can be shared: containment of the two
adjacent corners makes the inward radial direction strictly interior
to the actual corner sector.

The point q equals none of the three remaining vertices. Hence the
two positive screened applications have positive ray parameters; if
they coincided their normals would be parallel. An inner radial port
would leave an uncancelled transverse component at the other port.
The only possible two ports are therefore the two lateral vertices.
Their actual normals are

    n_+ = (-delta*e+sigma*Je)/alpha,
    n_- = (-delta*e-sigma*Je)/alpha,
    alpha=sqrt(delta^2+sigma^2).

Strict exposure gives `delta<sigma`; full force balance gives equal
positive contact magnitudes and `delta>0`. The lower radius premise
then gives `0<delta<sigma<r`. This uses no force equation at a neighbor.

## 3. Exact corrected motion and all physical constraints

I independently expanded the proposed actual motion

    S_theta=q+Rot_theta(S-q)-2*delta*u*e,
    u=1-cos(theta).

At either lateral contact the support change in the fixed original
normal is exactly

    ((delta^2-sigma^2)/alpha)*u<0.

Every extra screened contact at a lateral vertex has that same normal.
At the inner vertex its screen forces the normal `-e`, giving exactly
`-(sigma-delta)*u<0`. The outer vertex is the unshareable physical
circle corner. These cases exhaust all extra contacts allowed by the
screen; a coefficient-zero contact is not omitted. For sufficiently
small motion the same exposed labels still maximize every fixed
separator, so the inequalities separate the whole actual square sets.

The original active corner becomes

    z_theta=(R-(sigma+delta)*u)*e
                +(sigma-delta)*sin(theta)*Je.

Its exact squared-norm change is

    -2*B*u+4*sigma*delta*u^2,
    B=R*(sigma+delta)-(sigma-delta)^2>4*sigma*delta.

The strict last comparison follows from `R=r+sigma>delta+sigma`.
For `0<u<=2` the displayed change is strictly negative. The three
inactive corners remain inside by continuity. Finitely many positive
compact-set distances protect every original noncontact, and all pairs
not involving S are unchanged. Thus the motion really is a competitor
for the full original finite packing at the same radius.

The actual moved center is

    c_theta=(r-delta*u)*e-delta*sin(theta)*Je,

and its squared-norm change is exactly

    -2*delta*(r-delta)*u<0.

All other centers stay fixed. This contradicts the original Phi
minimum. No stress support needs to survive in the competing packing,
as the canonical input expressly permits arbitrary original feasible
competitors.

## 4. Complete ownership caller and preserved limits

In the same canonical packing, a physical-unique loaded true-two body
with only its two cycle neighbors as actual neighbors would meet the
full screen if both original normals strictly exposed its vertices.
It must therefore own at least one side. Each side transmitter owns
both incident normals. A physical singleton contact under the retained
strict point convention has at most one side-owning endpoint: two
owned axes would either give a shared interval or violate the strict
vertex/vertex convention. Thus, with the source's definitions,

    (t-s)+2*(k-d_D)<=t+k,
    s+2*d_D>=k.

The table `s>=3,2,1` for the three all-side short-C7 cases follows
literally. Two physical circle corners are counted even when one
coefficient vanishes. The count does not assert that every original
cycle is singleton or lacks supplemental physical neighbors.

The accepted theorem covers a complete sufficient contact screen,
including screened supplemental contacts. Unscreened contacts, owned
sides at the moving body, shared intervals, and its two-physical-corner
mask remain outside this motion theorem. The neighbor's masks and full
degrees are unrestricted. Its canonical conclusion is not automatically
an exclusion of every original equality packing, since such a packing
need not minimize Phi. Every original square remains in each physical
competitor. No fine or coarse gate is changed by this review.

All checks above are direct symbolic identities and continuous
inequalities. No numerical pose search, grid, computational packing
certificate, Lean/Lake invocation, CI, metadata edit or remote mutation
was used.
