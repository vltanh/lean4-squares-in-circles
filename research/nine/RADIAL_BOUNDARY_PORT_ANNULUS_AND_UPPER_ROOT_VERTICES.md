# Two physical port tests force a unique circle corner

Date: October 27, 2026.  
Author: topology_final.

**Status: complete fresh physical theorem, frozen for full independent
review.** A single incoming-support test confines every physical
two-circle-corner contact to a thin radial annulus. It then proves
physical uniqueness at both upper-vertex contact charts of the
genuine lower S root, including free contacts and every physical
circle-weight mask.

No force law, concurrence, degree assumption, owner selection or
angle certificate is used in these local results.

## 1. Full physical statement

Let C and H be distinct interior-disjoint unit squares contained
in the disk of radius R centered at zero. C touches the containing
circle, and

    d=sqrt(R^2-1/4)-1>0,
    R^2=(d+1)^2+1/4.                              (1)

Let P be an actual common point. Let n be any actual common
unit supporting normal directed from H to C, so

    n.Z>=n.P for every Z in C,
    n.Z<=n.P for every Z in H.                     (2)

The same P and n may be the original selected singleton
application, a genuinely free vertex contact, or any actual
shared-side mean. Nothing is moved or chosen after extraction.

**Theorem 1.1 (physical radial-port annulus).** If C has two
physical circle corners and the actual support value satisfies

    P.n>=0,

then

    d^2<=|P|^2<=d^2+1/4.                          (3)

**Corollary 1.2 (two physical uniqueness tests).** C has a unique
physical circle corner whenever either

    |P|^2<d^2,                                    (4)

or

    P.n>=0 and |P|^2>d^2+1/4.                     (5)

The endpoints in (3) are retained. In particular neither equality
in radius nor a zero support value is silently turned into a
strict contradiction. The conclusion concerns physical corners,
independently of which individual circle multipliers are positive.

## 2. Complete physical classification and every support feature

The circle-corner coordinate comparison gives the whole
two-corner physical form

    C=[d,d+1]e+[-1/2,1/2]f,                       (6)

for orthogonal unit vectors e,f. Here the two containing-circle
corners are (d+1)e plus or minus f/2.

For completeness, at a circle corner choose own axes so that
the square is [a-1,a] x [b-1,b]. Comparing the adjacent
corners gives a,b>=1/2. A second maximum-norm corner can occur
only if one of a,b equals 1/2; the opposite-corner equality
would require a=b=1/2 and R^2=1/2, impossible in (1).
The other coordinate is sqrt(R^2-1/4)=d+1. This proves (6).
It also shows that every boundary unit in this radius range
has either one or two physical circle corners.

Every point of (6) has norm at least d. This proves the lower
bound in (3), and proves (4) impossible for a physical
two-corner unit without even using n.

A containing-circle point cannot be shared by two contained
interior-disjoint unit squares. If Z were such a point, it
would be a vertex of both by strict convexity of the disk.
For either square and either orthogonal inward axis v,
containment of Z+v gives Z.v<=-1/2. Thus -Z is strictly
inside both inward quadrants. The points Z-epsilon Z would
belong to both open squares for small positive epsilon, a
contradiction.

Consequently the actual P cannot be either outer corner of (6).
If P is a vertex, it is one of the two inner vertices, and

    |P|^2=d^2+1/4.                               (7)

This covers every genuinely free vertex normal without an
owner premise or a generic-selection argument.

Suppose P is in the relative interior of a side of C. The
actual common normal n in (2) must be that side's inward
unit normal. Its four possible support values are exactly:

| Actual side of C | Actual inward normal n | Actual P.n |
| --- | --- | --- |
| Inner radial face | e | d |
| Outer radial face | -e | -(d+1) |
| Lower transverse face | f | -1/2 |
| Upper transverse face | -f | -1/2 |

Since d>0 and P.n>=0, only the inner radial face is possible.
Its actual full point is P=d e+t f, with -1/2<=t<=1/2,
and

    |P|^2=d^2+t^2<=d^2+1/4.                     (8)

The closed interval includes both side endpoints and every
actual shared mean. The side-interior and vertex cases exhaust
all possible common points. This proves Theorem 1.1 and both
tests of Corollary 1.2.

No point in the interior of C can be a common point with an
interior-disjoint positive-area square: a small neighborhood
would meet the other square's interior. Thus the boundary
feature cover above loses no physical intersection type.

## 3. A whole genuine lower-leaf far-vertex theorem

Let the actual root have the physical rectangle

    H=[-X,1-X] x [-A,1-A], X>0, A>=0,
    F=(-X,1-A).                                 (9)

Retain one of these two real radial-leaf alternatives:

* Vertex leaf: its actual radial application is (-X,-A),
  with X^2+A^2=d^2 and 0<=A<3/8.
* Aligned lower leaf: its actual radial direction is -E1,
  its actual application is (-d,0), and X=d with
  0<=A<1/2.

These are two different genuine leaf equations. The vertex
radius equation is not imposed on the aligned row. The
occupied leaf itself, any other root forces and every other
packing unit may remain present.

Suppose a physical boundary neighbor C has an actual common
application at the upper-left vertex F, with actual incoming
normal

    n=(-u,v), u,v>0, u^2+v^2=1.                 (10)

No C owner is assumed. The contact may be free, and any
physical C circle mask is initially permitted.

**Theorem 3.1.** In the entire domain (9)--(10), C has a unique
physical circle corner.

Indeed G=1-A>0 and

    F.n=Xu+Gv>0.                               (11)

In the genuine vertex row,

    |F|^2-(d^2+1/4)
      =X^2+(1-A)^2-d^2-1/4
      =3/4-2A>0.                              (12)

In the aligned row,

    |F|^2-(d^2+1/4)
      =(1-A)^2-1/4>0.                         (13)

Equations (11)--(13) are exactly the second physical test
(5). Thus a two-corner C is impossible on both whole actual
leaf rows.

The two strict height thresholds are intentional. At A=3/8
the vertex-row expression in (12) is zero; at A=1/2 the
aligned-row expression in (13) is zero. Those equalities are
not excluded by this theorem. All smaller values, including
the aligned A=0 endpoint, are covered.

The proof uses neither a C2 equation nor an equation at any
other root or boundary unit. It is valid for arbitrary
additional physical contacts, degrees, forces and real means.

## 4. Both upper-vertex charts of the fresh original lower root

The accepted fresh positive B-owned root normal form supplies,
after its single origin-preserving orthogonal map,

    d=1+delta, 0<delta<1/60,
    H=[-X,1-X] x [-A,1-A],
    X=1+x, 0<x<=delta,
    0<=A<31/120, G=1-A,
    F=(-X,G), W=(1-X,G)=(-x,G).                 (14)

The genuine H leaf is exactly one of

    X^2+A^2=d^2, A>0,       or
    X=d, 0<=A<31/120.                         (15)

The actual lower-root chart is retained in full; no central
or BK owner enters (14)--(15).

For any actual physical boundary neighbor at the upper-right
point W, regardless of the actual common normal,

    |W|^2=x^2+G^2<=delta^2+1
             <(1+delta)^2=d^2.                (16)

The strictness is the exact gap 2delta>0. Therefore the
first physical test (4) proves that neighbor physically unique.
This includes every free or owned upper-near contact and
the genuine aligned G=1 endpoint.

At the upper-left point F, every strict northwest incoming
normal has (11). The complete original height interval gives
the fixed reserves

    3/4-2A>3/4-2(31/120)=7/30,

    (1-A)^2-1/4
      >(89/120)^2-1/4=4321/14400.             (17)

Thus Theorem 3.1 proves physical uniqueness for the entire
strict far-upper contact, before splitting C-owned and free
HC or any CK owner/type. The two actual H leaf alternatives
are both included.

This is a local replacement for a whole physical-mask
dependency in those upper-vertex features. It is stronger
than assuming a one-atom positive circle resultant: the
second physical circle corner itself is excluded, even if
it would have had zero individual force weight.

## 5. Exact original-domain scope and honest assembly boundary

The full original source of (14)--(15) is

    POSITIVE_B_OWNED_ROOT_GENUINE_NEIGHBOR_NORMAL_FORM.md
    SHA256 93cbef188a875c95b56f51498ebb6b55633da09f34ce311740f370e1586849ce,

with its complete independent acceptance

    REVIEW_POSITIVE_B_OWNED_ROOT_NORMAL_FORM_TOPOLOGY_INDEPENDENT_2026_10_27.md
    SHA256 705bad0d0719b4712af8e6ba8c20f02715d566ad0832a5b10122f2d5df86df3d.

That fresh source retains the original graph

    HK, HB, BK, HC, CK, HL_H, BL_B,

with genuine H4/K3/B3/C2, both occupied S leaves, the actual
singleton B-owned HB and all other physical packing units.
Its two explicit B hypotheses are actual nonparallelity and
positive radial concurrence. Neither is proved by the local
annulus theorem. A separate accepted theorem may supply the
positive-concurrence hypothesis, as in the current fresh
original applications.

In any legitimate continuation of that full chart, once an
actual HC upper-vertex application and its strict normal
have been established, Sections 3--4 remove the physical
two-corner C alternative with no additional degree, load,
K mask or BK owner premise. In particular the far contact
may be C-owned or free, and CK may be singleton or shared
with its whole original mean.

This source does not claim that every original HC contact
is an upper-vertex contact. An H-owned top-side application
has its own complete support-point interval and is a separate
physical case. It also does not prove the original central
contact singleton or choose a new HC normal to create the
strict northwest sign.

If an earlier manuscript assumed physical C uniqueness
before proving its whole HC direction cover, a new assembly
must first establish that direction cover on the whole C
mask or rederive the needed physical features separately.
The present local result cannot be used circularly to
justify the antecedent of its own far-vertex chart.

Consequently this proof supplies the exact stated physical
mask implication, not a claim that the missing old global
C-mask source has been restored or that an entire original
graph gate is closed.

## 6. Complete present foundations and exact arithmetic

All physical arguments are given above. The present original
sources, read completely for the exact conventions and
genuine-leaf data, are:

| Source | SHA256 | Exact use |
| --- | --- | --- |
| C7_FORCE_POLYGON.md | d50d8ca48ea19156175e651bfa74be30ef3e58065ec14d8d1834670a41559089 | Physical two-corner classification and unshareability of a containing-circle point, both reproduced in Section 2 |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Actual common supporting normals, full singleton/free/shared physical contacts and unchanged real means |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676 | Genuine occupied S leaf and its actual radial application d times its direction |

The exact whole identities used in the proof are the four
support levels in (6), the inner-face norm (8), the two
different genuine-leaf expansions (12)--(13), and
(1+delta)^2-(1+delta^2)=2delta. The fixed rational
reserves were independently replayed with Fraction arithmetic:

    3/4-2(31/120)=7/30,
    (89/120)^2-1/4=4321/14400,
    (5/8)^2-1/4=9/64,
    1-31/120=89/120.

The third value is the aligned-row reserve even under the
common stronger restriction A<3/8; its complete aligned
theorem itself permits every A<1/2. The proof checks entire
linear or monotone quadratic intervals and contains no
finite pose list, interval subdivision or computational
exclusion certificate.

A full independent review must preserve the actual inward
normal sign, both physical circle corners regardless of
weights, every inner and outer side/vertex, the full
shared-mean interval, both genuine leaf equations, the
strict threshold boundaries, and the stated noncircular
original-caller scope.

No existing frozen source, original gate, ledger, remote
branch, Lean file or CI workflow is changed.
