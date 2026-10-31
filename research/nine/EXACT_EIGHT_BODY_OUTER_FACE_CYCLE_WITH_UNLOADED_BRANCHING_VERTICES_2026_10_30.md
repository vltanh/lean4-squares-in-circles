# An exact outer-face eight-cycle with unloaded branching vertices

Date: October 30, 2026 UTC.

**Status: complete proposed exact physical diagnostic and completion
check, awaiting independent review. This is an eight-square example,
not a nine-square counterexample to the target bound.**

A compatible physical force-and-torque stress can have an outer-face
cycle of length eight when its circle-clear cycle vertices have
additional positive edges. The example below uses only actual side
contacts. Its central four-square junction also proves directly that
no ninth unit can be added, even in the larger target disk.

## 1. Eight actual units and their exact containing radius

All units are axis-aligned. Their centers are

| Body | Center |
| --- | --- |
| E | (3/2,0) |
| N | (0,3/2) |
| W | (-3/2,0) |
| S | (0,-3/2) |
| NE | (1/2,1/2) |
| NW | (-1/2,1/2) |
| SW | (-1/2,-1/2) |
| SE | (1/2,-1/2) |

For every two distinct centers, at least one coordinate difference
has absolute value at least one. The corresponding open square
interiors are therefore disjoint.

The central four units have union [-1,1]^2 and farthest-corner
squared norm two. The other four units have farthest-corner squared
norm exactly

    q0=17/4<Q=1105/256.

Their eight actual circle corners are

    E: (2,±1/2),       N: (±1/2,2),
    W: (-2,±1/2),      S: (±1/2,-2).

All other corners have smaller norm. Thus precisely E,N,W,S are
physical boundary squares of this configuration in D_(sqrt(q0)).
The radius sqrt(q0) lies in the research window
79/40<=R<=sqrt(Q).

## 2. Complete positive pair list and actual means

Give each of the eight circle corners coefficient

    lambda=1/8.

The total circle coefficient is one. Give every pair in the following
table positive magnitude mu=1/2. A directed pair i to j uses its
listed normal n as the outward-to-neighbor normal at i, the opposite
normal at j, and the same actual point p at both bodies.

| Directed pair | n | Actual application mean p |
| --- | --- | --- |
| E to NE | (-1,0) | (1,1/4) |
| E to SE | (-1,0) | (1,-1/4) |
| N to NE | (0,-1) | (1/4,1) |
| N to NW | (0,-1) | (-1/4,1) |
| W to NW | (1,0) | (-1,1/4) |
| W to SW | (1,0) | (-1,-1/4) |
| S to SW | (0,1) | (-1/4,-1) |
| S to SE | (0,1) | (1/4,-1) |
| NE to NW | (-1,0) | (0,1/2) |
| NW to SW | (0,-1) | (-1/2,0) |
| SW to SE | (1,0) | (0,-1/2) |
| SE to NE | (0,1) | (1/2,0) |

These are all twelve positive body pairs. Each listed point is the
midpoint of the actual shared side segment. The first eight shared
segments have length 1/2; the final four have length one. All means
are in the relative interiors of their actual segments. If endpoint
atoms are required, each magnitude 1/2 at such a mean is equivalently
two positive magnitude-1/4 atoms at the actual segment endpoints.

All listed normals are true common supporting normals, and each
center projection gap is exactly one. Other physical contacts,
including the opposite central vertex contacts at the origin, have
zero selected force and remain occupied.

## 3. Full force and torque verification

Use the physical convention

    2*sum lambda*z + sum mu*n = 0

at each body. Circle atoms act at z. Since their forces are radial,
each has zero origin moment. Write p cross F=p_x*F_y-p_y*F_x.

### 3.1 The outer-body orbit

At E, the two circle terms sum to

    2*(1/8)*[(2,1/2)+(2,-1/2)]=(1,0).

Its two positive contact forces sum to (-1,0). Its two contact
origin moments are respectively

    (1,1/4) cross (-1/2,0)=1/8,
    (1,-1/4) cross (-1/2,0)=-1/8.

Thus its complete force and origin moment vanish. Rotation by
quarter turns preserves the whole configuration, weights and
contact data and proves the same equations at N,W,S.

### 3.2 The central-body orbit

At NE, the forces from E,N,NW,SE respectively are

    (1/2,0), (0,1/2), (-1/2,0), (0,-1/2).

They sum to zero. Their actual origin moments are

    -1/8, 1/8, 1/4, -1/4,

respectively, and also sum to zero. NE has zero circle weight.
Quarter-turn rotation proves the same full equations at NW,SW,SE.

At every body, zero total force and zero origin moment also imply
zero moment about that body's actual center, because

    sum (p-c) cross F=sum p cross F-c cross sum F.

This verifies a normalized positive physical force-and-torque stress
directly. It is not a claim that this eight-body configuration is a
global minimizing packing.

## 4. A compatible outer-face C8 with true degree-four unmarked vertices

The positive graph contains the spanning cycle

    E -- NE -- N -- NW -- W -- SW -- S -- SE -- E,       (1)

and the four additional edges of the central cycle

    NE -- NW -- SW -- SE -- NE.                        (2)

Every listed mean is also the midpoint of its two body centers.
Thus the original center-to-mean strands are precisely straight
center-to-center segments. These segments have no crossings away
from common endpoint centers. Cycle (1) is the actual outer-face
boundary, while (2) lies inside it. This is a compatible physical
embedding without any new routing or stress selection.

The graph is biconnected: it contains the spanning simple cycle (1),
whose deletion of any one vertex remains connected, and the added
edges cannot destroy that property. Its exact counts are

    8 vertices, 12 positive body pairs,
    4 positively loaded outer vertices of true degree two,
    4 unloaded circle-clear central vertices of true degree four.

All four marked boundary bodies have their original spokes to the
containing circle. Nevertheless the unmarked vertices of the
outer-face C8 are not true-degree-two transmitters. Their additional
positive central edges cannot be dropped from their full equations.

Consequently this is a concrete obstruction to extending the
compatible marked-cycle bound m<=7 to every outer-face boundary
using force, torque and planarity alone. It violates precisely the
full-degree condition required for propagation through its unmarked
vertices. It is not a counterexample to that theorem.

## 5. No ninth unit fits even in the target disk

Keep the eight units fixed, and allow a hypothetical additional
unit to have an arbitrary independent orientation. The following
argument uses only the central block and the original four side
units; it does not use the displayed stress.

Every unit contained in D_(sqrt(Q)) has center norm strictly less
than M=91/60, since its farthest-corner squared norm is at least
|c|^2+|c|+1/2 and

    M^2+M+1/2-Q=31/57600>0.

For any unit outside the central four-square block B=[-1,1]^2,
its open radius-1/2 incircle must avoid int(B). Hence

    dist(c,B)>=1/2.                                     (3)

A center outside both coordinate intervals would have

    |c_x|=1+s, |c_y|=1+t,
    s,t>0, s^2+t^2>=1/4.

It would therefore satisfy

    |c|^2>=2+2*(s+t)+s^2+t^2>=13/4>M^2,

contrary to the center bound. A center inside both intervals also
contradicts (3). Thus every additional center belongs to one of
the four caps

    x>=3/2, x<=-3/2, y>=3/2, y<=-3/2,
    x^2+y^2<M^2.

Each cap has squared diameter at most

    (M-3/2)^2+4*(M^2-9/4)=29/144<1.                  (4)

Distinct physical unit centers have distance at least one by their
open incircles, so each cap has capacity one. The actual original
units E,W,N,S already occupy those four caps. No ninth unit can
be added anywhere in the larger target disk.

This is the central-junction capacity argument at translation zero,
included here in full so that the diagnostic's nine-body boundary
does not depend on an unstated completion claim.

## 6. Exact scope

The example proves that a complete compatible physical stress can
have a biconnected eight-body block and outer-face C8 with unloaded
branching vertices. It does not exhibit nine units below Q, does
not invalidate the marked-cycle theorem's genuine degree premise,
and does not show that an arbitrary such eight-body block has
capacity eight. The latter broader task needs geometric control
of non-junction branching cores while retaining the ninth unit.

All coordinates, means, weights, normal directions, moment sums and
capacity constants above are exact. No numerical pose search, Lean
compilation, CI run, original ledger mutation, metadata change or
remote publication is asserted here.
