# Every short cycle with isolated transmitters has central capacity one

Date: October 30, 2026 UTC.

**Status: complete proposed hand scope extension and whole-family
transfer, awaiting independent full review.**

This source removes an unused circle-load premise from the accepted
width-one three-edge path theorem and combines both actual transmitter
widths with the accepted two-middle-boundary path theorem. The result
applies simultaneously to every compatible simple positive cycle on
at most seven bodies whose unloaded vertices are isolated. Its entire
central free union has capacity at most one.

This is a completion-location theorem. It does not exclude a proposed
extra in an exterior channel pocket, and it does not close the remaining
seven-body parent gate.

## 1. Original-domain statement

Put

    Q = 1105/256, M = 91/60.

Keep actual unit squares, with disjoint open interiors, in the same
unchanged disk about the origin, in the original window

    79/40 <= R <= sqrt(Q).

Keep a compatible selected physical certificate, including its actual
force and angular equations, original point normals, diagonal-avoidance
convention, all owned-side application means, full physical circle masks,
and the compatible plane embedding with its exterior circle spokes.

Let the entire positive component be a simple cycle on n bodies, where

    3 <= n <= 7.

Assume that at least three bodies have positive total circle load and
that no two unloaded vertices are adjacent on this original cycle.
Here unloaded means that its total circle coefficient is zero. It does
not imply physical circle clearance. Since this is the entire positive
component, every body has true positive pair-force degree two.

**Theorem 1.** Every pair of distinct actual core centers satisfies

    |c_i-c_j| < 3.                                     (1)

**Theorem 2.** The whole central free union enclosed by this actual
physical contact ring contains at most one additional interior-disjoint
unit square.

The second statement counts all bounded free components together.
Every proposed extra must retain its actual bounded-side winding label;
additional zero-weight physical contacts may subdivide the region but
do not create a second capacity allowance.

**Seven-body consequence.** In an actual nine-unit completion of any
such seven-cycle, at least one of the two original additional units
lies in an actual exterior singleton-transmitter pocket. All direct
loaded-to-loaded exterior pockets are empty. This consequence includes
every side/diagonal assignment, every placement of the isolated
transmitters, and every physical zero-weight circle contact.

## 2. The local three-edge lemma does not require its distant endpoint to be loaded

Consider four distinct actual bodies in the consecutive order

    A -- B -- U -- C.                                  (2)

Assume that U is the original unloaded degree-two transmitter, while
B and C are loaded. For the original full simple-cycle caller in
Section 1, A may be loaded or unloaded. No change to A's actual force,
circle weights, physical frame, or contact with B is made.

**Local lemma.** Under these hypotheses and the original whole-cycle
properness premises, the actual endpoints obey

    |c_A-c_C| < 3.                                     (3)

The same local conclusion holds without any load or degree premise at
A whenever the following explicit local geometric and force premises
have independently been supplied:

1. B,C are physically boundary squares. The actual B--U--C channel
   has full reserve w=1 or w=sqrt(2), unchanged applications
   P_C=P_B+w*d, and common signed support unit normal d.
2. With e perpendicular to d directed away from the origin, the
   channel line has e.P_B=e.P_C=h>0. Its actual endpoint centers
   have nonnegative e-coordinates and opposite signed d-coordinates.
3. In the diagonal case, d is an actual own side axis of B,C under
   the compatible original diagonal convention. B retains its true
   two nonparallel positive pair forces, its complete positive
   circle resultant, and the original proper concurrence.
4. A is a contained unit square, disjoint in open interior from
   the other units, with the original physical A/B application and
   its original common support normal.

There is no claim for an arbitrary force-free mixed path when these
local properness and channel-height premises have not been proved.

### 2.1. Supply of the local premises from the whole component

SIMPLE_CYCLE_LOADED_FORCES_NONPARALLEL.md applies to the entire positive
cycle whenever it has at least three loaded vertices. It explicitly
includes a loaded vertex with two unloaded neighbors. In particular
the two true pair forces at B are nonparallel even when A is unloaded.
It retains all original circle corners, individual zero weights and
owned-side means.

SIMPLE_CYCLE_CONVEX_FORCE_POLYGON.md then gives proper actual
concurrences at every load and exact contraction of each genuine
unloaded run. Its Section 5 supplies the channel line's positive
outward height, nonnegative endpoint-center heights and opposite
longitudinal center signs for B--U--C. Those statements concern the
entire channel between B and C; they do not require B's other immediate
neighbor A to have positive circle load.

The original full degree-two force and angular equations at U give
its side width one or diagonal width sqrt(2). All applications remain
their original means. The diagonal convention supplies the endpoint
side axes when the latter width occurs.

Thus each local premise above is supplied literally by the original
whole component, with A's true load status unchanged.

### 2.2. The diagonal proof already has the required endpoint scope

LOADED_INTERMEDIATE_DIAGONAL_PATH_DIAMETER.md proves (3), and its
Section 6 expressly states that no circle equation at A entered
the proof. It extends the conclusion to a merely contained endpoint
A once the listed local channel and properness premises are supplied.
Section 2.1 supplies precisely those premises.

For clarity, the complete proof uses A in only the following ways.
If R<sqrt(17)/2, the universal center bound immediately gives (3).
Otherwise a hypothetical distance at least three gives

    89/60 < |c_A|,|c_C| < 91/60.

In the actual diagonal frame, boundary endpoint C is localized to
0<=c_C,y<3/20 and c_C,x>22/15. The distance assumption and whole-square
containment then put the whole A in x<-2/3. The original B circle
corner and proper concurrence restrict its actual A-contact:
the bottom side and bottom-right vertex lie to the right of that
whole-A wall, while the remaining bottom-left support contradicts
the unit support lower bound of A.

In that last alternative the original support vector v has positive
components with v_2/v_1<4/15. The source proves

    v.(P-c_A)/v_1 < 11/24 < 1/2,

whereas the same original application gives

    v.(P-c_A)=H_A(v)>=|v|/2>=v_1/2.

Containment and actual support are sufficient at A throughout. B's
proper concurrence and C's boundary status remain essential and are
retained.

### 2.3. The same endpoint removal in the full width-one proof

The stated theorem in FOUR_C6_LOADED_INTERMEDIATE_SIDE_PATH_DIAMETER.md
lists A,B,C as loaded. I read and reconstructed its full proof,
including all three radius ranges and all of the actual B
circle-corner alternatives. Its displayed proof requires no circle
contact or force equation at A. The following is the complete
dependency check, so this extension does not silently replace a
loaded-body equality by containment.

First, actual support gives

    P_C=P_B+d, |d|=1,
    d.(z-P_B)<=0 for every z in B,

and therefore exactly

    dist(P_C,B)=1.                                    (4)

This retains every original side mean, including its endpoints.

The proof for R<sqrt(17)/2 again uses only the universal contained
center bound. In the other case, suppose |c_A-c_C|>=3.
In each original closed radius range, choose its unchanged center
bound M_j:

| R^2 range | M_j | lower q_* | k_* | j_* | L |
| --- | --- | --- | --- | --- | --- |
| [17/4,429/100] | 151/100 | 17/4 | 43/50 | 18/25 | 6 |
| [429/100,431/100] | 303/200 | 429/100 | 5/6 | 23/30 | 20/3 |
| [431/100,Q] | 91/60 | 431/100 | 33/40 | 39/50 | 55/8 |

The source uses actual boundary equality only at C to prove its
own-frame estimates x>59/40 and |y|<7/50. The horizontal-owned
support is excluded because its unchanged B application would lie
inside radius 129/200, whereas every point of the boundary square
B has radius at least R-sqrt(2)>129/200. Thus C's original application
is its inward upper or lower vertex; reflection gives the upper one.

Next, under the supposed far distance, write c_C=r*e_0 and define
the wall angle by

    cos(theta)=(9-M_j^2-r^2)/(2*M_j*r).

The wall frame is

    f=cos(theta)e_0-sin(theta)J(e_0),
    n=sin(theta)e_0+cos(theta)J(e_0).

Every use of A before the wall conclusion is exactly one of:

- |c_A|<M_j and |c_A-c_C|>=3;
- its actual unit-square radial frame and the containment inequality
  rho^2+rho(cos(psi)+sin(psi))+1/2<Rbar, where
  Rbar=M_j^2+M_j+1/2>R^2;
- the support halfwidth of its actual frame.

These prove the strict whole-square wall

    A subset {p:n.p<1/2}.                             (5)

In particular no equality |z_A|=R or positive circle coefficient
at A is used. The proof's angular interpolation is a scalar
containment estimate, not a replacement of A by a boundary square.

From this point A appears only once: its actual contact with B and
(5) imply

    min_(p in B) n.p <= 1/2.                          (6)

All subsequent quantities belong to B,C and their unchanged channel.
The source localizes P_C=(k,j) to

    k>k_*, j<j_*, 0<k<6/5, j>9/20,

and uses the already supplied proper channel-center signs to put
c_B in the upper-left wall quadrant. The complete boundary-square
screen then proves dist(P_C,B)>1, contradicting (4). Its exhaustive
alternatives are:

| Actual B circle-corner alternative | Uniform separating argument |
| --- | --- |
| P+v | The fixed positive-definite quadratic completion gives the squared reserve 1289/318400>0 and a horizontal gap above one. |
| P+u+v with lowest height l<=0 | The original circle corner gives max_B f<=-1/2, while k>33/40. |
| P+u+v, 0<=l<=1/2, 15c-8s>=0 | The actual unit direction (15,-8)/17 has gap above one; the three exact endpoint reserves 225q_*-E(L) are positive, and the final unnormalized gap exceeds 17. |
| P+u+v, 0<=l<=1/2, 15c-8s<=0 | B's original own-side separator has gap above one; the three whole orientation-interval lower bounds are 4011/4000, 807/800 and 631/625. |

The circle-corner ties, face joins and complete owned-side intervals
are included in those alternatives. Nothing after (6) uses A's
boundary status, load, or degree. Consequently the unchanged full
proof establishes (3) with A merely contained and actually touching
B, under the explicit channel premises in Section 2.

This is the only new scope extension of the imported three-edge
proof. No original load at B or C is removed.

## 3. Uniform pair cover for every cycle of length at most seven

Take any two distinct actual core bodies. Their shorter graph path
on the same original cycle has length at most three.

If it has one edge, an actual common point p gives

    |c_i-c_j| <= |c_i-p|+|p-c_j| <= sqrt(2) < 3.

If it has two edges, the same actual-contact estimate and the
triangle inequality give a bound at most 2*sqrt(2)<3.

It remains to consider a three-edge path

    S_0 -- S_1 -- S_2 -- S_3.                         (7)

There are only two logical possibilities, covering every actual
load pattern without an enumeration of cyclic placements.

If both middle bodies S_1,S_2 are loaded, they physically touch
the circle. TWO_MIDDLE_BOUNDARY_PATH_DIAMETER.md applies to their
unchanged four-body contact path and gives |c_0-c_3|<3.
Its theorem imposes no boundary, load or degree premise at either
endpoint.

Otherwise exactly one of the middle bodies is unloaded. They
cannot both be unloaded because the original unloaded vertices
are isolated. Reverse (7), if necessary, so the unloaded middle
body is S_2=U. Then B=S_1 is loaded. The other neighbor C=S_3
of U is loaded as well, again by isolation. A=S_0 may have either
load status. The complete local lemma in Section 2 applies to
A--B--U--C and gives the same strict endpoint bound.

These alternatives cover every pair of actual cycle centers.
They prove Theorem 1 without assigning a boundary contact to an
unloaded endpoint and without deleting or contracting a physical
square.

## 4. Whole central free-union capacity

Use the same original centers and actual contact applications p_i
to form the closed occupied center/contact chain

    Gamma = c_0 p_0 c_1 p_1 ... c_(n-1) p_(n-1) c_0.

The compatible physical embedding gives its actual bounded-side
enclosure. For weak junctions, fix compact inner portions of every
proposed central extra before taking arbitrarily small Jordan
routings of the same occupied chain. Those compact sets have positive
distance from the closed core union, so their winding labels persist.
This is the unchanged weak enclosure convention in the accepted
SHORT_DIAMETER_CONTACT_RING_CENTRAL_CAPACITY_ONE.md.

That geometric theorem requires actual unit squares in D_(sqrt(Q)),
actual consecutive contacts, and every actual core-center distance
strictly below three. Theorem 1 supplies the last premise; the
original configuration supplies all the others. Its conclusion
therefore gives at most one enclosed extra in the entire central
free union.

No convexity of the actual center chain is required. In particular,
the physical curve has not been replaced by the contracted force
polygon or the convex hull of the core centers.

## 5. All remaining no-long seven-cycle families share the same completion obstruction

For n=7, the no-adjacent-unloaded premise covers simultaneously:

- four loads and three isolated transmitters;
- five loads and two isolated transmitters, in every cyclic placement;
- six loads and one transmitter;
- seven loaded bodies.

Every side/diagonal choice and physical circle mask is retained.
The separate weighted occupied-arc theorem may already remove some
diagonal assignments, but no such removal is needed for Theorems 1
and 2.

In a nine-unit packing there are two actual extras. Since at most
one is central, at least one is in an exterior region. The complete
physical routing of SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md, Sections
1--2, applies to the same whole simple positive component. Every
direct loaded-pair pocket is empty. All other regions are the
actual pockets at the singleton transmitters, including any
subdivisions by zero-weight contacts or physical boundary contacts
on those transmitters. Hence at least one actual singleton pocket
contains a whole extra.

If every body is loaded, there is no such pocket, so the two-extra
completion is impossible; this is consistent with the previously
accepted all-boundary seven-cycle result. If at least one genuine
transmitter remains, this source leaves its actual exterior
occupancy and any simultaneous central occupancy intact.

In particular, with six loads, the necessary location is one
central extra and one exterior extra once the separately accepted
capacity-one theorem for that sole channel is applied in its radius
range. The present source does not infer that those two original
units cannot coexist. Likewise it does not silently add capacity
counts from different regions as though their maxima could not
occur together.

Long-run seven-cycle families are outside the isolation premise.
For a path whose two middle bodies are both unloaded, the pair-cover
argument would fail exactly at that step. The already proved long
pair has endpoint distance at least three, so no below-three
extension to that case is asserted.

## 6. Frozen dependencies and verification boundary

The complete sources imported above have these exact SHA256 pins:

| Source | SHA256 | Exact use |
| --- | --- | --- |
| FOUR_C6_LOADED_INTERMEDIATE_SIDE_PATH_DIAMETER.md | deb99ce00828e211a083cc4575ede1b4e506f6007575f9ec9eec91aff177bbf5 | Entire width-one path proof; only its unused load premise at A is removed after the complete dependency check in Section 2.3. |
| LOADED_INTERMEDIATE_DIAGONAL_PATH_DIAMETER.md | f4121e6416f025fc18b00b0fd558488112692bd6d2819cef4e137ec8136289f7 | Entire diagonal path proof and its explicit merely-contained-A extension. |
| TWO_MIDDLE_BOUNDARY_PATH_DIAMETER.md | 1a368789f5c4ccac4ebd3c7a50061ec10f5b1a9d773ade1de12b8eec3c877b61 | Three-edge contact path with both actual middle bodies physically boundary. |
| SIMPLE_CYCLE_LOADED_FORCES_NONPARALLEL.md | cd2a8c765c181ac803d8ee1c8672d1a8ceea3591248cbca449ef3653b4be6ebe | Full loaded-body nonparallelism, including a load with two unloaded neighbors. |
| SIMPLE_CYCLE_CONVEX_FORCE_POLYGON.md | 5dac2a88ac992ab72247e76eafcc5ee0fb1ad57a2ec4b11015d0caf07ec87635 | Actual proper channel geometry for the original whole component. |
| SHORT_DIAMETER_CONTACT_RING_CENTRAL_CAPACITY_ONE.md | 10d0ed2343f23c51e7ab165542aad6fd3ce72405c78a002511633c2a958b6a03 | Entire geometric central free-union transfer, with its original winding convention. |
| SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md | f9a008a8cebb02825891d773afeafa0fa953f5c499988bdaae0bac947ff6f1e7 | Full actual central/exterior routing and empty direct boundary-pair pockets. |

The first five sources and the complete central-transfer and routing
sources were fully read for this scope extension. The older imported
geometric inequalities remain at their accepted complete scopes;
this manuscript does not replace a separate global prerequisite
audit for the underlying selected-certificate construction.

This work used continuous proofs and exact fixed inequalities.
It performed no numerical pose search, mesh, coefficient packet,
normal reselection, mean replacement, force deletion, original-gate
mutation, Lean compilation, CI execution, or remote publication.
