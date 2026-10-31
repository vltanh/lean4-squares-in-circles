# n=9 TREE.F2: ALL positive trees have R^2=17/4 and exactly six central-incidence cases

**Status:** new exhaustive hand reduction of the entire positive-tree branch; independent mathematical audit and Lean verification pending. The six cases below include their continuous geometric parameters and **all unstressed-square completions**. This manuscript does not assert that those six completion problems are all solved.

**Inputs:** TREE_BODY_LOCALIZATION.md (TREE.F1), the physical radial bridge normal choice, and the previously proved star exclusion in SMALL_TREE_STRESS_CORES.md. All results retain the explicit radius window

    79/40 <= R <= sqrt(Q),  Q=1105/256.

A global n=9 application requires the declared n=8 lower-window dependency, or a separate proof of that lower window.

## 1. Precise theorem

Let T be any nontrivial connected **tree component** of the chosen positive physical body-pair stress graph. Then:

1. R^2=17/4.
2. Every unloaded vertex square contains the disk center 0 on its boundary, never in its open interior.
3. Every loaded vertex square is radial side-normal type S, centered at (3/2)e and contacting its unloaded neighbor(s) at e, for some unit radial vector e.
4. There are k=2,3,4 unloaded bodies. If s contain 0 in the relative interior of a side and v contain 0 at a vertex, the complete list is

       (s,v) = (2,0), (1,1), (1,2), (0,2), (0,3), (0,4).

This is a six-case **exhaustive geometric inventory for every positive tree** in the stated radius window, not a selection of small angle intervals. The cyclic-body-graph branch is separate and remains open.

## 2. Exact constants and the local radial contact rule

Write

    A=sqrt(R^2-1/4)-1,   B=R-sqrt(2).

TREE.F1 gives 9/10<A<51/50 and 1/2<B<7/10. For A>1 put a=A-1; then

    0<a<1/50,
    d=2 sqrt(a)<3/10,
    c=sqrt(A^2-1)<3/10,
    c>a,  c+a<1.

The inequalities are exact: 4a<2/25<9/100; A^2-1<101/2500<9/100; and c^2-a^2=2a>0.

A **radial outward contact** of a square U containing zero is a point p=r e, r>0, with e.x<=r on U. If p lies in the relative interior of a side, e is that side's unit outward normal. Otherwise p is a vertex. The contact force in the stationarity equation of U is a positive multiple of e.

By TREE.F1, every off-origin positive neighbor of an origin-containing unloaded body is one of:

- a loaded S terminal, with contact radius A;
- a loaded D terminal, with contact radius B;
- when A>1 only, a one-step unloaded transmitter leading to S, with inward contact radius a=A-1.

Contacts between two origin-containing bodies have application point **zero**. Indeed both bodies contain zero, so their separating line passes through zero; the radial force condition also makes its contact point parallel to its normal, forcing that point to be zero.

## 3. A D terminal requires an origin-interior neighbor

**Lemma F2.1.** If a loaded D terminal occurs in T, its unloaded neighbor contains zero in its open interior.

*Proof.* TREE.F1 shows that a D terminal has one neighbor and its off-origin bridge point p=B e is in the relative interior of a side of that neighbor (the chosen stress has no off-origin vertex/vertex bridges). In axes with e horizontal, the neighbor has horizontal interval [B-1,B]. The contact (B,0) lies in the relative interior of its vertical side, so zero is strictly inside its vertical interval. Since 0<B<1, zero is also strictly inside [B-1,B]. Thus it is in the square's open interior. QED.

In particular, if all origin-containing bodies meet zero only on their boundaries, no D terminal occurs.

## 4. Exhaustively exclude an origin-interior body

**Lemma F2.2.** No unloaded vertex of T contains zero in its open interior.

*Proof.* Suppose H contains zero in its interior. No other physical square can contain zero even on its boundary, because its interior approaches zero and would intersect int(H). Hence H is the unique origin-containing body of T.

By TREE.F1 every other unloaded body is one step away from H and has one outgoing S terminal. Thus T is a subdivided star with arms of length one or two. If A<=1, no origin-avoiding unloaded body is possible and this is an ordinary star, excluded by SMALL_TREE_STRESS_CORES.md. The same star exclusion applies for A>1 if there are no two-edge arms.

It remains to treat A>1 and an arm with intermediate unloaded body. Its contact on H is a radial support point p of norm a=A-1, where 0<a<1/50. Every positive force on H is outward radial at radius a, A or B. There are exactly two geometric cases for p.

### Case I-V: p is a vertex of H

Choose H's own axes/signs so

    p=(p1,p2),   p1>0, p2>0, p1^2+p2^2=a^2,
    H=[p1-1,p1] x [p2-1,p2].

The strict signs follow because zero is in int(H). Each pi<a. The near vertex p has radius a. Each adjacent vertex has squared radius 1+a^2-2pi, strictly between (1-a)^2 and 1+a^2, hence larger than B^2 and a^2 and smaller than A^2=(1+a)^2. The opposite vertex has squared radius greater than 2(1-a)^2>A^2.

A radial support point in a side's relative interior has radius equal to that side's distance from zero. These four distances are p1,p2,1-p1,1-p2. The first two are <a; the last two are >1-a>7/10>B and <1<A. None equals a, A or B.

Therefore the **only** possible positive contact on H is its vertex p. All such radial forces are parallel with the same sign and cannot balance. Contradiction.

### Case I-E: p is in a side's relative interior

Choose H's axes so

    p=(a,0),   H=[a-1,a] x [t,t+1],   -1<t<0.

A direct S contact cannot be in a side interior, because all four side distances of an origin-interior unit square are <1<A. On the right-hand vertices, |p|=A would require |y|=sqrt(A^2-a^2)=sqrt(1+2a)>1, impossible for this vertical interval. On the left-hand vertices it requires

    y=+d or -d,  d=2 sqrt(a)<3/10.

Both signs cannot be vertices because the side length is one while 2d<1. Thus at most **one** S contact exists, at one left vertex.

D contacts can only occur on horizontal sides: the distances to vertical sides are a and 1-a, neither B. Any other short-arm contact likewise has vertical normal: the opposite vertical side has distance 1-a != a, and no other vertex has radius a.

The known contact at (a,0) has a positive horizontal force. The only possible contact with negative horizontal force is the one left-vertex S contact, so it must exist. Reflect y so it is at (a-1,d). Then H's vertical interval is [d-1,d]. Its bottom-side distance is 1-d>7/10>B and >a. Consequently neither a D contact nor a short-arm contact can supply a downward force. There is no second S vertex. Every remaining force has nonnegative vertical component, while the S contact has strictly positive vertical component. They cannot balance. Contradiction.

The interior/side alternatives for p are exhaustive. Hence H cannot exist. QED.

## 5. Boundary vertex forces the unique tree radius

By TREE.F1 some unloaded body contains zero. By Lemma F2.2 zero is on its boundary.

**Lemma F2.3 (vertex-origin body).** If an unloaded square U has zero at a vertex, then A=1.

*Proof.* Rotate U to [0,1]^2. Its nonzero radial outward support points are exactly

    (1,0), (0,1), (1,1),

with radii 1,1,sqrt(2). For example, if both coordinates of p are positive, support in direction p forces p=(1,1); if only one is positive, it forces the corresponding axis endpoint. The available positive-contact radii from Section 2 are A in (9/10,51/50), B in (1/2,7/10), and possibly a in (0,1/50). Only A=1 can match this support-point list.

If A!=1, all positive contacts on U would therefore be at zero. Each of their outward normals has nonpositive components, and at least one component is negative. Their positive weighted sum has negative scalar product with (1,1), contradicting force equilibrium of unloaded U. Thus A=1. QED.

## 6. Boundary side also forces the unique radius

**Lemma F2.4 (side-origin body).** If an unloaded square U has zero in a side's relative interior, then A=1.

*Proof.* Put

    U=[-alpha,1-alpha] x [0,1],  0<alpha<1.

All positive contacts at zero have vertical normal (0,-1). By Lemma F2.1 there are no D terminals anywhere if all origin-containing bodies have only boundary incidence, as now known.

The nonzero radial outward support points of U can only be

    (-alpha,0), (1-alpha,0), (0,1),
    (-alpha,1), (1-alpha,1).

This follows by considering side interiors and vertices separately. The displayed list includes all such points, regardless of square angles elsewhere.

- **If A<1:** there are no off-origin unloaded transmitters, by TREE.F1. A direct S contact must be one of the two bottom vertices, with alpha=A or 1-alpha=A. Since A>9/10, at most one condition can hold. Its force has a nonzero horizontal component, which cannot be balanced by the vertical zero-point forces. If neither holds, there are only downward zero-point forces and these cannot balance either.

- **If A>1:** put a=A-1 and c=sqrt(A^2-1), as in Section 2. A direct S contact can occur only at a top vertex, requiring alpha=c or 1-alpha=c. A short arm can occur only at a bottom vertex, requiring alpha=a or 1-alpha=a. Since a,c<3/10, c>a and a+c<1, these four requirements are pairwise incompatible. Thus there is at most one off-origin positive contact direction. If present it has nonzero horizontal component (a bottom short arm or a noncentral top corner); the zero-point forces are vertical and cannot cancel it. If absent, downward zero-point forces alone cannot balance.

Both strict alternatives are impossible, so A=1. QED.

## 7. Complete tree radius and support geometry

**Theorem F2.5 (all-tree radius quantization).** Every positive tree component in the declared window has

    A=1,  R^2=17/4.

All unloaded bodies contain zero on their boundary; all loaded bodies are radial S terminals centered at (3/2)e, with inward force point e.

*Proof.* TREE.F1 supplies an origin-containing unloaded body. Lemma F2.2 excludes its interior incidence; Lemmas F2.3–F2.4 handle its two remaining boundary types and force A=1. At A=1 no unloaded body can avoid zero by TREE.F1. None has interior incidence by Lemma F2.2, so Lemma F2.1 excludes all D terminals. The S formula gives the stated loaded geometry. QED.

**This excludes ALL positive trees at every R in the window except sqrt(17/4)**, not merely stars or two-loaded trees. It does not exclude a full nine-square packing at that exceptional radius. That still needs its unstressed-square completion capacity.

## 8. Exactly six exhaustive central-incidence cases at the exceptional radius

Let s be the number of unloaded squares whose side interior contains zero; let v be the number whose vertex is zero. The tangent-cone interiors at zero are pairwise disjoint. Each side contributes angle pi, each vertex pi/2. Therefore

    2s+v <= 4.

There are at least two unloaded bodies: if there were only one, the component would be an ordinary positive star at A=1, already excluded. Thus s+v>=2. Solving these elementary integer inequalities gives **exactly**

| Case ID | s | v | Geometric description | Nine-square completion status |
|---|---:|---:|---|---|
| TREE.20 | 2 | 0 | Two opposed side-origin bodies, aligned side-normal path with sliders | OPEN (flat subcase previously excluded) |
| TREE.11 | 1 | 1 | One side-origin body and one vertex-origin body | OPEN |
| TREE.12 | 1 | 2 | One side body and two vertex bodies filling the complementary half-plane | OPEN |
| TREE.02 | 0 | 2 | Two vertex-origin bodies | OPEN |
| TREE.03 | 0 | 3 | Three vertex-origin bodies | OPEN |
| TREE.04 | 0 | 4 | Four quarter-angle bodies tiling a central 2x2 block | Completion theorem supplied separately |

The conditions are disjoint for the chosen physical tree component and exhaustive. Extra circle-clear or unstressed physical squares are **not** added to s,v; they remain part of the nine-square completion obligation. Continuous angles, side offsets, zero-stress obstacles and all positive load choices are retained within each case; they are not sampled or divided into an unbounded sequence of angle windows.

In TREE.20 the two tangent half-planes are complementary. Their axes agree, and their only S neighbors are the two radial terminals on the opposite normals. The component is exactly the four-square path with inner tangential offsets |tau_i|<1/2. Endpoint slider values |tau_i|=1/2 belong instead to vertex-incidence rows of this six-case table; they are not lost.

## 9. Limits, validation and next obligations

- **TREE.F2 CLOSED hand reduction:** all positive tree radii in the window are quantized to 17/4, and their physical completion problems are partitioned into the six cases above.
- **This is not all-tree exclusion.** Nonstar positive tree stresses really occur at 17/4 with fewer than nine squares; explicit regression witnesses must be preserved.
- **CYCLIC branch OPEN:** a connected selected stress component may have a cycle, where the radial bridge law does not apply to every edge. None of this tree argument is silently invoked there.
- **Remaining global goal:** prove at most eight total physical squares fit each tree case, and give a finite exhaustive sharp inequality for the cyclic branch (or one global inequality bypassing that classification).
- No Lean compilation, CI, or independent full mathematical audit was run for this derivation. Exact examples and algebraic checks are regression evidence only.