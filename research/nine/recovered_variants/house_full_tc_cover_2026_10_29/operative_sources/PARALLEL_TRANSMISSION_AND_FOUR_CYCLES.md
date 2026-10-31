# n=9 CY.CHANNEL: parallel transmission, two-loaded cycle quantization, and complete four-cycle exclusion

**Status:** new hand theorems for whole physical stress-component classes; independent audit and Lean verification pending. No graph sample or numerical orientation grid is a proof premise. The unrestricted nine-square lower bound, P.ALL and Y.ALL remain OPEN.

**Read base:** PR #11 `14b6a28c5f92224baa0e438746816800844a560e`, with the new companion ACUTE_LOADED_CONTACT_GRAPH.md (commit 690f245). Inputs are the physical force/application-point and angular equations in PHYSICAL_CONTACT_STRESS.md, not planarity of the body-pair graph.

The selected positive body-pair graph is simple after parallel same-pair contact aggregation. A body is loaded when its total circle weight is positive. A transmitter is an unloaded vertex of degree two.

## 1. A transmitter path is a shortest normal segment between its endpoint squares

**Lemma N.1 (physical normal channel).** Let a positive path connect endpoint squares A,B, with at least one internal square and every internal square an unloaded degree-two transmitter. Then there are a unit vector n, a length L>0, and actual endpoint contact points p_A in A, p_B in B such that

    p_B-p_A = L n,
    n.a <= n.p_A for every a in A,
    n.b >= n.p_B for every b in B.                         (1)

Every edge on the path has the same force magnitude and a consistent normal n. L is the sum of the intervening squares' projected widths, each exactly 1 or sqrt(2).

*Proof.* At a degree-two unloaded body, force balance gives equal opposite forces and angular balance makes the two application points collinear in their common normal. The exact square result in PHYSICAL_CONTACT_STRESS.md, Lemma 5.1, says their difference is n or sqrt(2)n, with side-normal or diagonal orientation respectively. Consecutive bodies share the same true contact point. Following the oriented path therefore telescopes the point differences and preserves the normal and force magnitude. The endpoint normals support A on its upper n face and B on its lower n face, proving (1). QED.

For any a in A,b in B, (1) gives n.(b-a)>=L, and hence |b-a|>=L. The displayed endpoint pair attains L. Thus p_B-p_A is a minimum-norm vector of the convex difference set B-A.

**Lemma N.2 (uniqueness across parallel graph paths).** Any two such transmitter paths between the same endpoint squares have exactly the same normal n and length L, regardless of their transverse contact positions or their original edge labels.

*Proof.* Euclidean squared norm is strictly convex, so a nonempty compact convex set B-A has exactly one minimum-norm vector. Each path attains it by N.1. Since L>0, the length and unit direction coincide. QED.

A direct positive A--B contact cannot coexist with a positive-length transmitter path between the same bodies: the direct contact says dist(A,B)=0, whereas N.1 says dist(A,B)=L>0. A transmitter path cannot return to its same endpoint body either: its end is on the minimum n face while its start is on the maximum n face, contradicting a positive telescoped displacement L n.

**Corollary N.3.** An unloaded degree-two vertex cannot have physically touching neighbors (even if their mutual touching carries zero stress). In particular, a degree-two vertex of a positive triangle is necessarily loaded.

## 2. The path reserves are exactly 1, sqrt(2), or 2 in the candidate disk

Assume R^2<=Q=1105/256. The usual farthest-corner inequality gives every center |c|<61/40. For a channel with internal projected widths w_i>=1,

    n.(c_B-c_A) = H_A(n)+H_B(n)+sum w_i
                >= 1+sum w_i,

while its left side is <61/20.

Three or more internal squares would give a gap >=4, impossible. Two internal squares cannot include a diagonal transmitter because 1+(1+sqrt(2))=2+sqrt(2)>61/20. Consequently every positive-length transmitter channel has

    L in {1, sqrt(2), 2},                                  (2)

and L=2 means exactly two side-normal internal squares. These are all-angle geometric consequences; no center or angle discretization is used.

## 3. Parallel forces at a loaded endpoint force radial S/D geometry

The following argument does not require the endpoint's graph degree to be one or its incident edges to be bridges.

**Lemma N.4.** Suppose a loaded square inside D_(R^2), with R^2>9/4, has all its positive pair forces parallel with the same sign and on one supporting face. Then their weighted-average application point is radially inward and the square has one of the exact geometries

    S:  c=(T-1/2)d,  p_bar=(T-1)d,  T=sqrt(R^2-1/4);
    D:  c=(R-1/sqrt(2))d, p_bar=(R-sqrt(2))d,

where d is the outward circle-load direction. In S there are two adjacent equally weighted circle atoms; in D there is one loaded outer corner R d.

*Proof.* Aggregate the parallel forces at their weighted-average point p_bar on the supporting face. Let z_bar be the normalized circle-corner average of the body. Force balance makes z_bar a positive multiple of the unit vector d opposite the aggregate contact force. The angular equation about the disk center makes p_bar parallel to d.

A unit square touching a circle of radius R>sqrt(2) has either one farthest corner, or two adjacent farthest corners; this follows immediately from the exact own-frame corner formula and its center being nonzero. An average of one or two adjacent circle corners has norm at least sqrt(R^2-1/4)=T>sqrt(2). Both z_bar and p_bar lie in the same unit square. If p_bar were a nonpositive multiple of d, their distance would be at least T, exceeding the square diameter sqrt(2). Thus p_bar=r d with r>0.

If only one circle atom is positive, its corner is R d. Direction d strictly exposes that corner: a nontrivial face in the circle tangent direction could not be contained in the disk. The opposite support point is therefore the opposite vertex. Their distance is sqrt(2), and radiality gives the D formulas.

If both adjacent circle atoms are positive, choose square axes so the center is (T-1/2,0), the two circle corners are (T,+/-1/2), and their weighted average is (T,eta). If eta>0, the unique opposite support point is (T-1,-1/2), not a positive multiple of (T,eta). This contradicts radiality; eta<0 is symmetric. Hence eta=0, the two circle weights agree, d is the horizontal side normal, and p_bar=(T-1,0). This is S. QED.

This lemma applies to the weighted-average point, not necessarily one original single pair contact. That is sufficient because convexity keeps the average on the same endpoint support face and preserves force and moment.

## 4. Every simple cycle with exactly two loaded bodies is a six-square S cycle at 17/4

Assume the explicit radius window

    79/40 <= R <= sqrt(Q).                                  (3)

**Theorem N.5 (two-loaded simple-cycle quantization).** If a selected positive component is a simple cycle and exactly two of its vertices are circle-loaded, then the component has exactly six bodies and

    R^2=17/4.

Its two loaded squares are side-normal S terminals in opposite directions, and each of the two arcs between them consists of exactly two side-normal unloaded transmitters. Every square in this six-body component is aligned with the same frame. The result does NOT exclude its completion to nine physical squares.

*Proof.* The two loaded bodies A,B divide the cycle into two arcs. They cannot be adjacent: one arc would be a direct contact while the other is a positive-length channel, contradicting N.1. Every internal arc vertex is an unloaded degree-two transmitter. By N.2 the two arcs have a common normal n and reserve L.

Both incident forces at A are parallel with the same sign, as are those at B. Lemma N.4 makes the two endpoints radial S/D bodies in opposite outward directions. Put

    A0=sqrt(R^2-1/4)-1,  B0=R-sqrt(2).

Their two inward support planes are radially located on opposite sides of zero. Their separation L is therefore one of

    2 A0, A0+B0, 2 B0.                                     (4)

The exact window gives

    9/10 < A0 < 51/50,   11/20 < B0 < 7/10.

For the lower B0 bound use sqrt(2)<57/40. For the upper use sqrt(Q)<21/10 and sqrt(2)>7/5. The A0 comparisons follow by squaring the positive terms. Thus

    1 < 2B0 < 7/5 < sqrt(2),
    sqrt(2) < 29/20 < A0+B0 < 43/25 < 2,
    sqrt(2) < 9/5 < 2A0 < 51/25.

Comparing (4) with the exact discrete possibilities (2), only L=2A0=2 survives. Hence A0=1 and R^2=17/4, and both endpoints are S. Reserve 2 on each arc forces exactly two side-normal transmitters. The cycle has 2+2+2=6 vertices, with the stated aligned frames. QED.

**Explicit survivor, not an exclusion.** In the resulting frame the endpoints are (-3/2,0),(3/2,0). Each channel has one intermediate center at x=-1/2 and one at x=1/2. Their y values need not equal zero. The application heights of the two channels have positive weighted average zero at each loaded endpoint, and each intermediate center is within 1/2 of its channel height. The complete additional-three-square capacity remains open. Do not call the six-body cycle a solid four-row.

For example, the two endpoints together with the four central squares centered at (+/-1/2,+/-1/2) form a valid six-body cycle stress at R^2=17/4 and admit the two outer vertical squares, yielding eight physical squares. This example prevents rejecting the core itself.

## 5. The ENTIRE simple four-cycle component is excluded

**Theorem N.6 (C4 exclusion).** In (3), no selected positive component can be a simple cycle on four bodies, regardless of which bodies are circle-loaded and regardless of all five other physical packing squares.

*Proof.* The component has at least two loaded bodies.

- With exactly two, Theorem N.5 requires six vertices, a contradiction.
- With exactly three, the loaded subset has a middle vertex on the three-vertex cycle path touching both other loaded bodies. Its loaded noncontact graph is disconnected, contradicting Theorem A.3 in ACUTE_LOADED_CONTACT_GRAPH.md.
- With four, partition the cycle vertices into opposite pairs. Every cross pair physically touches, so the same theorem gives a contradiction.

These are all load cardinalities. No orientation or contact-position subcase remains. QED.

## 6. Precise impact on the finite cyclic ledger

The coarse cell C1.4.b0 comprises all biconnected simple four-body components. Its complete abstract adjacency list is C4, K4 minus one edge (the diamond), and K4:

- **C1.4.b0.C4 CLOSED hand:** Theorem N.6 excludes the entire simple cycle component.
- **C1.4.b0.K4 CLOSED hand:** the loaded subset physically touches pairwise, already excluded, or use Theorem A.3.
- **C1.4.b0.DIAMOND PARTIAL:** Theorem A.3 excludes every load pattern except exactly the two nonadjacent degree-two tips loaded, with the two degree-three central bodies unloaded. This residual is OPEN. The degree-three nodes are NOT transmitters, so N.5 cannot be invoked on its two arcs.

Therefore the parent coarse cell C1.4.b0 is still OPEN, and the 57-open-coarse-cell count does not change merely because two of its three adjacency families are closed. The finer list is a proved finite subdivision of one whole cell, not an unbounded angle refinement.

The two-loaded theorem also excludes the entire two-loaded **simple-cycle** subfamilies on 3,4,5,7,8,9 bodies. It does not exclude other biconnected graphs of those orders, or components with attached trees or additional loaded bodies. The six-body survivor still requires completion capacity.

## 7. Verification boundary and remaining global work

All arguments use physical force/torque, convex minimum-vector uniqueness, exact unit-square transmission and explicit algebraic comparisons. The lower-radius premise (3) is declared, not proved here; a global application retains the existing n=8 dependency or a separate lower-window proof.

The new results are whole-component exclusions and necessary reductions, not unrestricted optimality. P.ALL, Y.ALL, the diamond residual, the six-cycle completion, other cyclic load/adjacency families, global equality necessity and independent mathematical/Lean verification remain OPEN.