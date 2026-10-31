# n=9 CY.B: finite cyclic block inventory, with exact scope and one closed cell

**Status:** hand proof of a finite **coarse** partition of the selected cyclic positive body-pair components, a global necessary load rule, and one whole-cell exclusion. It is NOT a sharp theorem for the remaining cells or a solution of P.ALL, Y.ALL or unrestricted n=9 optimality. Independent audit and Lean verification pending.

**Read base:** PR #11 head 59d0c95092a01a575a3fc078ab5c6db54107d4fc. The original physical minimizing-stress theorem and component normalization are inputs. Graphs below are the aggregated **simple positive body-pair graphs**, not the contact-point incidence graphs and not all zero-weight physical contacts.

## 1. Retain the global physical hypotheses

Choose a connected positive component G in the CYCLIC branch, with n vertices, 3<=n<=9. It contains a cycle. Every vertex represents one genuine unit square; every positive edge represents a true shared contact with positive force weight. All other 9-n physical squares remain in the completion problem, whether they are unstressed or belong to other stress components.

For the closed-cell exclusion in Section 6 we use the explicit radius window

    79/40 <= R <= sqrt(1105)/16.

The combinatorial inventory itself needs no radius bound. The tree reduction's lower-window input still requires an explicit prior n=8 theorem or an independent proof; it is not silently derived here.

## 2. A force identity forbids unloaded one-body appendages

**Theorem CY.LOAD.1.** There is no nonempty set A of unloaded vertices whose positive neighbors outside A all lie in a single body b, if A has a positive internal or boundary edge.

Here unloaded means zero total positive circle multiplier. Zero-weight physical contacts are not positive graph edges, but remain physical obstacles elsewhere in the problem.

*Proof.* Write d_e for the directed unit contact normal from i to j, and mu_e>0 for its weight. Its exact active gap is

    d_e.(c_j-c_i) = H_i(d_e)+H_j(d_e) > 0.            (1)

Every i in A has zero contact-force resultant. Dot its force-balance equation with c_i-c_b and sum over A. For an edge with both endpoints in A, its two terms sum to

    -mu_e*d_e.(c_j-c_i) = -mu_e*(H_i+H_j) < 0.

For an edge from A to b, its only included term gives exactly the same negative expression. There are no other positive boundary edges by assumption. The sum is therefore strictly negative, whereas the unloaded force equations give zero. Contradiction. QED.

**Corollary CY.LOAD.2.** Every endblock of the positive component has at least one circle-loaded body other than its unique articulation body. If the component has only one block, it has a loaded body as already known. Thus an arbitrary collection of circle-free cyclic appendages attached through one square cannot be admitted as a residual geometric case.

This is a global necessary force consequence, not a sharp radius bound. It does not say every biconnected block must contain a private loaded body: an intermediate block with two or more articulations is a different case.

## 3. Block decomposition and its exact vertex budget

Use maximal vertex-biconnected subgraphs of order at least three as **cyclic blocks**. Treat every bridge as a separate two-vertex block. Let the cyclic block sizes be

    3 <= k_1 <= ... <= k_m,

and let b>=0 be the number of bridges. The exact identity is

    n = 1 + b + sum_{i=1}^m (k_i-1).                (2)

For clarity, this does not require planarity of the body graph.

*Elementary block-tree justification.* Two distinct maximal biconnected blocks cannot share two vertices: their union would remain connected after removal of any one vertex, contradicting maximality. The incidence graph of blocks and shared articulation vertices is connected. A cycle in that incidence graph would similarly provide alternate routes around each articulation, merging the corresponding blocks into a larger biconnected subgraph; a bridge on such a cycle would not be a bridge. Hence the incidence graph is a tree. Start with a root block and attach the remaining blocks one at a time along their unique previously counted articulation. Each cyclic block contributes k_i-1 new vertices and each bridge contributes one. This proves (2).

Since n<=9, equation (2) yields

    b + sum(k_i-1) <= 8,   m>=1,   k_i>=3.          (3)

In particular m<=4. Sorting the sizes removes their ordering but does **not** identify nonisomorphic blocks, different loads or different physical square configurations.

## 4. The 21 size profiles and their 58 bridge-count cells

The complete solutions of (3) are:

| Profile | Cyclic block sizes | Allowed bridge count b | Number of cells |
|---|---|---|---:|
| C1.3 | (3) | 0..6 | 7 |
| C1.4 | (4) | 0..5 | 6 |
| C1.5 | (5) | 0..4 | 5 |
| C1.6 | (6) | 0..3 | 4 |
| C1.7 | (7) | 0..2 | 3 |
| C1.8 | (8) | 0..1 | 2 |
| C1.9 | (9) | 0 | 1 |
| C2.33 | (3,3) | 0..4 | 5 |
| C2.34 | (3,4) | 0..3 | 4 |
| C2.35 | (3,5) | 0..2 | 3 |
| C2.36 | (3,6) | 0..1 | 2 |
| C2.37 | (3,7) | 0 | 1 |
| C2.44 | (4,4) | 0..2 | 3 |
| C2.45 | (4,5) | 0..1 | 2 |
| C2.46 | (4,6) | 0 | 1 |
| C2.55 | (5,5) | 0 | 1 |
| C3.333 | (3,3,3) | 0..2 | 3 |
| C3.334 | (3,3,4) | 0..1 | 2 |
| C3.335 | (3,3,5) | 0 | 1 |
| C3.344 | (3,4,4) | 0 | 1 |
| C4.3333 | (3,3,3,3) | 0 | 1 |

This is 21 sorted size profiles and **58 disjoint cells** after fixing b. Their n value is determined by (2); each cell retains exactly 9-n other physical squares in its completion hypothesis. A canonical cell ID is the profile followed by `.b0`, `.b1`, etc.

**Exhaustiveness proof without a graph search:** for m=1, k_1 ranges from 3 to 9. For m=2, k_1+k_2<=10 yields the nine displayed pairs. For m=3, k_1+k_2+k_3<=11 yields (3,3,3),(3,3,4),(3,3,5),(3,4,4). For m=4, the minimum already uses the full budget and forces four triangles. The stated bridge ranges are then exactly 0<=b<=8-sum(k_i-1). Summing their lengths gives 28+22+7+1=58. QED.

**What this inventory does NOT claim:** a profile such as C1.9 does not specify its nine-vertex block's adjacency, circle-load locations, contact normals or the continuous geometry. Each cell is a quantified whole family. Declaring this list finite does not solve any of those sharp inequalities. There are currently **57 OPEN cells** after the one exact exclusion below; no global completion percentage is inferred.

## 5. A uniform loaded-body contact exclusion

**Theorem CY.LOAD.3.** In the stated radius window, the circle-loaded bodies of a normalized positive component cannot be pairwise physically touching.

*Proof.* Let there be k circle-loaded bodies. Summing the component's center force equations cancels internal contacts and gives

    sum lambda_v v = 0,   sum lambda_v = 1,
    |v|=R for every positive circle atom.           (4)

If the loaded bodies pairwise touch, their centers have pairwise distance at most sqrt(2): at a common point, each center is at most sqrt(2)/2 away. Let o be the arithmetic mean of these k centers. Every loaded center satisfies

    |c_i-o| <= ((k-1)/k)*sqrt(2).

Every circle atom is a corner of one of these squares and is therefore at distance at most sqrt(2)/2 from its center. Consequently

    |v-o| <= (3/2-1/k)*sqrt(2)
           <= 25*sqrt(2)/18,                       (5)

using k<=9. For k=1 the same estimate directly gives radius sqrt(2)/2 around its center.

On the other hand, (4) gives the exact identity

    sum lambda_v |v-o|^2 = R^2+|o|^2.

Combining with (5),

    R^2 <= 625/162 < 6241/1600 = (79/40)^2,

where the strict rational comparison is 1,000,000 < 1,011,042. This contradicts the radius window. QED.

The result concerns pairwise physical contact of the **loaded subset**, not necessarily positive edges between them. A circle load on a single body or a mutually touching cluster cannot sustain the high-radius minimizing certificate, irrespective of the rest of its positive component.

## 6. First complete cyclic cell closed

**Cell C1.3.b0 CLOSED hand.** There is one cyclic block of size three and no bridges; equation (2) gives n=3. A simple biconnected three-vertex graph is a triangle, so its three positive-component bodies pairwise physically touch. Its loaded subset is therefore pairwise touching, contradicting CY.LOAD.3. This excludes the entire selected triangle component at the stated radius, regardless of all six additional physical squares.

This is not an exclusion of C1.3.b1 through C1.3.b6: their loaded bodies may lie on the attached bridge tree and need not form a touching clique. Nor does a proof for a clique block automatically exclude a larger nonclique component containing it.

## 7. Contracts for every remaining cell

For every unchecked cell C(...).b_j, retain:

1. every biconnected graph on its stated block vertex sets, every valid block-cut attachment and every positive load allocation satisfying CY.LOAD.2;
2. true physical contact points and normals, joint force/torque equations and circle containment;
3. all 9-n other physical squares and all zero-stress contacts;
4. all independent orientations, degenerate contacts, and equality cases.

A cell closes only after proving q>=Q for **every** such nine-square realization, or proving no such selected component can occur in the radius window. An infeasible sampled graph or one canonical drawing does not close its size-profile cell.

The current global remainder is P.ALL, Y.ALL and these 57 coarse cyclic cells, plus their explicit lower-window prerequisite, global equality necessity and verification. The finite block table removes an unspecified bookkeeping category, but it is **not** the hoped-for small sharp geometric classification. A universal inequality may close many or all cells at once and is preferable to a huge SAT or orientation-grid search.

## 8. Verification boundary

The block budget, complete integer list, unloaded-appendage force identity and loaded-clique radius contradiction are proved above. A separate exact regression program enumerates the 58 integer cells and checks block decompositions on finite test graphs; that execution is not the proof of all graph decompositions or sharp packing bounds. Independent full audit, Lean, CI and unrestricted optimality remain outstanding.