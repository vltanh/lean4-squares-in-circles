# n=9 CY.TWOLOAD: every two-loaded physical component has parallel contact forces

**Status:** new hand argument for an entire load-cardinality class, including cyclic and branching components. Independent mathematical audit and Lean verification pending. This is NOT unrestricted n=9 optimality or a completion theorem for P.ALL/Y.ALL.

**Read base:** PR #11 `a89802cd834aef3a96d9622bd4829a2c49df17fd`. Inputs are the physical contact-point equilibrium of PHYSICAL_CONTACT_STRESS.md and the normal-channel/endpoint lemmas in PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md. The argument below proves its own planar vector-flow lemma; it does not assume that the positive body-pair graph is planar.

## 1. The theorem and exact hypotheses

Consider one connected positive component of a physical stress on interior-disjoint closed unit squares inside the disk D_q, with q>9/4. Each positive body-pair contact has a common point p and a positive multiple of a genuine outward supporting normal on one body and its negative on the other. The stress has force and torque balance, positive circle atoms at actual circle corners, and **exactly two circle-loaded bodies** A,B. All other bodies in this selected component have zero circle weight.

**Theorem R.1 (two-load parallelism).** Every positive physical pair force is parallel to one common line. The two nonzero resultant circle-load vectors point in opposite directions on that line.

No assumed square alignment, generic-position assumption, body-graph planarity or angle subdivision appears in the premises. The theorem holds before using the stronger research radius window.

For the later cardinality bound only, use the certificate that chooses a **strictly exposing common normal at every point-only vertex/vertex contact**, as in PHYSICAL_CONTACT_STRESS.md Section 2.2. This stricter choice is not needed for R.1 itself.

## 2. An elementary planar force-polygon lemma

Let H be a connected graph embedded on the sphere, with a distinguished vertex o. Give each directed half-edge h a nonzero vector f_h in R^2, with f_reverse=-f_h, and require the sum of outgoing vectors at every vertex to be zero.

Assume that at every vertex other than o, the outgoing vector directions occur in their nondecreasing counterclockwise angular order when the incident half-edges are read in the embedding's counterclockwise cyclic order. Equal directions and collinear polygons are permitted. Assume o has degree two.

**Lemma R.2.** Every edge vector of H is parallel to the same line.

*Proof, including the global gluing step.* Let J be a fixed quarter-turn. For an oriented primal edge h, prescribe a dual displacement from its right face to its left face equal to J f_h. These increments integrate to a vector potential z_F on the faces of H. Indeed, a closed dual curve has total increment equal to J times the sum of primal vertex divergences it encloses, hence zero. General closed walks split into such curves; a bridge gives the same statement by summing the divergence on either side. Thus choosing one face potential and integrating along dual paths is independent of the path. This uses the sphere/plane embedding, not an unproved reciprocal drawing of a nonplanar body graph.

Around each primal vertex v, the successive adjacent-face potentials form a closed polygon P_v with edge vectors J f_h in cyclic order. Different occurrences of the same face are retained in this walk. At v!=o, the direction-order hypothesis makes P_v weakly convex with nonnegative signed area. A direct justification is to fix one edge direction: the signed transverse partial sums first increase and then decrease to zero as the later edge directions pass through a full turn. Hence every vertex lies in the left closed half-plane of every oriented side. If any two edge directions are noncollinear, the resulting convex polygon has strictly positive area. Otherwise its area is zero.

The sum of signed areas of ALL P_v is zero. In the shoelace expression, every dual segment between face potentials occurs once in each direction, at the two endpoints of its primal edge, and cancels. The polygon at o has two opposite edges and area zero. All remaining areas are nonnegative and sum to zero, so each is zero and each vertex's incident forces are collinear. Because the graph is connected and every edge vector is nonzero, the local lines propagate to one common line throughout H. QED.

**Important:** arbitrary equilibrium vectors on an arbitrary rotation system do not satisfy this lemma. The plane embedding and the cyclic direction-order hypothesis are essential and are verified for the square packing below.

## 3. Physical contact junctions give the required direction order

Keep all true contact application points as explicit junction vertices. For each body S and junction p on its boundary, aggregate the positive pair forces applied to S at p into F_(S,p). Each summand is an outward supporting normal of S at p. Their positive sum is nonzero and remains in that normal cone: its scalar product with p-c_S is a positive sum of support halfwidths.

Join the center of S to p inside S. At S the incidence-edge force is F_(S,p); at p it is -F_(S,p). At a junction the incident vectors sum to zero because each original pair force cancels with its partner on the other body. At a body they sum, together with its circle load, to zero by physical equilibrium.

These incidence segments form a plane graph: distinct square interiors are disjoint; segments within one square meet only at its center, after equal application points have been combined; shared boundary points are retained as single junctions. No uncrossing that might destroy torque is performed.

**Body cyclic order.** Outward normals of a convex square are ordered counterclockwise with their boundary application points. At a corner the normal cone fills the intervening right-angle interval; aggregation stays in that interval. Hence the incidence forces around an unloaded body have the direction order required in R.2.

**Junction cyclic order.** The vector -F_(S,p) points into the closed tangent cone of S at p. For a side-interior contact this follows because the force is normal to the side. For a vertex contact it follows from the square's right angle: the inward negative of its outward normal cone is exactly its inward tangent quadrant. The tangent-cone interiors of the bodies meeting at p are disjoint, and their incidence segments lie in their respective cones. Therefore the junction forces -F_(S,p) have the same cyclic direction order as those incidence segments. Ties on a shared boundary ray are allowed.

This verification is specific to the right-angle square geometry. It must not be generalized silently to arbitrary acute-vertex polygons.

## 4. Combine each body's circle atoms into ONE exterior port

A square meeting a circle at q>9/4 has at most two farthest vertices; if two, they are adjacent. This follows from the exact own-frame maximum-corner formula: a nonzero center has either two nonzero own-frame coordinates (one farthest corner) or exactly one zero coordinate (two adjacent farthest corners). A zero center would force q=1/2 and is outside the premise.

For a loaded body S put g_S=2 sum_k lambda_(S,k) z_(S,k), where the positive circle atoms z_(S,k) satisfy |z|^2=q. This vector is nonzero: one corner or two adjacent circle corners cannot have zero in their convex hull at this radius.

We may replace all those circle forces by a single topological exterior edge carrying g_S, without changing force balance or the cyclic-order condition at S.

Here is the required geometric justification. If only one circle corner is loaded, it provides an exterior port directly to the disk boundary. Its radial normal lies strictly in that corner's outward normal cone, since containment of its two adjacent corners gives positive own-frame inward coordinates >=1/2. No other square can share that circle point: two right-angle tangent cones would have to fill the inward tangent half-plane, forcing a positive-length tangent edge outside the strictly convex circle.

If two adjacent corners z_-,z_+ are loaded, their connecting side is a chord of length one at distance T=sqrt(q-1/4) from the center. The circular cap outside that chord has thickness R-T<1. No other unit square has interior in this cap. Otherwise, if it crossed to the inside of the chord, a segment between its interior points would cross the chord strictly between its endpoints and immediately enter S's interior. If it did not cross, the whole square would be in a cap of width <1, contrary to the unit square's projection width >=1. The shared circle endpoints are also unavailable as just proved. In particular there is no physical contact anywhere along this outer side, and the cap supplies an empty route from that side to the disk exterior.

The two circle-force directions are consecutive in the boundary cyclic order. Their positive resultant g_S lies between them in an angular interval of length <pi. Replacing these two consecutive directions by their resultant therefore preserves the nondecreasing cyclic order of the remaining body forces. An exterior port may be drawn through the empty cap; no assertion that g_S is the normal at an interior chord point is needed, because R.2 requires direction order and a topological embedding, not force alignment with the drawn incidence segment.

There are exactly two loaded bodies. Add one exterior vertex o and draw their two exterior-port edges to it through the common disk exterior, without crossing any incidence edge. Give o the opposite vectors -g_A,-g_B. Summed component equilibrium gives g_A+g_B=0, so o is balanced and has degree two. Every other incidence vertex satisfies the cyclic-order hypothesis from Section 3 and the present port argument. Lemma R.2 now makes **all aggregated incidence forces parallel**.

## 5. Recover the direction of EVERY original pair force

It remains to check that aggregation at a multiple junction has not hidden nonparallel pair forces.

Fix a junction p. All nonzero aggregates F_(S,p) are parallel to a line e, with both signs present because their sum is zero. The inward vector -F_(S,p) lies in S's tangent cone. If two bodies have aggregates of the same sign, the corresponding inward ray is in both tangent cones. Their interiors are disjoint, so that ray must be a boundary ray of BOTH cones; it cannot be interior to either. Neither can be a side-interior tangent half-plane, whose inward force normal is strictly interior. Hence both are square-vertex cones. Their aggregate outward forces lie on an extreme ray of each corresponding normal cone. Every positively weighted constituent normal must therefore lie on that same extreme ray.

If exactly two bodies meet p, their aggregate is already the (possibly same-normal combined) one body-pair force. If at least three bodies meet, at least one of the two sign groups has two bodies. The preceding extreme-ray argument makes every pair force incident to that group parallel to e. If the other group also has two bodies the same holds there; if it has one, all its pair forces connect to the already handled group. Thus every original positive pair force is parallel to e. Connectivity propagates the same line over the selected component. This proves R.1. QED.

This step also shows that no hidden transverse self-stress is being discarded at a three- or four-square junction.

## 6. In the research window, EVERY two-loaded component has q=17/4 and two internal layers

Now assume 79/40<=R<=sqrt(Q), Q=1105/256. Let e orient the common force line. Direct every positive body-pair edge from its lower to its upper e-support side. Its center projection increases strictly, because its active gap is H_i(e)+H_j(e)>0. Thus this directed graph is acyclic.

At an unloaded body the total incoming and outgoing force magnitudes are equal and positive. Tracing predecessors and successors must terminate at loaded bodies. The leftmost loaded body B is the unique source and the rightmost A the unique sink: a source has circle-load resultant in the -e direction and a sink in +e. With exactly two loaded bodies, every vertex lies on a directed B-to-A path. In particular, every contact on B is on its inward +e support face, and every contact on A on its inward -e face.

Lemma N.4 of PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md applies to each loaded endpoint's parallel forces and their weighted-average application point. Each endpoint is radial S or D, in opposite directions. Write

    A0=sqrt(R^2-1/4)-1,  B0=R-sqrt(2).

Their inward support-plane distance is one of 2A0, A0+B0, 2B0.

At an unloaded body, aggregate its forces separately on the two opposite e-support faces. Force balance gives equal magnitudes; torque balance makes the weighted-average application points have the same transverse coordinate. If e is a side normal, this body's width is one. Otherwise the two support points are opposite vertices, so their displacement must be parallel to e and its length is sqrt(2): this is a diagonal square. Thus every internal body contributes exactly 1 or sqrt(2) to the support-plane distance along any directed B-to-A path.

Every center has norm <61/40. Therefore a path with three internal bodies is impossible, and a path with two cannot contain a diagonal body, since 2+sqrt(2)>61/20. The only positive path reserves are 1, sqrt(2), 2; a direct B--A contact would give reserve zero.

The exact window inequalities from the channel manuscript are

    9/10<A0<51/50,  11/20<B0<7/10,
    1<2B0<sqrt(2),  sqrt(2)<A0+B0<2,
    sqrt(2)<2A0<51/25.

Comparison with the discrete path reserves leaves only **2A0=2**. Consequently:

> **Theorem R.3.** Every two-loaded positive physical component in the research window has q=17/4. The loaded bodies are S terminals centered at (-3/2,0),(3/2,0). Every other positive body is axis-aligned and lies in one of two layers x=-1/2 or x=1/2. Every directed loaded-to-loaded path has exactly two internal bodies.

Each such body has a positive side contact with one of the endpoint terminals, so its height satisfies |y|<=1. Choosing any directed path gives a four-square layered skeleton, but its intermediate heights lie only in [-1,1] a priori. To apply the existing P.ALL domain one still needs the narrower |y|<=1/2. That narrowing is NOT inferred from parallel forces alone: a physical path's force line can lie at a nonzero transverse height when other parallel paths balance it. Therefore R.3 does NOT by itself reduce every cyclic two-loaded component to the existing P.ALL completion theorem.

The exact torque condition only says that the contact-height weighted average at either loaded endpoint is zero. It does not make every individual channel height zero. The distinction is retained in the next section.

## 7. Cardinality, triangles, and the exact residual two-loaded geometry

With the strictly exposing normal choice at point-only vertex/vertex contacts, each interior layer height actually satisfies |y|<1: equality would make its endpoint contact a point-only aligned vertex/vertex contact, for which a horizontal normal is not strictly exposing. In one layer, physical nonoverlap forces center-height gaps >=1. An open interval (-1,1) contains at most two such heights. Each layer is nonempty, so the component has **4, 5 or 6 bodies**.

- **Four bodies:** one per layer. All endpoint contacts lie on one transmitted horizontal force line; its weighted average is that same line and must have height zero. The two internal heights are consequently in [-1/2,1/2], exactly family P.
- **Five bodies:** one or two bodies in each layer, with admissible heights in (-1,1). The whole family now **REDUCES TO P.ALL** by [FIVE_BODY_TWO_LOAD_REDUCTION.md](FIVE_BODY_TWO_LOAD_REDUCTION.md): either an actual P skeleton is present, or at most three extra squares fit. The latter branch retains inner heights outside the P slider range and proves its capacity directly. P.ALL itself remains open.
- **Six bodies:** two bodies in each layer, with admissible heights in (-1,1). The entire physical completion family is now **CLOSED** by [SIX_BODY_TWO_LOAD_COMPLETION.md](SIX_BODY_TWO_LOAD_COMPLETION.md): at most two additional arbitrary unit squares fit, so these genuine six-body cores cannot occur in a nine-square packing. The proof uses cap piercing and physical obstacles, not a reduction to P.

**Corollary R.4 (no positive triangle with only two loaded bodies).** Such a component has no positive triangle. More directly, parallel true contacts cannot make three nondegenerate projection intervals pairwise touch: three pairwise interior-disjoint positive-length intervals cannot all have intersecting pairs. In the radius window the directed three-edge layer structure also makes the positive graph bipartite.

**Corollary R.5 (new whole load-class reductions).** In the declared window, every positive component with exactly two loaded bodies has q=17/4 and at most six bodies. Thus all two-loaded subfamilies with 7–9 positive bodies are excluded, and every triangle-containing two-loaded positive component is excluded. This says nothing by itself about components with three or more loaded bodies or the added physical squares completing the component to nine.

**Completion update.** The separate whole-family theorem in [SIX_BODY_TWO_LOAD_COMPLETION.md](SIX_BODY_TWO_LOAD_COMPLETION.md) excludes the six-body case from every nine-square packing. [FIVE_BODY_TWO_LOAD_REDUCTION.md](FIVE_BODY_TWO_LOAD_REDUCTION.md) reduces every five-body completion to an actual P skeleton. Thus every nine-square packing in the window with a selected two-loaded component contains family P, and **P.ALL is the only remaining two-load completion obligation**. The physical six-cycle and theta examples remain valid as isolated cores; it is their completion to nine that is excluded.

## 8. Why this closes the four-body diamond residual

The remaining load pattern of the positive four-vertex diamond K4 minus one edge has exactly its two nonadjacent degree-two tips loaded; ACUTE_LOADED_CONTACT_GRAPH.md excludes all other load patterns. The diamond contains positive triangles. R.4 therefore excludes this remaining pattern, without needing a capacity estimate for the five other physical squares.

Together with the already proved complete C4 exclusion and loaded-clique exclusion of K4, this closes the **entire coarse cyclic cell C1.4.b0**. The detailed finite cell argument is recorded in FOUR_BODY_CYCLIC_CELL_CLOSED.md. The two-loaded theorem applies more broadly, but does not justify ticking unrelated larger cells whose >=3-loaded realizations remain open.

## 9. Mathematical context and verification boundary

The face-potential integration in Section 2 is the elementary planar reciprocal-force-diagram construction. For background, see Jeff Erickson's *Maxwell–Cremona Correspondence*, sections on discrete integration and reciprocal diagrams:
https://jeffe.cs.illinois.edu/teaching/comptop/2023/notes/12a-Maxwell-Cremona.html

The square-specific direction order, exterior-port aggregation, recovery of individual forces, radius quantization and four-body-cell consequence are proved here; the background reference is not cited as proving those packing statements. The graph is the physical incidence graph, so no body-graph planarity assumption is smuggled into the argument.

An independent audit should specifically check cyclic orders at common contact points, the empty outer-chord cap, the signed-area cancellation with repeated face occurrences, and recovery of individual pair forces. Finite force-polygon and physical-packing regressions are supplementary only. No Lean compilation, CI, independent full audit, P.ALL/Y.ALL completion or unrestricted n=9 optimality is claimed.
