# n=9 TREE.02.P: all point-only two-vertex cores have total capacity at most eight

**Status:** complete hand proof of an entire contact-type case, covering its full continuous angle range and all unstressed completions. Independent audit and Lean verification pending.

**Parent:** TREE.02 in TREE_RADIUS_QUANTIZATION.md. Its hypotheses select the physical minimizing certificate constructed in PHYSICAL_CONTACT_STRESS.md, including a strictly exposing common normal at a point-only vertex/vertex contact. The tree-radius theorem gives q0=17/4, two unloaded vertex-origin bodies and side-normal loaded S terminals.

The finite split here is **point-only versus shared-edge contact of the two central squares**, not a subdivision into many numerical tilt intervals. The point-only branch is completely excluded at nine squares. The shared-edge branch is identified exactly with an endpoint configuration of the remaining staggered-path completion problem; it is not marked closed.

## 1. The central cones and their two gaps

Let U and V be the two unloaded unit squares with vertex 0. Their right-angle tangent cones have disjoint interiors. The two complementary angular gaps have lengths g,h>=0 with

    g+h=pi.

Their intersection is only {0} exactly when g,h>0. If one gap is zero, they share a full unit side [0,e]. These two possibilities exhaust all relative orientations of U,V.

By TREE.F2 all loaded bodies are S(e), centered at (3/2)e with inward contact at e. A positive contact with U can only use its two outgoing side-ray endpoints: those are its only outward radial support points of norm one. The same holds for V.

## 2. Point-only central contact forces four DISTINCT radial terminals

Assume g,h>0. The four central cone boundary rays are then distinct. A loaded S square cannot be shared between U and V, because its positive contact point e would have to be a common boundary-ray endpoint of both. Hence all loaded vertices are leaves. Connectedness of the positive component forces a positive U--V edge at 0.

In the physical certificate's point-only construction, the chosen normal exposes the origin **uniquely in both squares**. Consequently its negative on either square lies strictly inside the cone spanned by that square's two outgoing side rays. Force equilibrium of the unloaded body therefore requires strictly positive loads in **both** side directions. A single side-ray load could not balance a strictly interior normal.

Thus all four distinct endpoint terminal squares S(e) are physically present. The selected component has the two central bodies and these four loaded leaves. Every additional physical square, including all unstressed and other-component bodies, must avoid those six squares.

**Certificate caveat:** an arbitrary force balance using a non-strict separator at a point-only central contact is not this selected certificate. For example, the four-body boundary path with opposite endpoint sliders can carry a non-strict horizontal zero-point force. It remains a valid regression witness for general physical equilibrium, but does not invalidate the strict-normal implication above. Every unrestricted minimizer admits the selected certificate by the complete local construction in PHYSICAL_CONTACT_STRESS.md, Section 2.2.

## 3. Every additional square is trapped in one of the two screened gaps

Apply the single-vertex quadrant lemma in THREE_VERTEX_ORIGIN_CAPACITY.md, Section 2, separately to U and V. An additional center cannot lie in either open central quadrant. On a central boundary ray it could only be the point (3/2)e, but the corresponding loaded S terminal already occupies that center. Center separation excludes another body there.

Therefore every additional center lies strictly inside one of the gaps g or h. Each gap boundary ray is physically screened from 0 to 1 by a central side and from 1 to 2 by its terminal. The radial outer-face screen of RADIAL_SECTOR_POCKET_CAPACITY.md, Lemma P1.1 and Corollary P1.2, shows that the **entire additional square**, not merely its center, stays inside that gap wedge. It cannot pass around the radius-two terminal endpoint inside D_(17/4).

## 4. Two pocket bounds cover the COMPLETE point-contact angle range

Exchange g,h so 0<g<=pi/2<=h<pi. The two terminal directions bounding g are distinct. Lemma P5.1 in RADIAL_SECTOR_POCKET_CAPACITY.md gives

    g >= beta := 2 arctan(1/2).

Consequently

    h=pi-g <= pi-beta = 2 arctan(2).

There are now exactly two analytic possibilities:

- **g<pi/2.** The acute screened pocket contains no additional square, by Theorem P3.1. The other pocket, with pi/2<h<=2 arctan(2), contains at most two, by Theorem P4.1.
- **g=pi/2.** Both pockets are right angles. Each contains at most the unique origin-vertex unit square filling it, by Theorem P3.1. Again there are at most two additional squares.

The fixed six-square component therefore has at most two other physical unit squares in the disk. The total is at most eight. This proves:

> **TREE.02.P CLOSED hand:** every q0=17/4 nine-square completion whose chosen TREE.02 component has a point-only central contact is impossible, for every compatible angle, every positive load and every orientation/separator of the remaining squares.

The endpoint g=pi/2 is included explicitly; it is not lost in a strict-angle argument.

## 5. The only remaining TREE.02 boundary is an exact aligned half-block path

Suppose g=0 or h=0. The two vertex-origin squares share a unit side and form a solid 2x1 half-block adjoining the origin along the middle of one long side. Choose coordinates so they are

    [-1,0] x [0,1],   [0,1] x [0,1].

Their possible loaded directions are (-1,0),(0,1),(1,0). Summing all component forces cancels the internal forces. Every loaded S square in direction e contributes a positive multiple of e to the total circle force. The upward direction cannot occur with positive weight, since no downward loaded direction is available. Therefore exactly the two opposing horizontal terminals occur, with equal resultant weights.

The component is the aligned four-square path with centers

    (-3/2,0), (-1/2,1/2), (1/2,1/2), (3/2,0),

or its reflection. This is the precise shared-edge endpoint of the broader two-slider path geometry, not a new unbounded angle class.

- **TREE.02.E remains OPEN:** bound all five additional physical squares for this exact half-block endpoint configuration.
- A zero-stress upper cardinal square may be among those extra bodies; global force balance only excludes it as a *positive loaded terminal*, not as a physical square.
- The flat solid-row theorem does not apply to these shifted inner squares.

## 6. Updated finite gate impact

The completed tree rows are TREE.12, TREE.03 and TREE.04. TREE.02 is now partitioned into exactly two contact types: **TREE.02.P closed**, **TREE.02.E open and explicitly identified**. TREE.20 and TREE.11 remain open. The cyclic branch remains separate and open.

The general proof is analytic and completion-aware. Exact finite regression examples can check its identities and boundary controls but do not replace the all-angle argument. No unrestricted optimality, independent full audit, Lean compilation or CI is claimed.