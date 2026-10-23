# n=9 CY.ACUTE: loaded physical contacts are acute, and the loaded noncontact graph is connected

**Status:** new hand necessary-condition theorem for every normalized physical minimizing-stress component; independent mathematical audit and Lean verification pending. This is a global restriction on the entire loaded subset, not a classification of sample graphs. It does not alone establish the sharp n=9 radius.

**Read base:** `14b6a28c5f92224baa0e438746816800844a560e`, PR #11. Inputs: the exact square/circle model and the physical force balance in PHYSICAL_CONTACT_STRESS.md. No planarity, common square frame, coordinate separability or radiality of nonbridge edges is assumed.

## 1. A circle-loaded square lies in a strict 45-degree cone

**Theorem A.1.** Let a unit square S lie in a circle centered at zero of squared radius q, and let z be one of its corners on that circle. If

    q > 2 + sqrt(3),

then for EVERY p in S,

    z dot p > |det(z,p)|.                                  (1)

In particular p!=0, and its direction makes angle strictly less than pi/4 with z.

*Proof.* Choose orthonormal inward side coordinates u,v so

    S = z - [0,1]u - [0,1]v.

Write a=z.u and b=z.v. The contained adjacent corners z-u and z-v give a,b>=1/2, while a^2+b^2=q. The two linear inequalities z.p>+det(z,p) and z.p>-det(z,p) need only be checked on the four vertices.

At p=z they are immediate. At z-u and z-v they follow from

    q > a+b,

because a+b<=sqrt(2q)<q for q>2.

At the opposite corner z-u-v they are equivalent to

    q-a-b > |a-b|,  equivalently q>2 max(a,b).

Since a,b>=1/2,

    max(a,b) <= sqrt(q-1/4).

The desired strict comparison follows from

    q^2-4q+1>0,

which holds for q>2+sqrt(3). Both sides q and 2sqrt(q-1/4) are positive, so squaring is legitimate. All four vertices satisfy both strict linear inequalities. Their convex combinations do too. QED.

The explicit research window 79/40<=R<=sqrt(Q), Q=1105/256, satisfies the premise: (79/40)^2>15/4>2+sqrt(3), using (7/4)^2>3. This theorem does not require the upper endpoint Q.

## 2. Physical contact forces acute circle directions

**Theorem A.2.** If two circle-loaded unit squares S,T physically touch and each lies in D_q with q>2+sqrt(3), then

    z dot w > 0                                             (2)

for EVERY circle-contact corner z of S and every circle-contact corner w of T.

*Proof.* Take any p in S intersect T. By A.1, p!=0. In coordinates whose positive first axis is p/|p|, write z=(a,b) and w=(c,d). Inequality (1), applied to each square, gives a>|b| and c>|d|. Therefore

    z.w = ac+bd >= ac-|b||d| > 0.

This argument uses an actual common point, including a single corner contact. It does not require the pair to carry positive stress. QED.

For a loaded body i define its unnormalized circle-load vector

    m_i = sum_k lambda_ik z_ik,

where lambda_ik>=0 are its positive circle-corner weights and their total on i is positive. The vector m_i is nonzero: in the direction of any point of S_i the projections of all its circle corners are positive by A.1. From A.2:

> If loaded bodies i and j physically touch, then m_i.m_j>0.

The conclusion follows by expanding the weighted double sum; each contributing coefficient is nonnegative and at least one product is positive.

## 3. The loaded NONCONTACT graph must be connected

Consider one connected positive stress component, retaining and renormalizing it as allowed by the existing physical stress theorem. Summing all center force equations cancels internal contact forces, so

    sum_{i loaded} m_i = 0.                                 (3)

Define N on the loaded bodies by joining i to j exactly when their CLOSED physical squares are DISJOINT (not touching). This is the complement, on the loaded subset, of the physical touching graph. It is not merely the complement of the positive-edge graph: zero-stress physical contacts count as touching.

**Theorem A.3 (connected loaded noncontact graph).** Under the hypotheses above, N is connected.

*Proof.* If N were disconnected, partition its vertices into nonempty A,B with no N edge crossing the partition. Every cross pair of loaded squares would therefore physically touch. By A.2,

    (sum_{i in A} m_i) dot (sum_{j in B} m_j)
        = sum_{i in A,j in B} m_i.m_j > 0.

But (3) says the two sums are opposites, making their dot product the nonpositive number -|sum_A m_i|^2. Contradiction. QED.

This also rules out a single loaded body directly through (3) and m_i!=0; the prior component theorem already supplies at least two.

## 4. Exact graph-level consequences

The following exclusions apply to a WHOLE positive component and every completion by the other physical squares; no sampled orientation or proposed adjacency drawing is involved.

1. **Two loaded bodies cannot touch.** Their two-vertex noncontact graph must have its one edge.
2. **No loaded body touches every other loaded body.** It would be an isolated vertex of N.
3. **No complete touching join across a nontrivial partition of the loaded bodies.** This is the direct vector-sum contradiction above.
4. **If all four bodies of a positive four-cycle are loaded, it is impossible.** Partition the four cycle vertices into opposite pairs. Every cross pair is a cycle edge and hence a physical contact, violating item 3.
5. **If exactly three bodies of a positive four-cycle are loaded, it is impossible.** Their induced cycle path has a middle loaded body touching both other loaded bodies, violating item 2.
6. **Every positive four-vertex diamond component (K4 minus one edge) has only one load pattern not already excluded by this theorem:** exactly its two nonadjacent degree-two vertices are loaded. All larger loaded subsets have a contact-universal loaded vertex, and every other two-body loaded subset touches. This remaining diamond pattern is NOT excluded here.

A physical contact absent from the positive graph can only strengthen these exclusions. Conversely, failure of the graph condition is a valid obstruction, while satisfaction of it is merely necessary, not sufficient for a physical packing or a stress.

## 5. Scope relative to the existing cyclic inventory

This strengthens CY.LOAD.3 in CYCLIC_BLOCK_INVENTORY.md: a loaded clique was already excluded, whereas A.3 excludes EVERY disconnected loaded noncontact graph. It is a uniform necessary theorem for all 58 coarse cells, not a claim that all those cells are closed.

The complete four-cycle exclusion will additionally need the two-loaded opposite-vertex case, addressed by the transmission-channel argument in a companion manuscript. The four-vertex diamond with its nonadjacent loaded tips must remain an explicit residual case unless independently excluded.

No quantitative proof-completion percentage, universal n=9 lower bound, full independent audit, Lean compilation or CI run is claimed.