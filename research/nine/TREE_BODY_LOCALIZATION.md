# n=9 TREE.F1: localization of EVERY positive tree component

**Status:** new hand necessary-condition theorem; independent audit and Lean verification pending. This is an exhaustive reduction of the positive **tree** branch, not a lower bound for all nine-square packings.

**Read base:** PR #11 head `c27384b8112b553c26c6474a8c5bb3fd3ebd02c4`. Sources are PHYSICAL_CONTACT_STRESS.md, RADIAL_BRIDGE_AND_LEAF_REDUCTION.md and SMALL_TREE_STRESS_CORES.md at that base. Their general physical-stress existence and radial bridge theorems are inputs, not re-proved here.

## 1. Hypotheses and conventions

Put Q=1105/256 and assume

    79/40 <= R <= sqrt(Q).

The lower window is an explicit premise. Its eventual use for all nine-square minimizers needs the declared existing n=8 lower-bound dependency, or a separate proof. It is NOT silently obtained from the arguments below.

Choose the physical force-and-torque certificate whose off-origin point-only vertex/vertex positive contacts are nonbridges, as permitted by RADIAL_BRIDGE_AND_LEAF_REDUCTION.md. Aggregate each positive body pair into its genuine shared force point. Let T be any nontrivial connected component of this positive body-pair graph which is a **tree**.

A body is **loaded** if its total positive circle multiplier is nonzero; otherwise it is **unloaded**. All statements concern vertices of T only. Other physical squares, and all zero-stress contacts, are retained in the nine-square packing but need not be vertices of T.

Set

    delta=max(R-2,0),  A=sqrt(R^2-1/4)-1,  B=R-sqrt(2).

The existing radial bridge theorem supplies:

1. Every edge of T has application point p and a radial force line. At p!=0 we may write p=r e, r>0, with the inner square in e.x<=r and the outer square in e.x>=r.
2. The outer square has p as its unique nearest point to the origin. The inner square meets D_delta. If p=0, both incident squares contain zero.
3. Every square meeting D_delta is geometrically circle-clear, and at most four physical packing squares meet D_delta.
4. The positive component has at least two loaded bodies, and no unloaded leaf.

Elementary comparisons in the radius window give

    9/10 < A < 51/50,     1/2 < B < 7/10,     delta < 1/10.

For the upper A bound, Q-1/4=1041/256 < (101/50)^2. The other bounds are derived in SMALL_TREE_STRESS_CORES.md. These loose rational comparisons are only exact proof constants, not interval enumeration.

## 2. All unloaded tree bodies are central

**Theorem F1.1.** Every unloaded body of T meets D_delta. Thus T has at most **four unloaded bodies**. Every loaded body is geometrically disjoint from D_delta.

*Proof.* A loaded body cannot meet D_delta because such a square is circle-clear. Suppose an unloaded body U does not meet D_delta. At every incident bridge, U is the outer body, since the inner body meets D_delta; p=0 is also impossible. All incident application points must therefore equal U's unique nearest point p_U to zero. Their radial outward unit vector is the same e=p_U/|p_U|. All contact forces on U are negative positive-multiples of e in the stationarity convention, so with no circle load they cannot sum to zero. Contradiction. The four-body bound follows from the prior central-cover theorem. QED.

This is stronger than merely saying the central bodies cover bridges: inside a positive **tree**, every unloaded vertex belongs to that central cover.

## 3. Every loaded body has the exact radial S/D geometry, even when it is not a graph leaf

**Theorem F1.2 (radial loaded terminal).** A loaded vertex L of T has one of exactly two geometric forms, for a unit radial vector e:

| Type | Center | Common incoming force point |
|---|---|---|
| S | (A+1/2)e | A e |
| D | (B+1/sqrt(2))e | B e |

All positive incident forces on L act at that same point and are parallel. A D terminal has degree one. An S terminal has degree at most two; if its degree is two, its two neighbors meet its inward side at their vertices, with aligned right-angle cones filling the opposite half-plane.

*Proof.* Every bridge incident to L has a circle-clear central inner endpoint, so L is always outer. Every application point is L's unique nearest point p_L, and every force direction is parallel to p_L. Combine these collinear forces at p_L. The force and angular equations are exactly those of a loaded leaf with one resultant force. Consequently the proof of Theorem 6.1 in RADIAL_BRIDGE_AND_LEAF_REDUCTION.md applies without a degree-one assumption: it yields S or D with the displayed centers and points.

For a D terminal, p_L is a vertex. The chosen certificate forbids an off-origin vertex/vertex bridge. Hence each neighboring body has p_L in the relative interior of a side, occupying a half-plane tangent cone there. Two such neighboring bodies cannot be disjoint around that same point. Thus degree(L)=1.

For an S terminal, p_L is the midpoint of its inward side and L occupies one full half-plane locally. Each distinct neighbor has a tangent cone of angle at least pi/2 in the opposite half-plane; these cone interiors are disjoint. Hence there are at most two. With two, both cones have angle pi/2 and together fill that half-plane, which forces their axes to be parallel/perpendicular to e. QED.

**Warning:** these loaded nodes are not automatically graph leaves. A degree-two S terminal is possible in the graph syntax and must not be deleted on the strength of the old degree-one statement.

## 4. A radial outward support point of a square avoiding zero is farther than one

**Lemma F1.3.** Let an unloaded body U avoid zero, and let p be an outward radial support point: p=r e with r>0 and e.x<=r for all x in U. Then |p|>1.

*Proof.* In U's own orthonormal coordinates, at least one center coordinate has absolute value >1/2. Reverse that axis so its coordinate is a>1/2. Every point of U has first coordinate >0, including p. Maximizing the functional p.x over U therefore uses its far first-coordinate face, so p_1=a+1/2>1. Thus |p|>1. QED.

## 5. Complete off-origin unloaded-body classification

**Theorem F1.4 (one-step outward transmitter).** If an unloaded body U of T does not contain zero, then necessarily A>1 (equivalently R^2>17/4). In suitable orthonormal coordinates e,Je it has

    c_U=(A-1/2)e + b Je,  |b|<=1/2,
    p_in=(A-1)e,  p_out=A e.

Every incoming neighbor contains zero. There is exactly one outgoing neighbor: the S terminal centered at (A+1/2)e. U is therefore a single side-normal transmitter from one or possibly two origin-containing bodies to one S terminal; there are no longer chains of origin-avoiding unloaded bodies.

*Proof.* By F1.1, U meets D_delta, so its nearest point p_U has radius r<=delta<1/10. Orient every incident edge at nonzero p from its inner to its outer body. If every edge were outgoing from U, let f=p_U/|p_U|. The supporting half-plane of U at its nearest point gives f.x>=r>0 on U. Each outgoing radial direction p/|p| therefore has positive scalar product with f. A positive combination of these directions cannot be zero. Since U is unloaded, it must have an incoming edge.

Every incoming force acts at its unique nearest point p_U. For an outgoing edge, Lemma F1.3 gives |p|>1. Its outer neighbor cannot be unloaded, because by F1.1 every unloaded neighbor has nearest-point radius <=delta. Thus every outgoing neighbor is loaded. By F1.2 its incoming contact radius is A or B. Since B<1, it must be S, with |p|=A>1.

Use U's own axes and a center coordinate a>1/2, as in Lemma F1.3. Every outgoing point has first coordinate x_0=a+1/2>1. If the other center coordinate b had |b|>1/2, every outgoing point would also have |p_2|>1, contradicting A<51/50<sqrt(2). Hence |b|<=1/2. The nearest point is (a-1/2,0), and all incoming forces are parallel to the negative first axis.

An outgoing support point lies on the far side x=x_0 and on the circle |p|=A. If its second coordinate is nonzero, radial support can occur only at a vertex, not in the relative interior of that side. The two possible nonzero heights are +Y and -Y, where Y^2=A^2-x_0^2. Vertical force balance requires both signs if Y>0. They must then be the two endpoints of the side, so Y=1/2, b=0, and A^2=x_0^2+1/4>5/4. This contradicts A<51/50, whose square is <5/4.

Therefore Y=0, x_0=A and a=A-1/2. All outgoing points are (A,0), all outgoing normals the first-axis direction. F1.2 gives the same S square for every outgoing neighbor, so physical disjointness permits only one distinct such neighbor.

Finally an incoming neighbor cannot itself be an origin-avoiding unloaded body: its outgoing point would have radius >1 by F1.3, whereas p_in has radius A-1<1/50. It cannot be a loaded body, all of whose incident contacts have radius A or B. Thus it is an unloaded body containing zero. QED.

**Corollaries.**

1. At R^2<=17/4, **every** unloaded body of a positive tree contains zero.
2. Every nontrivial positive tree component has at least one origin-containing unloaded body: an unloaded body exists because no bridge joins two loaded bodies, and an unloaded body avoiding zero has an incoming origin-containing neighbor by F1.4.
3. If exactly one unloaded body contains zero, the entire component is a subdivided star with arms of length one or two. A loaded terminal shared by two arms would create a cycle. No geometric completion or global sharp-radius claim follows from this corollary alone.

## 6. Gate status

- **TREE.F1 CLOSED hand reduction:** all positive tree bodies are now localized; loaded nodes have S/D geometry even at degree two, and every origin-avoiding unloaded body is a one-step side transmitter.
- **NEXT:** classify the origin-containing bodies by interior/side/vertex incidence and prove the complete radius alternatives. This is a finite geometric split, not an enumeration of small angle windows.
- **OPEN:** any eventual lower bound for a full nine-square realization must still retain every unstressed square. The tree component alone need not contain nine bodies.

No numerical optimization, graph sample, or Lean compilation is a premise of this proof. An independent mathematical audit is still required.