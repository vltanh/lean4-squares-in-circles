# Joint closure: SS and SD boundary blocks over the complete radius window

Date: October 25, 2026.
Pinned repository head: `4c8584155ba0b4f5a59375d7140e3a38f95eecfa`.
PR: vltanh/lean4-squares-in-circles #11.

This is a **draft-proof supplement** to the existing deep roadmap and
JOINT_CLOSURE_ROADMAP_2026_10_25.md. It adds no gate IDs. It does not replace
or silently retick the authoritative accepted checklist.

## 1. New uniform result

TWO_LEAF_CONNECTED_BOUNDARY_BLOCK_EXCLUSION.md proves:

If a positive component has two genuine radial leaves at H, at least one
S, and all its other circle loads lie in one connected physical graph of
circle-touching neighbors of H, then the component is impossible throughout
79/40 <= R <= sqrt(1105)/16.

The theorem permits arbitrary genuine degrees at H and the boundary graph,
zero-stress physical connectivity, unequal radial weights elsewhere, all
original shared-contact means and every additional physical square.

A single geometric support bound holds on the entire opposite cone of the
two leaf directions:

    h_H(w) < 14/25 < R - sqrt(2).

Hence no boundary neighbor can have a circle corner in that cone: projecting
its corner-to-contact segment would make its length greater than sqrt(2).
The existing S-leaf sign-propagation theorem, used only at the actual S
leaf, and the true component force sum then give opposite signs for the
same determinant. No force equation at an individual block body is needed.

The proof has four complete SS radial-support types and three complete SD
types, not angle bins. The only coupled SD estimate is

    d^2 - r^2 > 1/2,

proved on the whole window by monotonicity, with lower-endpoint reserve
1/680. There is no Bernstein table or external solver certificate.

## 2. Whole existing gate coverage and larger-family applications

| Existing gate / scope | Draft result in this continuation | Accepted status |
| --- | --- | --- |
| M6.B4L2.DIAMOND.SAME_HUB.LKBC.SS | Entire original gate, full radius interval, every mask/owner/mean and three extras | Independent review outstanding; original checkbox unchanged |
| M6.B4L2.DIAMOND.SAME_HUB.LKBC.SD | Entire original mixed-leaf gate, including either ordering under the true same-hub symmetry | Independent review outstanding; original checkbox unchanged |
| M6.B4L2.DIAMOND.SAME_HUB.LKBC.DD | Not covered by the new theorem | Low-radius DD remains; the prior high-radius draft retains its own scope |
| Same-root path fan on seven bodies, two leaves, inside C1.5.b2 | Complete SS and SD graph/leaf families, with two arbitrary extras | Draft scope only; surrounding coarse parent open |
| Same-root path fan on eight bodies, two leaves, inside C1.6.b2 | Complete SS and SD graph/leaf families, with one arbitrary extra | Draft scope only; surrounding coarse parent open |
| Fully loaded C4 with two same-root SS or SD leaves and actual root/middle physical contact | Entire physical-chord feature, including zero HK stress, full radius interval | Physical noncontact residue remains |

The fan has H joined to all k vertices of a positive path and to the two
leaves. Its two path endpoints have genuine degree two; its inner path
vertices degree three. The existing unloaded-hub theorem forces those
inner bodies loaded without deleting any root force. H keeps degree k+2.
The same proof applies for every k with k+3<=9.

At k=3 this is the diamond; at k=4,5 it gives the seven-/eight-body rows
above. The k=2 triangle case was already closed, and k=6 also violates the
existing boundary count. Neither is counted as new progress.

Thus one theorem covers six complete named graph/leaf families (SS/SD at
sizes six, seven and eight), plus the stated C4 contact features. This is
not six newly introduced gates and is not six whole coarse-cell closures.

## 3. Combined draft frontier

Combining this result with the previously saved high-radius assembly leaves
only **DD with R^2<17/4** in the same-hub/two-leaf diamond layout. That is a
remaining whole geometric domain, not a sequence of newly created cells.

For fully loaded C4 with two SS or SD leaves, the actual root must be
physically disjoint from the middle loaded square in any surviving draft
case. No theorem asserting that this contact must occur has been proved.

The new theorem does not exclude a triangle petal by replacing it with two
independent leaves, a D/D leaf pair, disconnected loaded groups, or a circle
load not physically neighboring H. The triangle-attached upper-left
ABC/diamond work, both remaining alternating C6 families, the other mixed
cells, unrestricted bound and original equality therefore remain open.

The next joint target is an actual-force or complete-packing argument for
the DD residue and/or disconnected outside groups. A local low-radius tip
sign must not be assumed, and a higher-degree hub must not be replaced by
an isolated smaller-component equation.

## 4. Verification record

Author mathematical checks: complete for the saved manuscript. The review
covers the four SS and three SD radial-support rows, d=1, the coupled radius
comparison, closed cone endpoints, both circle masks, zero weights, original
shared means, the single-S sign-propagation scope, and all genuine degrees
in the fan and diamond applications.

Direct prerequisites inspected at the pinned head:

- TRIANGLE_THREE_BRIDGES_DOUBLE_LEAF_ROOT_EXCLUSION.md, Sections 1.1--1.2;
- S_LEAF_CONNECTED_BOUNDARY_NEIGHBORS.md, Sections 1--2;
- S_LEAF_TRIANGLE_EXCLUSION.md, Sections 1--3 (geometric inaccessible arc);
- NO_UNLOADED_DIAMOND_HUB.md, theorem statement and scope;
- FOUR_BODY_BLOCK_TWO_BRIDGES_LOAD_COVER.md, original load/leaf catalogue.

TWO_LEAF_CONNECTED_BOUNDARY_CHECK.py passed 24 exact rational strict reserves
and nine exact identities, using only standard-library Fraction arithmetic.
The checker certifies these arithmetic comparisons, not geometry or an
independent manuscript review. Every comparison is also explicit in the
hand proof.

Independent saved-source/dependency review: NOT performed. No independent
agent or reviewer is claimed. The earlier full prerequisite-chain audit
remains a separate open obligation.

No Lean compilation or CI was run.

## 5. October 27 publication note and accepted counts

This October 25 manuscript is preserved as an **unreviewed draft supplement**
to PR #11. It was prepared against pinned prerequisite commit
`4c8584155ba0b4f5a59375d7140e3a38f95eecfa`, before the October 27
reviewed checkpoint `50c0cd616eb494ade100f055ad518cdbd33c7275`.

At that reviewed checkpoint, the authoritative original inventory has
**19/58 coarse cells closed, 39 open** and **2,271/2,513 fine IDs checked,
242 unchecked**. Nothing in this draft reticks those accepted inventories;
the new SS/SD proof applications are candidate closures requiring a fresh
independent full-source and dependency review against the current branch.
The DD and disconnected-loaded-group alternatives are not covered.

The standard-library checker verifies 24 strict rational comparisons and
nine identities only, not the geometric proof. The unrestricted nine-square
sharp inequality, equality classification, full prerequisite audit, and Lean
kernel verification remain open. No Lean compilation or CI was performed
for this draft.
