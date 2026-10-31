# Review of the connected-boundary two-leaf argument

Date: October 27, 2026. Reviewed repository snapshot:
`252b400e2fd10e8f7a02505c3a73080ae602d462`.

## Result and scope

Independent full-source review of
TWO_LEAF_CONNECTED_BOUNDARY_BLOCK_EXCLUSION.md: **PASS** as the stated
SS/SD necessary-condition theorem, with the common compatible selected
certificate and the unchanged radius window. This review does not assert
Lean verification or completion of the older prerequisite audit.

The theorem has a connected physical graph of boundary neighbors of H
containing every other positive circle load, two genuine radial leaves
at H, and at least one actual S leaf. The proof retains arbitrary root
degree, every original mean and corner-weight endpoint, and every
completion square. Disconnected boundary groups, a load not touching H,
and a formal aggregate substituted for a genuine leaf are outside its
scope.

## Full checks

The reviewer read the entire saved proof and the entire direct geometric
sources S_LEAF_CONNECTED_BOUNDARY_NEIGHBORS.md,
TRIANGLE_THREE_BRIDGES_DOUBLE_LEAF_ROOT_EXCLUSION.md,
RADIAL_BRIDGE_AND_LEAF_REDUCTION.md, S_LEAF_TRIANGLE_EXCLUSION.md,
CENTERED_INNER_ARC.md, ACUTE_LOADED_CONTACT_GRAPH.md,
CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md and CIRCLE_CONTACT_ANGULAR_ORDER.md.
The full NO_UNLOADED_DIAMOND_HUB.md, UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md
and PHYSICAL_BODY_GRAPH_UNCROSSING.md were read for the fan applications
and their simultaneous selected-certificate scope.

1. The two-leaf radial-support classification is complete. In SS the
   side/side, side/vertex, adjacent-vertex and opposite-vertex rows retain
   the full d=1 boundaries. In SD the D side axis fixes the full root
   rectangle; the S application is exactly its top side or one of its top
   vertices after reflection. No post-extraction normal choice is used.

2. Every support estimate is strict on the original closed radius window.
   In particular the adjacent SS vertex row uses a>3/4, not an unjustified
   stronger numerical approximation. The SD right-vertex estimate uses
   the coupled function d(R)^2-r(R)^2; its derivative is positive from
   R^2>1/2 and its exact lower reserve is 1/680. The top-left SD cone
   includes its southeast sector through the inequality
   h_H(w)<137/252<14/25. These estimates do not treat d and r as independent.

3. The opposite-cone corner exclusion uses a genuine contact point in
   both actual units and their exact diameter sqrt(2). It applies to
   every physical circle corner, including one with zero multiplier,
   and requires no force equation at the boundary neighbor.

4. The sign-propagation input is valid before the separate force-balance
   argument of its source. Its two angular intervals are separated at
   both ends, every body's two physical circle corners have one common
   interval assignment, and an actual physical contact cannot bridge
   the intervals: the acute-corner minor arc would contain an S-leaf
   circle corner, contradicting the angular-neighbor order theorem.
   Thus this input applies to zero-stress physical edges and zero-load
   physical boundary vertices of the connected graph K.

5. Only the true whole-component force sum is used in the final
   contradiction. With directions e1,e2 in counterclockwise order,
   M=-lambda1 e1-lambda2 e2 has negative e1 determinant and positive e2
   determinant. Propagation puts every atom of M below e1; exclusion
   of the entire closed opposite sector then makes every such atom
   have strictly negative e2 determinant. The two conclusions
   contradict each other. Neither root is assigned a false degree.

6. For the path-fan applications, the endpoints have true degree two;
   each internal path body has true degree three and the two-neighbor
   physical-edge pattern required by NO_UNLOADED_DIAMOND_HUB.md.
   That selected-certificate theorem explicitly allows arbitrary
   additional neighbors at the other bodies. Its finite exclusions
   preserve the full shared-side and matched-junction conventions.
   All path bodies are therefore genuinely loaded and meet the
   connected-neighbor premise. The physically chorded C4 application
   uses a physical HK contact only and introduces no positive HK force.

The standard-library arithmetic checker was also run successfully:
24 strict exact rational reserves and nine exact identities.
That calculation supplements the mathematical review above; it is not
being used as a certificate of geometry.

## Existing gate reconciliation: no new original ID closes

The supplement was drafted against the older October 25 head. In the
reviewed October 27 snapshot its two named diamond IDs were already
checked, along with the DD sibling and the full same-hub parent:

- M6.B4L2.DIAMOND.SAME_HUB.LKBC.SS;
- M6.B4L2.DIAMOND.SAME_HUB.LKBC.SD;
- M6.B4L2.DIAMOND.SAME_HUB.LKBC.DD;
- M6.B4L2.DIAMOND.SAME_HUB.

The full source DIAMOND_ROOT_PRESSURE_AND_MIXED_BOUQUET_CLOSURE.md
explicitly supplies the arbitrary-root nonnegative block-pressure join
over both radius ranges and its complete same-hub SS/SD/DD application.
The corresponding original checklist is therefore consistent with that
source. The latest connected-neighbor proof is an alternative proof of
SS/SD, not two new original fine closures. Its remaining-DD description
is historical and must not override the accepted current source.

Likewise ORIGIN_ROOT_C4_PRESSURE_AND_BOUQUET_CLOSURE.md explicitly
supplies the origin-root join for the complete same-root C4 BCD family,
and joins the earlier canonical BD proof. The current fine checklist
checks the whole SAME parent. Older frontier prose saying that its
nonparallel BCD branch remains open is superseded.

D_LEAF_BOUNDARY_FAN_DIRECT_LEAVES_EXCLUSION.md also already proves the
whole path-fan family with any number of direct leaves and at least one
D leaf, after the declared same-nine R>2 reduction. The present SD fan
argument supplies an independent route without that lower-radius
dependency; it does not newly close the existing DD/SD fan profiles.

No shared roadmap, accepted count or coarse cell is changed by this
review. The genuinely unchecked C1.4.b2 layouts remain C4 arm,
adjacent-root leaves, opposite-root leaves, diamond arm at a hub,
two-hub leaves and hub/tip leaves. Their original true degrees and
completion requirements are the next proof obligations.

