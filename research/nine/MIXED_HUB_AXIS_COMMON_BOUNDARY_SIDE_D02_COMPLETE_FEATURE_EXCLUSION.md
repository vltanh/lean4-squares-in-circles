# Complete D02 exclusion when a hub-owned incoming normal and both normals into W share the common-side interface

Date: October 28, 2026 UTC. Assembly author: root continuation.

**Status: complete proposed original-feature assembly, submitted for independent cover and literal-join review.** This covers every physical V circle mask, all parallel and nonparallel V frames, every original UW/VW side position, and all original means. It joins a new radius-free parallel-frame obstruction to two complete nonparallel theorems. It does not close unequal UW/VW normals or the entire original D02 row.

## 1. Complete original feature

Retain the original nine squares and the common selected physical certificate for M6.B6.HEXAGON.D02.L01345. The rim is 01,12,23,34,45,50, the positive chord is 02, and the positive load set is {0,1,3,4,5}. Put

    U=2,V=1,W=0,T=3,
    loaded boundary path 1,0,5,4,3.

The complete positive degrees are U3,V2,W3,5_2,4_2,T2. U is unloaded; all five path units are positively loaded and physically boundary. All three actual extra squares remain.

Let n be the unchanged U-to-V normal, m the unchanged U-to-W normal, and r the unchanged V-to-W normal.

**Theorem.** The original feature

    n is an own side axis of U,
    m=r

is impossible throughout the declared radius window.

There is no initial owner or frame condition on m, no physical V-mask choice, no T-mask or owner premise, and no restriction on any original shared mean. The equality m=r is an equality of the original directed normals into W. No normal is selected to make it hold.

## 2. Radius and complete hub-normal cover

The same-nine analytic theorem excludes every original R<=2. Retain all nine units and work in

    2<R<=sqrt(1105/256).

If m is also a U side axis, the complete TRIANGLE_HUB_TWO_OWN_AXES_D02_COMPLETE_FEATURE_EXCLUSION.md applies directly. It excludes every original feature with both UV and UW U-owned, independently of the relation to VW. This includes the same and perpendicular U axes, with opposite axes already excluded geometrically.

It remains to take m not a U axis. Rotate all actual data about O so n is North. Since U,V,W physically touch pairwise, the radius-free UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md gives n.m>=0. The second coordinate of m cannot be zero, because then m would be a U side axis. It is therefore strictly positive. Its first coordinate is likewise nonzero; reflect horizontally, if necessary, so it is positive.

Thus every remaining original m has exactly the normalized form

    m=r=(b,a), a,b>0, a^2+b^2=1.

The UW support is the actual U northeast vertex Q=(L,H), where U=[L-1,L]x[H-1,H]. These symmetries apply to every actual unit and equation together.

## 3. A radius-free support-span contradiction covers every parallel V

Suppose V is parallel to U. Because the unchanged UV normal is North and the actual contact is nonempty, V's bottom side has height H. Its top side has height H+1. This is an actual support fact even before any singleton/shared classification; the original UV mean remains unchanged.

The strict Northeast normal r=m exposes V's top-right vertex M, whose height is H+1. On W, the normals from U and V are both m. Consequently both actual points Q and M lie on the same minimum-m support face of W.

They are distinct because their vertical difference is exactly one. Therefore that support face is a side of W, not a vertex. A unit side perpendicular to m=(b,a) has direction (-a,b), up to sign, and its complete vertical span is b<1.

It cannot contain both Q and M with vertical difference one. This contradiction excludes the entire parallel-V feature, without any circle-mask, force, degree, shared-mean or containing-radius premise. In particular no endpoint-valued UV mean has been mistaken for a physical singleton.

## 4. The nonparallel frame and exhaustive physical V masks

Now let V be nonparallel to U. Its actual UV intersection is its unique bottom vertex P. Name the inward axes

    e_1=(c,s),e_2=(-s,c), c,s>0, c^2+s^2=1.

The full common-side chart, printed in Section 2 of both nonparallel component sources below, is independent of the physical V mask. It gives

    M=P+e_1,
    D=c+(a/b)*s in (0,1),
    f=(-a,b),
    W=M+[-beta,1-beta]f+[0,1]m,
    s/b<=beta<=1.

Both actual Q and M lie on this genuine W side; its lower corner need not be Q. The full original U3 torque and every original application remain unchanged. No W3 equation is replaced by a tip equation.

A containing-circle point cannot belong to two contained interior-disjoint units. At such a square corner, the short inward radial segment enters the square's open interior, so two units sharing that corner would overlap. Therefore neither of the actual shared points P nor M is a physical V circle corner.

At R>2, a physical boundary unit has exactly one circle corner or exactly two adjacent circle corners. The farthest-own-coordinate formula excludes a four-corner tie, which would require its center at O and radius 1/sqrt(2). This classifies actual physical corners independently of individual positive or zero coefficients.

There are now exactly three possible physical V alternatives:

| Actual physical V circle mask | Full component used |
| --- | --- |
| Unique corner P+e_2, adjacent to P | Complete adjacent-mask pocket theorem in 94f9d485 |
| Two physical corners P+e_2 and P+e_1+e_2 | Complete radial-mask pocket theorem in 94f9d485 |
| Unique corner P+e_1+e_2, opposite P | Complete opposite-mask quarter-disk theorem in af77bc31 |

The other two vertices P,M have already been excluded as physical circle points. A physical two-corner V with one individual zero coefficient stays in the second row, not the unique-mask rows.

## 5. Literal use of both complete nonparallel theorems

For the unique-adjacent and physical-two alternatives, apply MIXED_HUB_AXIS_SAME_BOUNDARY_SIDE_ADJACENT_OR_RADIAL_TIP_POCKET_CAPACITY_ONE.md. Its premises are exactly the normalized original common-side interface, nonparallel V, one of those two masks, and the complete U3/V2/W3/T2 boundary-path component.

That source derives every W-mask and original terminal support before its scalar bounds. Its full continuous geometry gives closing-pocket capacity one with all original side positions, W/T masks, zero corner coefficients and original means retained. The central triangle/pentagon union has combined capacity one, the four direct boundary-pair pockets are empty, and the actual embedding allocates all three extras. At most two extras could fit, a contradiction.

For the unique-opposite alternative, apply MIXED_HUB_AXIS_SAME_BOUNDARY_SIDE_OPPOSITE_CIRCLE_TIP_QUARTER_DISK_EXCLUSION.md. Its local theorem uses the complete U3 and true loaded V2, the unchanged common-side normals, physical-boundary W and the unique-opposite V mask. It allows arbitrary W degree/load and requires no physical-boundary or degree premise at T. The literal original U3,V2,W3,T2 therefore satisfies its broader statement.

Its full W-mask derivation and continuous bounds prove all four actual margins

    1/4<L<3/4, 1/4<H<3/4.

The closed quarter disk is inside open U. Each of all eight other actual units contributes a disjoint actual open radius-5/4 arc longer than 45 degrees, contradicting a full turn. No completion square or force is omitted, and this branch needs no additional pocket allocation.

These two complete sources cover every physical V mask in Section 4. Combined with Section 3, no V-frame alternative remains.

## 6. Whole-feature conclusion and exact limits

Section 2 excludes m being a U axis. In the remaining strict-vertex interface, Section 3 excludes every parallel V. Sections 4--5 exhaust every nonparallel V physical mask. Therefore the entire original feature in Section 1 is impossible.

Every branch refers to the same original selected certificate, unchanged directed normals, true degrees, actual application means, physical circle masks, individual zero coefficients and nine actual squares. No normal is chosen differently between branches.

Within the exact single-U-axis structural cover, this removes the entire sole-UV interface satisfying n_UW=n_VW, including any initially parallel V and every physical mask. The sole-UV cases with unequal normals into W remain separate. The sole-UW and sole-UT interfaces are not claimed closed here.

This manuscript changes no original fine identifier, flag, order or denominator, and no coarse flag. The whole D02 row, global sharp inequality, equality classification and remaining prerequisites remain open.

## 7. Exact operative sources and independent-review requirements

| Source | SHA256 | Exact operative use |
| --- | --- | --- |
| TRIANGLE_HUB_TWO_OWN_AXES_D02_COMPLETE_FEATURE_EXCLUSION.md | ecf3c638f97421f173fd1b05674034991d2014ab951a9c926d876a673b451e7d | Whole original UV/UW both-U-owned feature |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Radius-free actual n.m>=0; strict signs after removing U-owned m |
| MIXED_HUB_AXIS_SAME_BOUNDARY_SIDE_ADJACENT_OR_RADIAL_TIP_POCKET_CAPACITY_ONE.md | 94f9d4850e408c3b076605f8738126d32dd3856899ba3fe330d132b8d029ccb0 | Mask-independent actual chart, then both complete adjacent/radial pocket and original-feature theorems |
| MIXED_HUB_AXIS_SAME_BOUNDARY_SIDE_OPPOSITE_CIRCLE_TIP_QUARTER_DISK_EXCLUSION.md | af77bc31483ab340c2384dcede4e6e1d85534b733d9297a1cdeba9a844b2ecb1 | Entire unique-opposite local quarter-disk theorem and all-eight-unit contradiction |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Original physical supports, complete means and unchanged selected certificate |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Literal original graph/load/degree and all-three-extra join |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 | Same-nine lower-radius exclusion only for the original caller |

The new parallel support-span argument is printed in full above. Both nonparallel component proofs require their own full independent review, and this union requires a separate whole-cover review. A citation is not a substitute for those audits.

No Lean compilation, CI, workflow, pose search, numerical mesh, computational exclusion packet, normal reselection, altered mean, force deletion, false lower-degree body, remote write or ledger mutation was used.

