# Independent review of the full unloaded-module two- and three-port rules

Date: October 30, 2026.

Reviewer: branch-budget proof agent, not the author of the reviewed
manuscript or its rational-stress prerequisite.

Input repository tree: `4d2b3d62ce489b3251f0241d6c592e868fd7a410`.

**Verdict: the complete stated two-port and physical-singleton three-port
theorems are correct under the explicitly stated common-certificate
prerequisites.** This review covers arbitrary entirely unloaded body
subsets, all determinant degeneracies, matched normal parameters, the
common-actual-point work contradiction, and the displayed graph-family
callers. It does not close an original fine or coarse proof cell.

## 1. Final source pins and scope of the review

The complete reviewed source is
`GENERIC_TWO_AND_THREE_PORT_CUT_RULES_FOR_ARBITRARY_UNLOADED_BODY_MODULES_2026_10_30.md`,
SHA-256
`f6b12507086fd284e99b637748ef3b40c994c56aba44264a2c3a408338181251`.

I also read the complete rational full-atom prerequisite
`GENERIC_MINIMAL_PHYSICAL_STRESSES_HAVE_RATIONAL_WEIGHTS_AND_SHARED_MEANS_2026_10_30.md`,
final SHA-256
`fa459e3713c3dc244111528ed65be230dd718a00f388f38f13b6519bb85fa049`,
and checked its interface to the cut theorem. That manuscript also has
a separate independent review by the joint-pockets agent.

The direct physical and common-domain prerequisites read for this review
are:

| Source | SHA-256 |
| --- | --- |
| `PHYSICAL_CONTACT_STRESS.md` | `d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5` |
| `PHYSICAL_BODY_GRAPH_UNCROSSING.md` | `bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe` |
| `GLOBAL_COMMON_NORMAL_DOMAIN_AFTER_FORCE_FREE_C7_AND_ALGEBRAIC_SELECTION_2026_10_29.md` | `557d3f5904a6ba09250a2167c6495cf3555d02536cf016a5ee09c0ccf84cfb20` |

The construction of their common nonempty normal domain is imported as
stated. This review checks every new generic factor in the cut source;
it is not a fresh audit of every older downstream selector.

Two requested source corrections were made before these final pins:
the support class was specified as physically compatible and
noncrossing, and a typographical `+makes` was removed. The first is a
real prerequisite clarification. Abstract graph planarity would not
exclude both physically opposite pairs at a four-square junction.

## 2. Full original equations and the selected support

Summing each member's two original force equations and origin-moment
equation over an entirely unloaded subset cancels every internal atom
with its action/reaction partner. The cancellation uses the same actual
application on the two bodies. Shared contacts may first be aggregated
at their original weighted means; this does not alter the cancellation.
Every positive contact leaving the subset remains in its entire cut.
Thus the resulting balanced wrench equation is valid for arbitrary
internal branches, cycles, connected components and contact means.

Zero total circle coefficient at each member is exactly the needed
hypothesis. A physical circle contact with coefficient zero does not
contribute to these equations and need not be physically absent.
External bodies can have arbitrary loads, degrees and other contacts.

The rational prerequisite's atom matrix retains two force rows and one
origin-moment row per real body, all actual shared endpoints, every
physical circle atom, and normalization. Minimal positive support is
chosen initially in the physically compatible noncrossing class, or in
one already noncrossing atom universe. A support-decreasing dependence
preserves that class because it only deletes old atoms. Consequently
its positive columns are independent. Cramer's rule and evaluation at
algebraically independent legitimate normal parameters give the stated
unique rational weights; all remaining row residuals vanish identically.
Actual aggregate means are derived from those same endpoint weights.
The cut theorem never freezes a variable shared mean in a generic
determinant.

## 3. Common generic choice and two-port degeneracies

At each independent free singleton, parallelism with a fixed normal or
another independent free normal is a proper trigonometric condition.
After rational half-angle substitution it is a proper polynomial
condition over fixed physical geometry. Its zero set cannot fill any
nonempty open admissible parameter domain.

At a four-square junction, the only linked free parameters are the two
opposite pairs with normals `au+bv` and `au-bv`. Their determinant is
`-2ab`, which is nonzero for the legitimate positive parameters. The
compatible matched uncrossing leaves at most one of these pairs
positive. Hence every supported three-singleton cut used in the
determinant theorem has genuinely independent free parameters. It is
legitimate to omit triples containing both opposite pairs from that
prelist, and only those impossible supported triples are omitted on
this ground.

For a two-edge positive cut, force balance forces equal magnitudes and
opposite unit normals. The preceding conditions exclude every pairing
containing a free contact, including the matched pair case. Both
remaining normals are geometrically fixed. The full moment equation
then says that the two original applications lie on one force line.
This proves Theorem 3.1 even for shared contacts, without asserting any
false unit-square width for the whole module.

## 4. Complete three-singleton determinant audit

Place the auxiliary origin at the designated free application `p_0`.
Its wrench vectors span `E_0={(x,y,0)}` as the normal varies over its
open interval. All other singleton applications remain fixed physical
points.

If the other two normals are fixed and parallel, the positive force
equation forces the free normal parallel to them. Generic pair
avoidance excludes this rank-one force case directly. If those normals
are nonparallel, their wrench columns are independent. The full
determinant vanishes identically in the designated free parameter
exactly when their plane is `E_0`, equivalently when both fixed force
lines pass through `p_0`. This concurrency exception is correctly
retained.

If a second normal is free at `p_1 != p_0`, choose it neither radial
from `p_0` nor parallel to the remaining normal. Only finitely many
directions are forbidden in its open interval. Its wrench is outside
`E_0`, and the other two chosen wrenches are independent, so their
plane differs from `E_0`. Varying the designated free normal then makes
the determinant nonzero. This proves nonidentity on the full product,
including all possible special values that the final generic choice
must avoid.

If the two free applications agree, their wrenches independently span
`E_0`; the determinant is identically zero precisely when the third,
fixed force line passes through that same point. With three free
normals the preceding different-point argument applies whenever at
least two applications differ. When all three applications agree,
every wrench lies in the same plane and the determinant is identically
zero. The source correctly leaves that case to geometry.

These alternatives exhaust the possible numbers of free normals in a
three-singleton cut containing a designated free contact. No unknown
multiplier or mean enters any polynomial coefficient. The common
generic choice excludes all and only the proved proper determinant
conditions required by the theorem.

## 5. Common actual point and the resulting cut rule

For a common actual cut application `p`, dot the full force equation of
body `i` with `c_i-p` and sum. Every internal contact contributes
`-mu_e(h_i(n_e)+h_j(n_e))`, and every cut contact contributes
`-mu_e h_i(n_e)`. The support half-widths are strictly positive; the
cut is nonempty; all circle coefficients in the subset are zero.
The sum is therefore strictly negative, contradicting its being zero.
This proof keeps every original internal force and is valid even when
some original cut applications are shared-contact means at `p`.

The argument requires equality of actual applications. Merely
concurrent extended force lines do not satisfy its support-point
premise. The source makes this distinction explicitly.

Combining this work identity with the complete determinant
classification gives exactly Theorem 6.1: all free applications equal
the designated free point; every fixed exit line passes through it;
and at least one fixed exit has an actual application elsewhere.
In particular an all-free three-edge cut of an entirely unloaded
module is impossible. If the three singleton applications are distinct,
at most one exit is free, and the two fixed exits must concur there.
No unjustified single-square classification is imported to remove that
remaining module-level concurrency.

## 6. Graph-family callers, exact limits and verdict

The displayed graph caller uses the entire positive cut of the
unloaded set `V(H)`. Joining a two-connected graph `H` to a cycle by
three edges at distinct endpoints on each side gives a two-connected
graph: deletion of a vertex leaves its constituent connected and at
least two joins intact. The triangle, diamond and `K2,3` size counts
and their displayed bare-block parents are therefore correct. The
`K2,3` module has branching and no simple cycle of length five, so the
argument does not conceal a long-cycle premise.

These are exact conditional graph/load/contact features. They do not
assert physical realizability of every abstract graph, remove other
features of a coarse parent, or discard the remaining completion
squares. In particular the three-port theorem is confined to three
physical singleton intersections. A positive-length shared segment
with an endpoint-valued selected mean is not relabelled as a singleton.
The source correctly leaves its possible full-atom determinants to a
separate argument.

**Final review result:** the final pinned manuscript proves its full
stated uniform cut rules with all physical bodies, original loads,
actual means and force-and-torque equations retained. The prerequisite
support clarification is incorporated. No remaining defect was found.
No original proof checkbox changes follow from this review alone.

This was a hand proof review. No Lean compilation, numerical search,
angle grid, CI run or ledger edit was used.

## 7. Separate application check: no newly closed six-body row

The adjacent-terminal page theorem from
`UNLOADED_NETWORK_TERMINAL_DISTANCE_AND_FULL_BRANCH_CUT_BUDGET_2026_10_30.md`,
SHA-256
`28506dbf70ccc567765d98f9a4021c79dc46acb5c40fa682993886ab1fca4e46`,
excludes a maximal biconnected block having an actual edge `AB` and at
least three components after deleting `A,B`. This is a broad exclusion
of non-Hamiltonian branching blocks; it does not close any of the
currently open original six-body graph/load rows.

Indeed every open outer-hexagon graph contains its spanning `C6`.
Deleting two vertices from a spanning cycle leaves at most two path
components, and its remaining chords can only merge components.
Thus no such graph satisfies the three-page hypothesis for any pair
`A,B`, whether adjacent or otherwise. This includes the original
`D02`, `D03`, `D0203`, `D0204`, `D0235`, `CHORD_PATH` and
`CENTRAL_TRIANGLE` rows, independently of their load allocation.

The original interior-pentagon load rows and their five graph joins
are already checked in the pinned roadmap. In the two-spoke case, the
only possible three-page chord would connect the two hub neighbors;
that contact is already forbidden by the actual unloaded hub's
degree-two transmission rule. Higher spoke counts connect the hub
to a surviving rim vertex after removing any two rim vertices, so
they do not add a third component to the two remaining rim paths.
No new original fine-cell identifier or closure is asserted.

This check used `DEEP_GATED_ROADMAP.md` at SHA-256
`a4114c2914d61458571e21be2fcbe0904d3100defb324ee87aa3b58659469a69`.
It concerns actual original graph domains, not an invented new gate.

## 8. Separate review: exact obstruction to virtual contact rerouting

I independently checked the complete local construction in
`EXACT_OCCUPIED_SIDE_POCKET_OBSTRUCTION_TO_VIRTUAL_CONTACT_REROUTING_2026_10_30.md`,
SHA-256
`aefac8b75f7e8727ca37e343628cb44caceada5a4ddb13372819e7701aa9fdf1`.
This is a valid counterexample to the stated automatic contact-length
shortcut. It supplies no nine-body packing and no proof-cell closure.

The two displayed frames are exactly orthonormal. Substitution of
`h=2927/5880` makes the two stated farthest corner squared radii
equal to `q=29660753/6914880`. The signs of the own-coordinate
midpoints select the stated unique farthest corner in each of `X,Y`.
The other two squares have maximum squared radii `521/400` and `17/4`.
All displayed positive rational differences from `q`, and from the
target squared radius `1105/256`, are correct. I also checked all
sixteen fixed corner radii directly with exact rational arithmetic.
Convexity of the disk then contains each complete square.

All six pairwise nonoverlap comparisons are valid support
comparisons. In particular `X` and `E` have the strict horizontal gap
`1/20`; the actual side axis `u_Y` gives the exact strict `E,Y`
separation `14977/296940`. The `U,E` intersection is confined to
`y=1`. The actual `X,U` and `U,Y` applications lie at the stated
height `0<h<1` and give the unchanged horizontal support chart.

The crosscut is a simple graph in the horizontal coordinate, running
through its successive points `z_X,P_X,P_Y,z_Y`. Its endpoints both
lie on the upper circle semicircle, so the chosen upper circle arc
is also a graph between their horizontal coordinates. Both strands
and the middle segment lie in the disk by convexity. On the
horizontal range of `E`, the crosscut height is either `h` or at
most `53077/99960<1`; the `X` strand lies strictly to its left.
Every point of `E` is above that crosscut and below the upper circle
arc. This proves that the complete `E` occupies the specified closed
upper pocket, including its support contact with `U`, without any
unstated winding or placement convention.

Finally the displayed centers give exactly
`|c_E-c_X|^2=3286621/1382976`, exceeding `2` by
`520669/1382976`. Thus occupying that side pocket does not imply the
contact-center bound needed to replace `X-U-Y` by `X-E-Y` in a
contact-length polygon. The negative conclusion is limited precisely
to that proposed automatic inference. Additional hypotheses of a
complete nine-body selected certificate are not claimed or tested.

All arithmetic checks here used only the fixed rational construction;
there was no numerical pose search or sampled angle argument.
