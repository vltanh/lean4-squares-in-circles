# Root review of the new uniform geometric implications

Date: October 27, 2026 (America/Chicago).
Read base: committed PR #11 checkpoint `53d326511bd6280f18a14555922351ec15942b3d`.

**Decision: accept the five complete implications below at their stated
scope. None by itself closes an additional coarse cell or a currently open
house/pentagon fine family.** The new sources were read in full, and the
arguments described here were reconstructed from their actual equations
and geometry. Existing global certificate-selection and lower-window
prerequisite audits are not silently enlarged by this review.

## 1. Frozen sources

| Source | SHA-256 |
| --- | --- |
| CENTRAL_DISK_LEAF_ROOT_AND_DOUBLE_LEAF_TRIANGLE_BLOCK_EXCLUSION.md | dd03214ab5e0100bd35211993591baabd5fd0578191cc2ad2d4c1e344b8a5411 |
| C2_35_TWO_BRIDGES_AND_C2_36_ONE_BRIDGE_ORIGINAL_ATTACHMENT_REDUCTION.md | 28810d74517a6f6a4a4e5b2972c5359bdf41559957bd7e33bcb5fb4b358685d5 |
| GENERAL_BALANCED_THREE_BOUNDARY_FULL_WINDOW_METRIC_EXCLUSION.md | 5da69931a63ac7cbf93ec3ff494489dc05d2245017da1c4dcddf1b4a8a6c956e |
| D_LEAF_COMMON_TRIANGLE_NEIGHBOR_AVOIDS_QUARTER_DISK.md | 2330462d457e8f6eaedae3f8d6c8d535379742a213e033c438827f86b4d31288 |
| INNER_PENTAGON_FOUR_SPOKE_NO_CHORD_OCCUPIED_POCKETS_AND_LONG_PORT_REDUCTION.md | ad0a8e658d303d7527a383c4688fa4bfdae1a04f46cecfb59c424cc4028e02a6 |

`ROOT_NEW_UNIFORM_EXACT_RECORD_2026_10_27.json` records the exact displayed
rational comparisons independently recomputed here. These are checks of
the written whole-domain proofs, not samples of square configurations.
Separate independent reviews of the first two sources, the balanced-three
source, the D-root source, and the four-spoke caller accompany publication.

## 2. A genuine leaf supplies the needed exterior access

I read the complete support and port-order argument in Sections 1--3 of
the existing `GLOBAL_NEXT_DEGREE_FREE_MOMENT_PORT_ORDER_AND_INTACT_BLOCK_EXCLUSION.md`.
Its operative premises are avoidance of the closed epsilon disk by all
actual cycle units and opposite signs at the two actual moment ports.
They do not require an intact triangle or a degree bound. Its equality
case really does force both applications to the same nearest point; a
cycle whose every angular change vanishes would put three disjoint square
tangent sectors in a half-plane. The strict winding conclusion follows.

The first new source correctly supplies those premises. For a radial
contact outside the disk, write the application `p=t e`. An origin-free
inner square has a missing own interval `[a,a+1]`, `a>0`. Its coordinate
at this radial maximum must be `a+1`, since `p=t e` fixes the sign of that
component. Thus `t>1` and `a<=t-1<=epsilon`. A second missing interval
would give `t>sqrt(2)>d`; otherwise `(a,0)` is an actual point in the
epsilon disk. Both alternatives contradict the assumed disk avoidance.
This proof includes every original radial side mean.

For each maximal block, the sum of the full torque equations outside
that block cancels all internal pair moments and all circle moments.
Each outside component attaches at at most one block vertex, so its
total extra moment there is zero. The remaining original nonzero block
moments therefore form a positive circulation. No outside force is
deleted from a body equation. A directed simple cycle follows and has
the required positive winding.

The actual genuine leaf provides exactly the missing boundary-access
path: its nonzero single pair force forces positive circle load. The
segment from the origin to its root center stays away from the enclosing
cycle, and the original leaf edge is disjoint from that cycle in the
same compatible embedding. This contradicts the leaf's protected
exterior access. The extension from an open-origin root to a closed-origin
root in the second source is valid because the compact segment still
avoids the closed cycle units, including its origin endpoint.

The bridge consequence also retains full forces. A bridge has zero
origin moment by the complete cut sum, so it must meet the central root.
An additional edge at its other endpoint would either be another
forbidden nonroot bridge or a cyclic block producing an alternative path
to the root. Hence each bridge is genuinely a direct leaf.

## 3. The critical double-leaf and attachment arguments

The privately double-leaf triangle argument correctly treats the true
four-force root. Away from the critical corner it invokes the complete
geometric central-disk conclusion of the two actual leaves. The unrelated
five-block does not contain that root and is excluded by the new winding
theorem, without inventing a leaf at its own root.

At `d=1`, the surviving corner root is the actual `[0,1]^2` with two
real adjacent radial S squares. The center bound excludes another
boundary body on either occupied outer face; the inner-side lemma
excludes a boundary body at either occupied leaf-side point. The actual
B contact is therefore on one of the remaining relative sides. The
complete root force and torque imply that the other triangle normal is
the perpendicular negative axis. Its actual B contact then has
nonpositive scalar product with the first B point, contradicting the
physical boundary point-cone theorem. No original hub mean is prescribed.

I checked the entire block-cut enumeration for C2.35.b2. With two bridges,
disjoint blocks have a connecting path of length one or two, and shared
blocks have either one length-two arm or two direct leaves. The stated
exits leave exactly the four listed structural families, with every
marked five-block and every original load mask still quantified over.
For `d<=1`, disk avoidance reduces to closed-origin avoidance, so the
new block theorem applies precisely where claimed. In the private/common
critical family the two West means have strict opposite signs. The full
radial support classification of the aligned H square gives either the
actual P cage or a top/bottom leaf whose B contact violates the acute
point cone. Both sliders and all additional H forces remain.

For C2.36.b1, the critical H chart is only necessary. Its top/bottom
endpoints are excluded by the same point-cone argument, but `0<k<1`
remains. The source does not turn H into a transmitter. The genuine C6
leaf join is explicitly restricted to a simple C6, while chorded blocks
remain open. The high-radius distinction between avoidance of O and
avoidance of the epsilon disk is correctly preserved throughout.

## 4. Full-window balanced-three metric theorem

The new metric proof is self-contained on the original radius interval.
The farthest-corner bound gives center norm below `91/60`, and any
physical boundary center has norm above `19/15`. The actual-corner
formula is correct: writing `t=a+b`, its tangent deviation has maximum
`1/(2 sqrt(R^2-1/4))`. The lower endpoint `R=79/40` gives the strict
`pi/12` correction, including the radial two-corner masks.

The proof first establishes pairwise center separation above `pi/6`
using the three exact corners of a separately convex radial expression.
The resultant directions therefore inherit the centers' circular order.
The zero force sum makes each resultant gap strictly below pi, so each
directed center gap is below `7pi/6`; no minor-gap assumption is made
at this stage.

The three putative distance bounds give minor gaps below `2v,2u,2u`,
where `sin(v)=297/532` and `sin(u)=507/532`. The positive squared reserve
`1742127084` proves `2u+v<pi` on the correct monotone sine interval.
Since `v>pi/6`, each minor gap is below `5pi/6`. A major directed gap
would consequently exceed `7pi/6`, already forbidden. The three actual
directed gaps are therefore minor and their sum is strictly below
`2v+4u<2pi`, a contradiction.

The literal H3.L013 caller retains both genuine unloaded2 channels and
the actual H bypass. Their full unit reserves give the two long distance
bounds, the real boundary contact gives the short one, and the complete
six-body force sum gives exactly three circle resultants. This removes
the radius-two prerequisite from that already accepted caller without
recounting its fine ID.

## 5. Arbitrary-degree D-root common-neighbor theorem

The support-span lemma is valid at both strict vertices and all side
means. For a minimum `(-c,t)` support, a downward inward edge must point
southwest and has vertical component at most c; two such inward
orthogonal edges cannot both point southwest. A minimizing side has
vertical tangent length c and an upward normal. Reflection gives the
companion upper span.

Under a hypothetical quarter-disk point in K, the complete shallow D
chart and boundary-neighbor theorem fix K's strict Northwest normal.
The physical triangle cover excludes North and Northeast without a
force equation at any neighboring body. Every other actual root force
is West or Southwest. The original West means are all strictly below
`-1/4`, by the boundary point norm and `r^2-s^2>1/16`.

The full arbitrary-degree root force and torque equations are retained:
the y equation gives `gamma t = sum beta_i v_i`, and torque gives
`b sum beta_i u_i <= gamma a c`. A weighted average therefore selects
an actual Southwest page with `u/v <= a c/(b t)`. No coefficient or
contact is modified. The hypothesized quarter-disk point gives
`s c+a t<=1/4`; the complete cubic estimate then proves `c+u<1`.
The exact lower cubic value is `63/64`, and its derivative upper bound
is `-69/16` over the full interval. The physical upper/lower spans
make that actual page and K strictly vertically separated, contradicting
their real contact.

This accepts the original source with its stated same-nine R>2 entry
prerequisite. A later full-window shallow-kernel supplement must have its
own complete proof and review; it is not silently substituted here.
The theorem forces one actual neighbor off the quarter disk. It does
not yet control the arbitrary completion squares and earns no whole
house/fan fine closure.

## 6. Four-spoke occupied pockets and compulsory long ports

I read the entire occupied-hub localization and its full weak-junction
argument. The contact-chord contraction stays in the occupied rim and
preserves winding at all nonrim open square interiors. Arbitrarily
close compatible Jordan resolutions show the limiting pentagon has
winding only zero or one; there is no cancellation of signed lobes.
The long-chord subtraction bounds its free winding-one area strictly
below two. The actual hub already occupies area one, excluding every
inner extra before any exterior capacity is considered.

The simultaneous physical spokes then put whole extras in actual
exterior pockets. For H4_D0.L124 these are `1--0--4` and `4--3--2`;
for H4_D0.L0124 only `2--3--4` remains. Physical boundary refinements
are treated separately from zero multipliers. The reflection
`i -> 3-i mod 5` preserves the graph, the first load mask and every
true degree.

The new balanced-three theorem gives a boundary-center distance above
`1+sqrt(2)` in the three-load case; the accepted four-boundary-path
theorem gives it directly in the four-load case. The triangle inequality
then makes every actual pair of endpoint contact points at rim body 3
more than one unit apart. Its real third force to H remains positive,
so this does not create a two-force channel. The source correctly leaves
the joint exterior capacity and both original H4_D0 fine gates open.

## 7. Publication disposition

These are complete reusable implications and exhaustive necessary-domain
reductions. Publication must retain all operative recovered prerequisites
and their exact existing acceptances, especially the intact-root and
genuine-cycle inputs used in the second source. No original checkbox is
changed by these five sources. The unrestricted sharp inequality,
original equality classification and complete inherited prerequisite
audit remain open. No Lean compilation, CI or merge was performed.
