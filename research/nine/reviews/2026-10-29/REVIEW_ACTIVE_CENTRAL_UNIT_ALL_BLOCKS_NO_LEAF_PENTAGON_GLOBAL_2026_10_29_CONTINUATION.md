# Full independent review: active central units, branch mass and all cyclic blocks

Date: October 29, 2026 UTC. Reviewer: pentagon/global continuation.

**PASS for all new theorems at their exact stated scopes.** The complete
260-line source and every complete direct input or review have been
read. The center-virial branch proof, full outside-block boundary-path
substitution, central-disk block and bridge conclusion, and low-radius
zero-moment restriction all pass. No mathematical correction is needed.
The last restriction is not an exclusion of its zero-moment residual.

## 1. Exact target and independent-review boundary

| Complete reviewed source | SHA256 | Scope |
| --- | --- | --- |
| ACTIVE_CENTRAL_UNIT_ALL_BLOCKS_AND_BRANCH_MASS_WITHOUT_LEAF_2026_10_29.md | 4a402273a45a7780effc38b622ed88a6dd68ac1c80755a415a1491e7139f390b | Entire 260-line, 13670-byte source, including all three structural conclusions and their accounting limits |

Root authored this source and the new branch-path strengthening. I
supplied none of its center-virial derivation, removal of the leaf
hypothesis, or new arbitrary-active-unit theorem. I independently
reconstructed these arguments from the original equations and the
complete retained geometric inputs.

I did author the separate input
LOW_RADIUS_CLOSED_ORIGIN_MOMENT_CYCLES_AND_DOUBLE_LEAF_FORK_EXCLUSION_2026_10_29_CONTINUATION.md,
SHA256
`867a7a74edc969a462c7b831addaed3d6e4e0e04c359596fcb978e7cad80c1c1`.
This report is therefore not represented as a new independent review
of that input. Its distinct, complete independent root review remains
REVIEW_LOW_RADIUS_CLOSED_ORIGIN_CYCLES_DOUBLE_LEAF_FORK_ROOT_2026_10_29.md,
SHA256
`bef4bf9c79d022bfded764a768475751fdf8abeed1e5ee8b69915d1849ca2dc2`.
I read that entire 311-line review and checked its actual equality,
neighbor-identity and common-embedding conclusions before reviewing
their literal use in the new root-authored theorem.

The older selected physical certificate and common compatible
embedding retain their established original scopes. This audit does
not constitute a new recursive global prerequisite audit or a Lean
formalization. No historical manuscript, review or source pin has
been edited or silently superseded.

## 2. Complete radius-free branch-mass argument

Let A be a vertex of one connected original positive body component
G, and X a nonempty connected component of G-A. Every positive
external neighbor of X is A, and at least one such edge exists by
connectivity. Suppose the total original circle weight in X were
zero. Nonnegativity forces each of its individual circle coefficients
to be zero, including every coefficient of a physical two-vertex mask.

Summing the unchanged original force equations over all X vertices
cancels the internal pairs. The sum of its entire pair force to A
is zero. By the original opposite-normal relation, the entire force
at A contributed by its actual X neighbors is also zero.

Consequently the retained actual edges inside X and between X and A
have zero pair-force sum at each vertex in X union {A}. At an X
vertex this is its full original force equation with its actual
circle resultant zero; at A it is the just-derived complete branch
identity. No original force at A is asserted to vanish separately,
and no smaller-degree theorem is applied to A after deletion.

For each retained physical pair, its common support gives

    (c_j-c_i).n_ij = h_i(n_ij)+h_j(n_ij) >= 1.

Here the h_i are half-widths of the actual unit squares, each at
least 1/2. The equality is valid for every normal owner and for an
entire actual shared-face mean; only the support value is used.
Dotting the derived zero pair-force equation at each vertex with
its own actual center and summing over X union {A} therefore gives

    0 = -sum_(retained unordered pairs ij)
             mu_ij*(h_i(n_ij)+h_j(n_ij)) < 0.

Strictness follows from one retained edge and its actual mu_ij>0;
no force normalization or radius estimate is needed. This proves
strictly positive original circle mass in every deletion branch.
Some actual body B in X has a positive circle coefficient and
therefore has physical circle contact. Physical contacts with zero
coefficients are neither removed nor needed to supply this B.

The existing articulation manuscript already states deletion-branch
positive mass. The target gives its full center-virial justification
and the new uses below. Its proof does not require a radial bridge,
a genuine leaf, or an unloaded private vertex in X.

## 3. Exact graph identity behind the boundary-path substitution

Let Q be a maximal cyclic biconnected block. A connected component
X of G-V(Q) attaches to at least one Q vertex by connectivity.
If it attached to two distinct Q vertices, its connecting outside
path would be an ear joining vertices of Q and enlarge the same
biconnected block. Thus there is exactly one attaching vertex A.

In particular, X is an actual connected component of G-A, not
merely a selected branch of a larger component: its only external
positive neighbors are A. The radius-free lemma applies at that
literal graph scope. It yields a loaded boundary body B in X.
For every actual E in X, connectivity gives a positive E-to-B
path lying wholly in X and avoiding every Q vertex.

Nothing here requires E to carry a load or to have a prescribed
positive degree. There is no need to choose a leaf as the path's
last body. B can have arbitrary actual degree, because its original
positive circle coefficient supplies the same protected exterior
access in the common selected embedding.

This is precisely the hypothesis needed in the later topological
contradiction. It does not assign such a path to a physically present
completion square outside the connected positive component G.

## 4. Whole-window central-disk separation and nonzero edge moments

The stated window retains the original nine actual squares and

    79/40 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,
    epsilon=max(d-1,0)<1/60.

Suppose the closed disk D_epsilon lies in int(E), where E is an
actual vertex of G. Every other actual closed square avoids that
disk. Indeed, a point of another closed square in int(E) can be
approximated by that square's interior points still in int(E),
contradicting disjoint open interiors. The relevant compact sets
therefore have positive clearance, including epsilon=0.

Consider an original positive contact between two non-E units with
zero origin moment. Its actual application cannot be O. Reverse
the edge orientation if necessary to write it as p=t*n, t>0,
with the inner unit maximizing n and the outer unit minimizing n.
The complete contained-unit support bound gives t<=d.

The origin-free inner square has an own coordinate interval missing
zero; reflect that coordinate to [a,a+1] with a>0. Since p=t*n
has positive own coordinate, n has positive component there. The
actual maximizing contact coordinate is therefore a+1. It follows
that t>1 and a<=t-1<=epsilon. This reasoning applies to an actual
side mean as well as an individual contact vertex.

If the other own interval also missed zero, its absolute maximizing
coordinate would exceed one as well. Then t>sqrt(2)>d, impossible
in the retained window. Otherwise the second interval contains zero,
and the inner square contains its actual point (a,0) in D_epsilon.
That contradicts the preceding physical clearance.

Every original positive edge whose endpoints both differ from E
thus has nonzero origin moment. No selected normal, application or
mean was changed to obtain the radial contradiction.

## 5. Every cyclic block contains the central unit

Suppose a maximal cyclic Q omitted E. All of its actual bodies
avoid D_epsilon, and every Q edge has nonzero original moment.
For each whole component outside Q, sum all unchanged origin torque
equations. Internal pair moments cancel at the same actual mean,
and all radial circle atoms have zero origin moment. Its complete
moment at its sole Q attachment is therefore zero.

Subtracting these complete zero outside contributions from each
original Q torque equation leaves exactly the original Q-edge
moment circulation. This works with arbitrary degrees, chords,
loads, further branches and other blocks. It does not apply a
private degree-two equation at a Q vertex.

Orient each edge in its positive-moment direction, with the
positive magnitude as its circulation weight. Following outgoing
edges in a finite nonempty circulation gives a directed simple
cycle C. The actual graph is simple and a single direction was
assigned to each undirected edge, so C has at least three vertices.

The complete far-disk port and cycle theorem applies literally:
every cycle unit and both actual cycle neighbors avoid D_epsilon.
Only Sections 1--3 of that source are used. Its later intact-tip
premise is not imported. The original center/contact walk has
positive winding about O, and the common compatible physical
embedding supplies a Jordan cycle with the same winding.

Let X be the outside-Q component containing E. Section 3 supplies
the real positive path in X from E to a loaded B. The compact
segment O--c_E lies in int(E), hence misses all original C bodies.
Choose the one common routing within that positive clearance and
the cycle's origin clearance, preserving every exterior spoke.
The winding is the same at O and c_E, so c_E lies inside C.
The disjoint original graph path in X cannot cross the embedded
cycle, and hence c_B also lies inside. This contradicts B's
protected physical boundary access to the unbounded face.

Every cyclic block of G therefore contains E. This is a full
arbitrary-block statement within E's positive component, rather
than a theorem restricted to a designated terminal triangle or
an intact root with a specified leaf.

## 6. Exact bridge consequence

For any original positive bridge, summing the complete torque
equations on either cut side cancels all interior pair and circle
moments and gives zero moment for that actual bridge. Section 4
then requires the bridge to be incident with E.

Write it E--U. A second bridge at U would avoid E and contradict
the same conclusion. Any other incident edge at U lies in a cyclic
block through U. By the proved block theorem that block contains
E and gives a path from U to E not using the bridge, contradicting
that E--U is a bridge. Thus U has actual positive degree one.

Every bridge is a direct genuine leaf edge at E. Distinct cyclic
blocks can meet only at their common actual vertex E, by the
standard maximal-block intersection property. Every other block
is one of the just-classified leaf edges. No force classification
inside a surviving cyclic block follows from this structural result.

## 7. Low-radius origin-boundary restriction: complete application

Now assume R<=sqrt(17)/2 and O belongs to the actual closed E,
without assuming O or D_epsilon lies in int(E). Let a maximal
cyclic Q omit E. The same full outside-component torque sums
produce the original Q moment circulation.

If one Q edge had nonzero moment, the nonzero part of that
circulation would contain a directed simple positive-moment cycle
C. Other zero-moment edges stay in the original graph; omitting
them from this auxiliary circulation does not delete their forces.

No actual C unit contains O openly, since it would then overlap
the distinct closed E by the same interior-approximation argument.
The separately reviewed complete low-radius theorem therefore
applies to the actual cycle, including an origin vertex or relative
side-interior origin at any of its bodies. Its distinct-neighbor
equality analysis is retained, not replaced by a strictly-origin-free
port claim.

The actual center/port strands avoid O and have positive winding.
Except possibly for its endpoint O, the segment O--c_E is in
int(E) and cannot meet a strand in another actual square. At O
the strands themselves are disjoint from the segment. Thus the
two compact sets have positive distance even when O is on the
boundary of E. The one common routing can preserve this segment's
clearance, the origin clearance and every protected exterior spoke.

It follows that c_E lies inside the resulting Jordan cycle. The
full branch-mass argument again gives a real E-to-B path outside
Q, with actual B loaded. That entire path cannot cross C, placing
B inside and contradicting its protected exterior access.

Consequently every original Q edge has zero origin moment. This
conclusion uses the complete force system only to obtain branch
mass and the complete torque system only to isolate the original
circulation; it makes no degree or load assertion at E or at a
Q vertex touching O.

## 8. Exact zero-moment residual and preserved scope

An edge with two origin-free actual endpoints cannot have zero
moment at low radius. Its actual p is nonzero; orient p=t*n with
t>0. The outer-unit support cap is t<=1. The positive own
interval [a,a+1] of the origin-free inner square makes its actual
maximizing coordinate a+1>1, so t>1. The contradiction includes
shared means and all interval endpoints.

Thus the Q vertices whose squares contain O form a vertex cover
of all original positive Q edges. This does not exclude an actual
all-zero-moment block whose edges all meet those vertices. That
residual remains explicitly open in the source and receives no
whole-domain closure credit from this review.

The strong conclusion that all blocks contain E and all bridges
are its direct leaves requires the stated central-disk interior
hypothesis. The weaker closed-origin low-radius hypothesis gives
the moment and vertex-cover restriction only. Keeping these two
conclusions separate is essential.

All nine actual units, full physical masks, individual zero circle
coefficients, actual positive degrees, all original pair forces and
shared means remain. No original fine or coarse flag is changed
by this review. The sharp global theorem, equality classification
and global prerequisite audit retain their prior open status.

## 9. Complete direct manuscripts and exact identities

| Complete source or review read | SHA256 | Exact audited use |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Entire 399-line source; full original force and torque, positive pair coefficients, support separation, all physical masks and means |
| GLOBAL_CLOSURE_ARTICULATION_STRESS_SPLITTING.md | 39aa9e31a6de4ecdff535a8136f5c3330e6bb653903951fde812ee522d128d4a | Entire 255-line source; existing branch-mass statement, now justified directly by the target's complete virial proof |
| GLOBAL_NEXT_DEGREE_FREE_MOMENT_PORT_ORDER_AND_INTACT_BLOCK_EXCLUSION.md | 8def789e0cde632795f81d8ecf92d6dd3642b37fd4ca6e79cc4890594264fd49 | Entire 366-line source; complete Sections 1--3 support and far-disk directed-cycle theorem, without the later intact-tip premise |
| LOW_RADIUS_CLOSED_ORIGIN_MOMENT_CYCLES_AND_DOUBLE_LEAF_FORK_EXCLUSION_2026_10_29_CONTINUATION.md | 867a7a74edc969a462c7b831addaed3d6e4e0e04c359596fcb978e7cad80c1c1 | Entire 521-line source authored and read by this reviewer; complete Sections 1--3 used, with separate independent review retained |
| REVIEW_LOW_RADIUS_CLOSED_ORIGIN_CYCLES_DOUBLE_LEAF_FORK_ROOT_2026_10_29.md | bef4bf9c79d022bfded764a768475751fdf8abeed1e5ee8b69915d1849ca2dc2 | Entire 311-line independent root review read; full boundary-origin equality, actual-neighbor and common-embedding validation |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Entire 326-line source; one compatible selected physical embedding, arbitrarily close actual center/contact routing, protected exterior access |

The frozen target and all six displayed direct source/review hashes
were checked against their actual complete bytes. This was a complete
hand-proof review. No numerical pose search, angular mesh, packing
certificate, physical deletion, force or mean replacement, normal
change, Lean/Lake compilation, build, CI/workflow dispatch, metadata
edit, commit, merge or remote write was used.
