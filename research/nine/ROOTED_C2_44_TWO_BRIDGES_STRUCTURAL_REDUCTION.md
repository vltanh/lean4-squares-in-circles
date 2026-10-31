# Exact original C2.44.b2 forest reduction with present complete inputs

Date: October 27, 2026.

**Status: complete proposed original-domain structural reduction,
frozen for full root and separate independent review.** The two
distinct-private-root residual families in Section 6 are retained.
This source does not declare the entire original b2 cell closed.

Keep all nine actual unit squares, the common radius/Phi-minimizing
packing and its compatible selected certificate in

    79/40<=R<=sqrt(1105)/16.

Use the same simultaneous strict/nonradial physical normal choices
and the global scalar-atom/body selector. No actual force, circle
weight, application, shared-side mean or square is removed.

The original connected positive component has exactly two four-body
biconnected blocks and exactly two bridges. Its actual body count is

    1+(4-1)+(4-1)+2=9.                                  (1)

The full selected-positive-K4 exclusion removes K4 blocks at arbitrary
true degrees. Every remaining block is C4 or a diamond.

## 1. Exact block-cut and bridge-forest partition

If the two blocks are vertex-disjoint, their unique interblock path
uses either one or two bridges.

- With two bridges it is a length-two connector and there is no
  other pendant edge.
- With one bridge, the remaining bridge is one genuine leaf attached
  to a vertex of one of the two blocks. No internal connector
  vertex exists in this case.

If the blocks share their one articulation H, the cyclic core has
seven vertices. A bridge forest cannot attach to two different core
vertices, because the core already connects them and such an edge
would lie on a cycle. The two actual bridge edges therefore form
exactly one of:

- one two-edge pendant path R-U-L, attached at a core vertex R;
- two genuine direct leaves at core vertices R,S, where R=S is allowed.

The listed cases include every possible original placement. A fork
with an internal branch body needs at least three bridge edges and
is not part of b2.

## 2. Every disjoint-block placement is excluded

For the length-two connector, both four-body blocks are genuine
terminal at their connector roots. The full fresh source

    ROOTED_TWO_GENUINE_FOUR_BLOCKS_ORIGIN_AND_SMALL_FORESTS.md
    28dbc8bbf0db38ea04ec3c8a61bd4b35b1fb39185b78c758c565949fc263fe4e

excludes their vertex-disjoint layout at arbitrary root-force scope.

For a direct connector plus one leaf, if the leaf is at either
connector attachment root, both blocks are still genuine terminal
and the same theorem applies.

If the leaf is at a private vertex X of one block, that block has
exactly one genuine private leaf; the other block is genuine terminal.
The full fresh origin source for its actual type is

    ROOTED_GENUINE_FOUR_BLOCK_LEAF_C4_OPEN_ORIGIN.md
    95e445471efc748b14c299ef21227dfb28c4eaf0009e4fed18315e460096fb87,

or

    ROOTED_GENUINE_FOUR_BLOCK_LEAF_DIAMOND_OPEN_ORIGIN.md
    c11df54a8da029734088e7555ea3777b4158f2a842444959f7b8216a9fd4df7d.

Both complete statements exclude the initially vertex-disjoint
placement. The actual bridge to the other block remains among the
arbitrary root forces until that contradiction. Every C4 leaf orbit,
ordered diamond role and original private circle mask is included.

Thus both original blocks must share H in every retained b2 layout.

## 3. Every two-edge pendant arm is excluded

If the actual arm H-U-L is rooted at H, both cyclic blocks remain
genuine terminal. The complete b=2 forest theorem in 28dbc8bb
excludes that real arm, at its exact full S/D and width scope.

Suppose instead the arm is X-U-L, with X a private vertex of Q1.
The other block Q0 is genuine terminal at H. The complete theorem

    ROOTED_TERMINAL_FOUR_BLOCK_CLOSED_ORIGIN_EXCLUSION.md
    e54c9dc0914c310d01eff64f6ff75a59bea64cbcecae468fd4cfdd01289f85ab

forbids closed O in every actual unit outside Q0. In particular
neither X nor U contains O. No open-origin premise at H is needed.

The genuine leaf L is positively loaded and radial S or D.
The central-endpoint theorem for its real bridge UL makes U
physically circle-clear: the physical boundary L cannot be the
central endpoint. U has exactly its two original pair forces,
so it transmits on the actual radial line.

Write the true outward direction toward L as e, the actual leaf
application as r_L e, and U's projected width as W>=1. Its real
two applications satisfy

    p_UL=r_L e,
    p_XU=(r_L-W)e.                                    (2)

The entire segment between them belongs to U. Since r_L>0 and
U avoids O, necessarily

    0<r_L-W.                                         (3)

A D leaf has r_L=R-sqrt(2)<1 and contradicts W>=1.
For an S leaf, r_L=d=sqrt(R^2-1/4)-1, so (3) gives d>1 and

    0<r_L-W<=d-1<1/60.                               (4)

The same actual point p_XU is an outward radial support of X
in direction e. The inward unit segment of X from that point
contains O by (4). This contradicts the genuine-Q0 closed-origin
theorem.

This is the whole original private-arm exclusion. It uses the
real radial channel rather than replacing X-U-L by a direct
leaf at X. The actual X degree and full circle system of Q1
are unchanged.

## 4. Two direct leaves at the same core vertex

If their common root is H, both blocks are genuine terminal.
The complete two-H-leaf row of 28dbc8bb excludes the configuration.

If their common root X is private to Q1, Q0 remains genuine.
The full geometric two-leaf-root theorem in Section 1 of

    TRIANGLE_THREE_BRIDGES_DOUBLE_LEAF_ROOT_EXCLUSION.md

puts O in the closed X in every original S/S, S/D or D/D
case. For d<1 it is open; for d>1 the whole closed central
disk is strictly interior; for d=1 the possible origin-vertex
endpoint is explicitly retained. The lemma uses no triangle
equation and permits arbitrary other forces at X.

Closed origin in private X contradicts the genuine-Q0 theorem.
Thus the entire repeated-core-root allocation is excluded,
including the critical d=1 geometry.

## 5. Distinct roots with one leaf at H and one private leaf

Let H have a genuine leaf L0, and let a private vertex X of Q1
have its genuine leaf L1. Q0 is still genuine terminal.

The current one-private-leaf origin theorem 95e44547 or c11df54a
has arbitrary extra forces at H. It therefore gives open-origin H
without deleting the real HL0 force. The private X is origin-free,
so its leaf is S with d>1. All original private degrees are the
same as in the complete one-bridge assembly

    ROOTED_C2_44_ONE_BRIDGE_CELL_CLOSED.md
    5f24a9a0c54235760ff38e676b6301adf674755faa9c3fbb888d9d3e5536c1c0.

We use its entire local cover at the following precise scope.

The fresh high-radius four-ring theorem excludes both same-role
diamonds and the opposite-leaf C4 with arbitrary H forces.
The genuine-X3 boundary-continuation theorem excludes the
H-hub/X-tip diamond and both adjacent-C4 U-loaded rows.
The complete X4/K3/Y2 source excludes the other mixed diamond,
again at arbitrary H forces.

For the adjacent-C4 U-unloaded/V-loaded row, every tilted and
aligned inside-concurrence X is excluded at arbitrary H forces.
The complete parallel-X source still applies: the genuine Q0
has at least two physical boundary neighbors and V a third;
the further real L0 is retained. Its fresh unsigned-corner and
59/60-wall replacements are exactly those matched in Section 6.4
of the one-bridge assembly.

The only place where that assembly used the exact absence of
an extra H force is its final aligned exterior-concurrence
pressure sum. Its local branch-pressure proof itself permits
arbitrary H forces. We retain that final case explicitly.

Let M0 be the full genuine Q0 resultant at H, M1 the complete
two-force decorated-C4 branch resultant, and F0=lambda0 e0
the real HL0 leaf force, lambda0>0. The unchanged local proof
gives c_H.M1>0 and c_H nonzero. The current complete genuine
strict-pressure theorems give c_H.M0>0 at every surviving
Q0 graph and private mask.

The real H leaf also has strictly positive center pressure.
For S, its actual support is d e0 and

    c_H.e0=d-halfwidth_H(e0)>=d-1/sqrt(2)>0.

For D, the selected nonradial point convention puts its radial
leaf vertex in the relative interior of an actual H side.
Consequently

    c_H.e0=R-sqrt(2)-1/2>0.

These are the degree-free genuine-leaf calculations in Section 5
of 28dbc8bb. They retain both real S/D types and use no equation
at another H neighbor.

Since H is now physically clear, its complete original equation is

    M0+M1+F0=0,

whose scalar product with c_H contradicts all three strict
positive pressures. Thus the last local case also exits.

This excludes the entire one-H-leaf/one-private-leaf allocation:
both C4 leaf orbits, all four ordered diamond roles and every
original private load mask. The extra H leaf has never been
dropped to call the one-bridge source.

## 6. The exact retained original domains

After Sections 2--5, the two bridges must be two genuine leaves
at DISTINCT PRIVATE vertices of the shared cyclic core. There
are exactly two ways to distribute those roots.

### 6.1. Both private leaf roots belong to the same block

The other Q0 is genuine terminal. For a C4 H-A-B-C-H the two
private-leaf pair orbits, up to its root-preserving reflection,
are

    {A,C}; {A,B}.

For a diamond, preserve the ordered root role. If H is a hub,
the private pair is either both tips or the other hub and one tip.
If H is a tip, the private pair is either both hubs or one hub
and the other tip. These are four complete rooted graph orbits.

The genuine-Q0 theorem already makes every such private leaf
root avoid closed O. Thus each is a real clear S root with d>1
and meets D_epsilon. Any stronger open-origin statement at H
must still be supplied by its complete two-leaf source; the
one-leaf parent theorem is not silently reused.

The separate current source
ROOTED_TWO_PRIVATE_LEAF_C4_OPEN_ORIGIN.md proves open H
for both C4 pair orbits and completely excludes {A,C}.
The {A,B} orbit retains its exact remaining aligned interfaces.
The separate two-leaf diamond work retains all original hub
degrees and is not declared complete merely by this graph list.

### 6.2. One private leaf root belongs to each block

Neither block is genuine terminal at H. Every such original
placement remains in this second domain.

Each rooted leaf-decorated block is one of six graph types:

    C4 with adjacent private leaf;
    C4 with opposite private leaf;
    diamond H-hub/X-hub;
    diamond H-hub/X-tip;
    diamond H-tip/X-hub;
    diamond H-tip/X-tip.

The two blocks may be interchanged. All combinations of these
rooted types and every compatible physical embedding, actual
circle mask, genuine S/D leaf alternative and true root/private
degree remain. No origin premise at H, high-radius restriction,
genuine-Q pressure or genuine-Q shallow-path theorem is assigned
to this domain before separately proved.

In particular the one-private-leaf origin sources do not apply
by calling the other privately decorated block genuine. The
central K3 or decorated K4 forces cannot be shortened.

## 7. What the reduction proves

The original disjoint layouts, every real two-edge arm, every
double-leaf single root, and every H-leaf/private-leaf layout
are excluded by complete present proofs at their exact scopes.
The full remaining original domain is precisely Section 6.

Every force, leaf body and circle mask is retained through its
stated case; all nine actual units are the positive component
in this b2 cell. No completion unit is implicitly available or
deleted. No shared ledger is changed, and no full b2 closure
is inferred from these complete structural reductions.

This source requires its own full independent original-domain
audit and root acceptance, separately from the complete local
reviews of every cited input.

