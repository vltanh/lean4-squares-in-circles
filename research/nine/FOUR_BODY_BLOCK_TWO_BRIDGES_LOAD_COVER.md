# Four-body blocks with two bridges: every necessary load and leaf domain

**Status: complete hand finite cover and whole load/leaf-family exits;
root and separate independent full hand audits passed.**
Use the common selected certificate in

    79/40 <= R <= sqrt(1105)/16,
    r=R-sqrt(2),   d=sqrt(R^2-1/4)-1,
    epsilon=max(d-1,0)<1/60.

The exact positive component has six bodies, one four-body biconnected
block and two bridges. All three other physical packing squares remain
arbitrary and present. Every original positive force, physical contact,
circle mask and actual shared-side mean is retained.

SIX_BODY_CYCLIC_FRONTIER.md proves the complete eleven-layout cover:
four C4 attachments and seven diamond attachments. The positive K4
block is excluded uniformly even when bridges are attached. The diamond
arm-at-tip and two-leaves-at-one-tip layouts are already wholly closed.
This source supplies the full remaining necessary positive-load cover
and the genuine leaf/transmitter alternatives for the other nine.

## 1. Exact graph labels, genuine roots and arm alternatives

The C4 has cyclic order A--B--C--D--A. The diamond has hubs H,K,
page tips B,C, and exact block edges

    HK, HB, HC, KB, KC.

A two-edge arm is R0--U--L at its block root R0. U is the central
neighbor of the genuine leaf L, hence physically circle-clear and a
true unloaded degree-two transmitter. With leaf direction e and
actual reserve w, the application on R0 is x e, where

    x=r-w for a D leaf,   x=d-w for an S leaf,
    w in{1,sqrt(2)}.

The D/diagonal combination is forbidden by the existing off-origin
vertex/vertex bridge selection: both physical applications at the
D leaf would be vertices, and their actual bridge force is radial.
Thus the complete arm-type alternatives are exactly

    S/side,   S/diagonal,   D/side.                  (1)

For every alternative in (1), |x|<31/60<r. Every point of a physical
circle-touching unit has norm at least r, so the actual root R0 is
physically circle-clear. These are the full arm formulas from
TRIANGLE_THREE_BRIDGES_DISTINCT_ARM_EXCLUSION.md, Section1; their
proof uses only this real arm, not any triangle force equation.

A root of a genuine direct leaf is also physically circle-clear and
meets D_epsilon. These full leaf conclusions hold regardless of its
other block forces. No root is assigned a smaller positive degree.

## 2. Three uniform restrictions with their complete scopes

### 2.1. An unloaded channel cannot join two genuine leaf roots

Let X,Y each support a genuine leaf, so each actual unit meets
D_epsilon. Suppose a positive path of one or more true unloaded
degree-two transmitters joins X to Y. Its total reserve w>=1 gives
some unit direction n and support value h with

    X subset{n.x<=h},   Y subset{n.x>=h+w}.

Taking an actual point of X in D_epsilon gives h>=-epsilon;
taking one of Y gives h+w<=epsilon. Hence

    1<=w<=2epsilon<1/30,

which is impossible. Endpoint degrees, leaf types and all actual
transmitter means are unrestricted. This is a local contradiction
for the entire channel domain, not a sampled separation bound.

### 2.2. A two-leaf root has no unloaded degree-two neighbor

TWO_LEAF_ROOT_NO_UNLOADED_TRANSMITTER.md proves this whole theorem
with arbitrary other positive forces at the root and the other channel
endpoint. Away from d=1 its two-leaf central disk contradicts the
sharp unit support bound. At d=1 the actual equality geometry is a
complete physical P or Y cage, which cannot be completed to nine.
The other channel endpoint is identified geometrically as radial S;
it is not given a false degree-one equation.

This theorem excludes nine-square completions at the critical radius,
and all local noncritical configurations. It retains all three extra
squares of the present six-body component.

### 2.3. Two D leaves at distinct roots are impossible

A D leaf has its inner vertex at r e in the relative interior of
its root's support side, with 0<r<1. In that root's own coordinates
its support interval in direction e is[r-1,r], and zero is strictly
inside its transverse side interval. Thus O is in the root's open
interior. Two distinct D-leaf roots would have overlapping interiors
at O. Consequently every full D/D assignment to distinct roots is
excluded throughout the entire radius window.

There is a useful necessary refinement for a mixed S/D assignment
at distinct roots. If d<=1, the S root also contains O, by the inward
unit segment from its actual radial application d e. A small interior
ball at the D root would then meet the S root's interior. Hence every
surviving distinct-root mixed S/D family has

    d>1,   equivalently R^2>17/4.                  (2)

This restriction retains its entire remaining radius range and every
physical frame/mean; it does not close the full mixed family.

## 3. Complete remaining block-load table

The genuine outside leaf or leaves are always positively loaded and
are omitted from the displayed block-load sets. There are at least
three noncollinear loaded bodies in the whole component. Thus an arm
needs at least two block loads, and a two-leaf layout at least one.

The full loaded positive-graph complement is automatically connected:
each genuine leaf's sole positive neighbor is clear, so that leaf has
a complement edge to every other loaded body. A load exclusion for
an isolated four-body component is therefore not transferred here.

| Block | Complete attachment layout | Exact remaining necessary positive block-load sets |
| --- | --- | --- |
| C4 | Arm at A | BC; BD; BCD |
| C4 | Two leaves at A | BCD |
| C4 | Leaves at adjacent roots A,B | C; CD |
| C4 | Leaves at opposite roots A,C | BD |
| Diamond | Arm at hub H | KBC |
| Diamond | Arm at tip B | None; whole layout already closed |
| Diamond | Two leaves at hub H | KBC |
| Diamond | Two leaves at tip B | None; whole layout already closed |
| Diamond | Leaves at both hubs H,K | BC |
| Diamond | Leaves at both tips B,C | HK |
| Diamond | Leaves at hub H and tip B | KC |

The nine open layouts have exactly twelve necessary whole block-load
orbits. Each set includes every automorphism preserving the actual
attachment; each leaf/width refinement below uses the stabilizer of
that specific load set. The table is necessary coverage and asserts
no physical realization.

### 3.1. Every C4 load orbit

For an arm at A, A and U are clear and the single genuine leaf is
loaded. At least two of B,C,D are therefore loaded. The reflection
fixing A exchanges B,D and fixes C. This gives exactly BC,BD,BCD.
If the mask is BC, the remaining true transmitter D has the unit
bypass B, so D has reserve1. The reflected CD case is included.
If the mask is BD, the transmitter C has bypass A and also has
reserve1. These are actual-degree conclusions, not deletions of
an extra root force. No internal transmitter remains in maskBCD.

For two leaves at A, the full two-leaf-root theorem forces both
actual degree-two neighbors B,D loaded. This excludes the entire
one-adjacent-load, one-opposite-load and two-adjacent-load families,
for all S/S,S/D,D/D choices and every physical mask. The initial
necessary load alternatives are BD andBCD.

TWO_LEAF_ROOT_OPPOSITE_C4_EXCLUSION.md now excludes the entire BD
alternative at the common canonical radius/Phi minimizer. Each actual
genuine leaf has positive circle-force pressure at A, in all three
whole S/S,S/D,D/D domains. POSITIVE_ROOT_PRESSURE_OPPOSITE_C4_EXCLUSION.md
then applies to the genuine B-C-D path, with C an unloaded transmitter,
B/D true loaded degree two, and all four positive A forces retained.
All three arbitrary extras remain. Only BCD remains in this layout;
its true middle C equation cannot be deleted to use the opposite-load
theorem. The complete same-root attachment parent is still open.

For adjacent leaf roots A,B, both roots are clear. At least one of
C,D is loaded. The attachment reflection swaps A,B and C,D, leaving
representatives C andCD. In the single-C case, D is the true
unloaded transmitter between A,C, with the physical bypass B;
hence it has reserve1. The leaf at B and its true degree-three
root equation remain. Both loads in CD retain their degree-two
body equations with all physical circle masks.

For opposite leaf roots A,C, any unloaded B or D would be a true
transmitter directly between those two actual leaf roots. Section2.1
excludes it. Therefore both B,D are loaded, giving exactly BD.
The entire single-block-load family is excluded for every genuine
leaf-type assignment, not only the D/D family.

### 3.2. All diamond load orbits and the two prior whole exits

Every unchanged degree-two page tip is loaded, because its two
neighbors H,K physically touch. An unchanged exact-degree-three hub
is loaded by NO_UNLOADED_DIAMOND_HUB.md: its other hub neighbor
physically touches both page-tip neighbors.

With an arm or two leaves at H, the actual H is clear. K retains
true positive degree three and is loaded; B,C retain degree two
and are loaded. Thus KBC is the sole block-load set in either
layout. H has genuine degree four or five respectively.

With an arm or two leaves only at tip B, both unchanged hubs H,K
and the other tip C are forced loaded. They form the positive
triangle H--K--C--H, impossible for three boundary units. These
are the two entire layouts already closed by
ROOTED_BLOCK_ATTACHMENT_OBSTRUCTIONS.md.

With one leaf at each hub, H,K are physically clear and B,C remain
loaded triangle tips. The sole load set is BC. Both hubs keep their
true degree-four equations.

With one leaf at each tip, B,C are physically clear and both hubs
retain exact degree three with the two-edge neighbor pattern. The
sole load set is HK. Both tip roots keep their true degree-three
equations, including their original leaf forces.

With leaves at hub H and tip B, those roots are clear. K retains
exact degree three and is forced loaded, as is the unchanged
degree-two tip C. Thus KC is the sole block-load set. H has degree
four, B degree three; they cannot be exchanged as attachment roots.
These arguments exhaust every row of the eleven-layout catalogue.

## 4. Exact leaf-type orbits, including the asymmetric adjacent mask

For an arm, (1) is the full three-way leaf/transmitter-width cover.
For two leaves at one root, exchanging the two actual leaves gives
exactly S/S,S/D,D/D, with their entire relative placement domain.

At distinct roots, every D/D assignment is excluded by Section2.3.
A mixed remaining assignment retains all of d>1 by (2). It must not
be identified with its reversal unless an actual automorphism also
preserves the chosen positive-load representative.

In the C4 adjacent-root single-C family, the only nonidentity
attachment reflection swaps A,B and also C,D. After choosing C as
the loaded representative, that reflection no longer preserves the
load set. The two mixed assignments S at A/D at B and D at A/S at B
are therefore distinct full gates. In the CD family the reflection
does preserve the load set, so the two mixed assignments are one
orbit. This distinction prevents loss of an entire leaf placement.

For C4 opposite roots with maskBD, a reflection exchanges A,C while
preserving that load set. For both diamond hubs or both diamond tips,
the corresponding root swap also preserves its sole load set. In each
of those three layouts the remaining leaf pairs are S/S and S/D up
to that genuine symmetry. For the hub/tip diamond, the root degrees
distinguish H and B, so both mixed orders remain separately.

The full remaining semantic counts are therefore:

| Layout | Whole block-load representatives | Full leaf/width families remaining |
| --- | ---: | ---: |
| C4 arm | 3 | 9: three arm types for each mask |
| C4 same-root leaves | 1 | 3: all three unordered leaf pairs at BCD |
| C4 adjacent-root leaves | 2 | 5: three ordered pairs at C; two at CD |
| C4 opposite-root leaves | 1 | 2: S/S and the full mixed orbit |
| Diamond arm at hub | 1 | 3: all three arm types |
| Diamond same-hub leaves | 1 | 3: all three unordered leaf pairs |
| Diamond both-hub leaves | 1 | 2: S/S and the full mixed orbit |
| Diamond both-tip leaves | 1 | 2: S/S and the full mixed orbit |
| Diamond hub/tip leaves | 1 | 3: S/S and both ordered mixed pairs |
| Total | 12 | 32 |

These are entire genuine leaf/width alternatives, not sampled angles
or arbitrary intervals introduced to inflate progress. Every original
continuous pose and shared mean remains in its appropriate full gate.
The two previously closed diamond-tip layouts contribute no open gate.

## 5. Remaining sharp and completion contracts

All nine displayed attachment parents remain open, with twelve
necessary block-load orbits and thirty-two leaf/width refinements.
The complete new restrictions are the two-leaf-root/no-transmitter
exclusion, the no-channel-between-leaf-roots theorem, and the distinct-
root D/D exclusion; their proper scopes have been applied before
recording the residual families. The complete canonical two-leaf
opposite-load C4 exit removes all three BD leaf-type alternatives.

Each remaining whole family must receive a full core contradiction,
a sharp radius bound or a joint capacity theorem excluding all three
other physical units. Every actual higher-degree root equation remains;
no isolated C4, diamond-plus-leaf or tree theorem is applied after
removing a positive attachment. The P/Y invocations in Section2.2
are physical completion theorems at their exact full critical domains.

The catalogue and these full load/leaf exits do not close C1.4.b2.
No numerical graph enumeration, sampled pose, Lean compilation or CI
is used. The unrestricted sharp theorem, original equality and full
earlier prerequisite-chain audit retain their separate open status.
