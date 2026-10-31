# Every single four-edge tree attached to a four-body block is excluded

Date: October 27, 2026.

**Status: complete hand forest-cover join, resubmitted for full root
and separate independent review after correction of the negative-
bridge dependency.** The exact cover and path proof are unchanged;
the stem row also has the separate accepted
TWO_LEAF_ROOT_NO_UNLOADED_TRANSMITTER.md exit. No shared metadata or
coarse count is changed.

Keep all nine original physical unit squares, the same compatible
selected certificate and its minimum-positive-original-scalar-atom
property in

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1<61/60,
    epsilon=max(d-1,0)<1/60.

The positive component has exactly one four-body cyclic block and
one outside bridge tree of four edges attached to it at H. Thus
there are four outside positive bodies and one arbitrary additional
physical square. The tree has only this one block attachment; all
original degrees, circle masks, individual zero weights, force
magnitudes, selected normals and actual means remain.

**Theorem.** Every such original C1.4.b4 attachment is impossible,
for every four-body block profile and root orbit. This is the whole
single-outside-tree forest class, not the entire coarse cell.

## 1. Exhaustive original rooted-tree cover

Every outside body is all-bridge. The exact splitting theorem
GLOBAL_CLOSURE_ARTICULATION_STRESS_SPLITTING.md makes every outside
nonleaf genuinely unloaded in the selected minimum-atom certificate.
Its branch bound k+ell<=3 makes an outside nonleaf's degree at most
three. Orient the original tree away from H: each outside nonleaf
has one parent and either one or two children.

There are precisely three remaining rooted shapes on the four
outside vertices:

| Shape | Original positive outside edges |
| --- | --- |
| Four-edge path | H--U, U--V, V--W, W--L |
| Two-edge stem to a double leaf | H--U, U--V, V--L, V--M |
| Direct leaf and short arm at the first fork | H--U, U--L, U--V, V--M |

To check exhaustiveness, if every outside vertex has at most one
child the tree is the displayed path. Otherwise let the first fork
have depth one or two. A depth-one fork has child subtree sizes
one and two, giving the last row; a depth-two fork must have two
leaf children, giving the middle row. A deeper fork would need
at least five outside vertices. Three children at the first vertex
would give four articulation branches and was excluded above.
These statements concern the actual original rooted tree, not a
tree obtained by deleting positive forces.

Every outside nonleaf meets D_epsilon: if it contains O this is
immediate, and otherwise GLOBAL_CLOSURE_OFF_ORIGIN_BRIDGE_TRANSMITTERS.md
gives its actual side-transmitter point rho e with 0<rho<=d-1.
This same result includes every original endpoint mean.

## 2. The complete four-edge path

Here U,V,W are true unloaded degree-two transmitters. Let e be the
actual direction of the genuine leaf L, with radial root coordinate
r_L in {R-sqrt(2),d}. The original transmitter widths w_V,w_W are
each one or sqrt(2), and propagation of their unchanged force and
moment equations gives the actual U--V application

    p_UV=(r_L-w_V-w_W)e.

Its true outward support on U therefore satisfies

    h_U(e)=r_L-w_V-w_W<=d-2<-epsilon.

But U meets D_epsilon, so h_U(e)>=-epsilon. This contradiction
covers every genuine leaf type and transmitter width. It does not
use a force equation at the original cyclic root H.

## 3. The two-edge stem to two genuine leaves

Now V has the two genuine leaves L,M, and its parent is the true
unloaded degree-two transmitter U. The accepted theorem
TWO_LEAF_ROOT_NO_UNLOADED_TRANSMITTER.md
already excludes this whole actual local pattern at every radius,
with arbitrary forces at its other endpoint H. The following direct
join records how the present negative-bridge theorem also closes its
critical equality geometry.

The purely geometric double-leaf root theorem in
TRIANGLE_THREE_BRIDGES_DOUBLE_LEAF_ROOT_EXCLUSION.md, Section 1,
places O in int(V) for d<1, and the whole closed D_epsilon in
int(V) for d>1. The distinct original U contains O when d<=1,
or meets D_epsilon when d>1. Thus every noncritical radius gives
physical overlap.

At d=1, V cannot contain O openly for the same reason. Its exact
double-leaf alternatives consequently give

    V=[0,1]u+[0,1]v,
    L=S(u),       M=S(v).

V is truly unloaded, with its full three positive forces. The
two genuine leaf forces are positive multiples of u,v, so its
unchanged parent normal points strictly into their negative
quadrant. The actual V--U application is its unique origin
vertex O. Hence O belongs to closed U.

Let e be the actual normal from U to V. U's other actual contact
is at -w e, where w is its original normal width in {1,sqrt(2)}.
The sharp contained-neighbor support bound at that other contact
gives w<=d=1. Thus w=1 and the actual original H--U data are

    n_HU=e,       P_HU=-e,       rho=-1<0,
    O belongs to closed U.                            (1)

All private block bodies retain exactly their block degrees, and
H--U is the only external block edge. Apply
FOUR_BODY_BLOCK_NEGATIVE_BRIDGE_WITH_FULL_ROOT_LOAD_EXCLUSION.md
to (1). It excludes the full four-body block with H's possible
original circle force retained. In particular the critical fact
that H may itself be a physical radial S square is included;
it is not silently declared clear.

## 4. The first fork with one direct leaf and one short arm

This is exactly the unchanged original graph and all-radius domain
of FOUR_BODY_BLOCK_DIRECT_LEAF_AND_SHORT_ARM_FORK_CLOSED.md.
Its true U3 contains O; the true short arm forces S/side and d>=1;
the high-radius side/vertex cover makes U origin-interior, and the
critical full U3 equation gives a strict positive parent support.
The resulting actual negative H--U bridge is excluded by the same
full-root-load theorem. Every D/S type for the other direct leaf,
block root orbit, actual mean and physical mask is covered there.

The three rows of Section 1 are exhaustive and each is now excluded.
The original ninth physical unit is retained in every dependency.
No multiple-outside-tree forest or entire C1.4.b4 coarse-cell claim
is made. No numerical search, post-extraction normal choice, Lean
compilation or CI is used.
