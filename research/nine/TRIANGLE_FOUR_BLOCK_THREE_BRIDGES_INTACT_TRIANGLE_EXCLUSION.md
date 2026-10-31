# A triangle and a four-body block with three bridges cannot have an intact triangle

Date: October 27, 2026.

**Status: accepted complete hand theorem after full root and separate
independent source/scope review in
REVIEW_TRIANGLE_FOUR_BLOCK_THREE_BRIDGES_INTACT_ROOT_2026_10_27.md and
REVIEW_TRIANGLE_FOUR_BLOCK_THREE_BRIDGES_INTACT_LEAF_PAIR_2026_10_27.md.**
Their source pins precede this acceptance-only header update.
This source closes the entire
intact-triangle attachment family of C2.34.b3. It does not yet close
that whole coarse cell and changes no shared ledger or original ID.

Keep all nine original physical unit squares, the common compatible
selected physical certificate, its minimum positive scalar support,
and the original selected radius/Phi-minimizer pose in

    79/40 <= R <= sqrt(1105)/16,
    d = sqrt(R^2-1/4)-1,
    epsilon = max(d-1,0) < 1/60.

Suppose the selected connected component has exactly two cyclic
blocks, one triangle and one four-body biconnected block, and exactly
three bridges. Its nine component bodies are the original nine
physical units; no completion body is discarded. Suppose the actual
triangle is H,U,V, with true positive degrees two at U,V.

**Theorem.** This complete original attachment family is impossible.
Both possible block-tree forms, every bridge forest and internal
connector branch, every terminal-four-block graph and load mask,
both genuine leaf types, all actual means, and all physical circle
masks and individual zero weights are included.

## 1. Uniform facts at this unchanged intact triangle

The actual triangle makes U,V loaded: an unloaded true degree-two
triangle vertex would put its touching neighbors beyond opposite
supports. The intact-petal origin theorem therefore gives

    O belongs to int H.                                    (1)

H keeps its original true degree and all forces. In particular every
other actual closed unit avoids O, and H is physically circle-clear.

The following consequences have already been proved at precisely this
arbitrary-H-degree scope.

1. Every genuine leaf root C meets the closed disk D_epsilon.
   For S this is its original inward radial-unit-segment point
   epsilon e when d>1, and O when d<=1. For D its root contains
   O openly. Hence no other root can have a D leaf, and a genuine
   leaf at C different from H requires d>1.

2. There cannot be two distinct actual units C_1,C_2, both different
   from H, meeting D_epsilon. For d>1 this is the full uniform
   theorem INTACT_PETAL_TWO_DISTINCT_NEAR_ORIGIN_UNITS_EXCLUSION.md.
   At d<=1 it follows immediately from (1), because D_epsilon={O}.
   The two units need no load, degree, leaf, force, or orientation
   premise.

3. If H itself has any genuine S or D leaf, the whole closed
   D_epsilon lies strictly in int H. These are the complete
   GLOBAL_CLOSURE_INTACT_ROOT_S_LEAF_CENTRAL_DISK_EXCLUSION.md and
   GLOBAL_CLOSURE_INTACT_ROOT_D_LEAF_CENTRAL_DISK_EXCLUSION.md.
   Consequently such a leaf excludes every other actual unit
   meeting D_epsilon. No other H force is omitted.

4. An actual root C different from H cannot have two genuine
   leaves. The force-free central-disk lemma in
   TRIANGLE_THREE_BRIDGES_DOUBLE_LEAF_ROOT_EXCLUSION.md, Section 1,
   puts O in the closed C at every radius: openly when d!=1, and
   either openly or at its actual vertex when d=1. This contradicts
   (1). The lemma is geometric and permits arbitrary other forces
   and degrees at C.

It follows in particular that the genuine leaves have at most one
root outside H, and that root supports at most one such leaf. A leaf
at H cannot coexist with any leaf at a different root.

## 2. Every bridge-only nonleaf must be a near transmitter adjacent to H

A bridge-only body means one whose every incident positive edge is
a bridge; it need not be in a tree component.

The full original articulation theorem
GLOBAL_CLOSURE_ARTICULATION_STRESS_SPLITTING.md, Sections 3--5, makes
every loaded bridge-only body a genuine radial S/D leaf. In particular
every bridge-only nonleaf T here is actually unloaded. This uses the
common minimum-support choice and/or its exact inherited small-core
split; it does not erase a load from a larger original body.

Such T differs from H, so (1) puts O outside its closed square.
Apply the complete
GLOBAL_CLOSURE_OFF_ORIGIN_BRIDGE_TRANSMITTERS.md. It gives, in the
actual radial direction e of its unique outgoing edge,

    T = [rho,rho+1] e + [b-1/2,b+1/2] Je,
    0 < rho <= d-1,       |b| <= 1/2,                    (2)
    p_in = rho e in T.

In the same common minimum-support certificate T has true positive
degree two: exactly one incoming and one outgoing original bridge.
Every incoming physical neighbor contains O closed. By (1), the
incoming neighbor can therefore only be H. Thus

    every bridge-only nonleaf T is adjacent to H,
    T meets D_epsilon, and d>1.                         (3)

There is at most one such T, by Section 1.2. No two such bodies can
be adjacent; this also follows directly from the same off-origin
transmitter theorem.

These facts retain the entire actual transverse interval in (2),
both original applications, the original side-normal transmission,
and every other body's degree and force equation. In particular an
internal route vertex is included: it is not assumed to be a pendant
vertex, and an extra branch there is ruled out by its proved true
degree two.

## 3. The exact block-tree alternatives

Two different biconnected blocks share at most one vertex. Accordingly
the triangle and four-block either share one actual articulation,
or are disjoint and joined by a unique bridge path. In the shared
case their common articulation is H: sharing U or V would contradict
its true positive degree two.

Every edge not in the two cyclic blocks is a bridge. Deleting all
cyclic edges leaves a forest. Each off-route tree attaches to exactly
one vertex of a cyclic block or of the unique connecting route;
two attachments would put one of its edges on a cycle. This includes
all possible branches on internal connector vertices.

If no bridge-only nonleaf exists, all bridges are direct leaf edges,
except that disjoint cyclic blocks also have one direct connecting
bridge. Indeed a longer route or a longer leaf path would have a
bridge-only internal nonleaf.

When a bridge-only nonleaf T exists, Section 2 gives its exact two
neighbors: H and one further actual body N. Its outgoing neighbor N
cannot be another bridge-only nonleaf. It is consequently either a
genuine leaf, or a vertex of the four-block. It cannot be a second
triangle vertex: that would put HT on a cycle inside the triangle.
No further outside fork or branch at T is possible.

There is also a uniform restriction on direct leaves at H. The
original graph minus H has at least two nonleaf branches: the intact
triangle tips form one, and the other cyclic block lies in another.
Thus H has at least two branches before any direct leaf is counted.
The accepted minimum-support articulation inequality

    number of branches + number of positive circle atoms <= 3

from GLOBAL_CLOSURE_ARTICULATION_STRESS_SPLITTING.md, Section 5,
allows at most one direct leaf at H. H's physical clearance was
already proved in Section 1; no original atom has been suppressed.

## 4. No bridge-only nonleaf: at most two bridges

Suppose first that there is no T.

If the blocks share H, all three bridges would be direct leaf edges.
If the blocks are disjoint, one bridge connects them directly and
the remaining two would be direct leaf edges.

Both forms are impossible. Section 1 allows at most one genuine
leaf root outside H and at most one leaf at that root; a leaf at H
cannot coexist with it. Section 3 allows at most one leaf at H.
Hence there is at most one genuine leaf in total.

The shared form therefore has at most one bridge and the disjoint
form at most two, contrary to the original count of three.

This excludes repeated-root and distinct-root direct-leaf assignments
together, including the exact d=1 vertex alternative of the
two-leaf lemma.

## 5. A transmitter whose outgoing neighbor is cyclic: no third bridge

Now let the unique T have its outgoing neighbor N in the four-block.
The blocks are disjoint, and H--T--N is their complete two-edge
connector. If the blocks instead shared H, this path would create
an additional cycle and HT would not be a bridge.

A third bridge would lie in a pendant tree. There is no other
bridge-only nonleaf, so it must be a genuine direct leaf edge.
Its root cannot be T, whose exact degree is already two. If its
root were H, the strict disk of Section 1.3 would contain T's
actual point p_in from (2), giving overlap. If its root were
different from H,T, that root and T would be two distinct units
meeting D_epsilon, contrary to Section 1.2.

The apparent possibility of a pendant branch on the internal
connector has thus been included and excluded at its real degree,
not silently omitted from the graph cover. No third bridge exists.

## 6. A transmitter whose outgoing neighbor is a leaf

It remains that N=L is a genuine leaf. The two bridges are exactly

    H--T--L.                                              (4)

There is no other bridge-only nonleaf. Nor can there be another
genuine leaf. A different root from H,T would be a second distinct
near unit beside T. A root at H is excluded by its strict disk.
Another leaf at T would contradict its actual degree two.

If the cyclic blocks share H, every bridge belongs to a pendant
tree, so (4) accounts for all of them. There are only two, contrary
to the assumed three.

If the cyclic blocks are disjoint, the third bridge must be their
direct connector H--K, with K an actual vertex of the four-block.
There are no further bridge attachments anywhere. The four-block
therefore has its genuine terminal form at K: each of its other
three vertices retains exactly its positive degree in that block.

Apply ORIGIN_OCCUPIED_ANY_TERMINAL_FOUR_BLOCK_EXCLUSION.md with

    E = the original H,
    terminal root = the original K.                     (5)

Equation (1) puts O in int E, and the cyclic blocks being disjoint
makes E distinct from every one of the four block bodies. The
terminal-four-block theorem permits arbitrary K degree, all its
outside forces, and any original root circle mask. Thus its direct
bridge to H is retained exactly. Its complete graph and load cover
includes every private C4 load mask, either diamond root orbit,
and the already excluded K4 alternative.

The theorem excludes (5). This removes the only graph with three
bridges surviving Sections 1--5.

## 7. Whole stated-family conclusion

The argument starts from the actual intact triangle and derives
all near-origin, clearance and transmitter premises before use.
The shared-articulation and disjoint-route forms are exhaustive,
and every possible branch on an internal route was included.
The radius endpoints, genuine S/D alternatives, repeated leaf
roots, full private four-block loads, selected normal conventions
and every application mean remain throughout.

Consequently no original C2.34.b3 component with an intact triangle
can occur in the full nine-square minimizer. This is a whole
attachment-family exclusion, not a claim that a smaller graph can
be extracted by deleting a positive leaf or a four-block force.

The no-intact-triangle C2.34.b3 attachments remain separate
obligations. No whole-cell closure, new fine ID, Lean compilation,
CI run, numerical pose certificate, remote write, or central-ledger
edit is asserted.

